//! Packed-digit SHA-512 compression AIR (FIPS 180-4 §6.4.2), v2.
//!
//! SHA-384 is the same compression with the SHA-384 IV and a 48-byte truncation,
//! both chosen by the consumer of the interface bus.
//!
//! What changed against v1 (442 bit columns x 44 rows):
//! * Words are stored as `nd = ceil(64/k)` little-endian base-2^k digits (k = 1, 2, 3),
//!   not bits.  A digit is range-checked by the polynomial prod_{m<2^s}(v - m), and each
//!   bit is the degree-(2^s - 1) interpolating polynomial of its digit.  Integer values
//!   (limbs) stay linear in the digits; only Σ/σ/Ch/Maj see the bit polynomials, so the
//!   constraint degree becomes 3(2^k - 1) (21 for k = 3), with no gate on those
//!   constraints.
//! * Values that v1 stored only to use them in one constraint are gone: the constraint
//!   itself is sent over a bus as a residual.  The slot-0/1 `a` additions are looked up
//!   against the round-constant table (no K columns); the `e` additions are matched against
//!   `d` (slot 1) and `d - T2` (slot 0) sent by the row two back (no D_a, S_E columns); the
//!   schedule additions are matched against W[t-7] (no received W[t-7] columns); the
//!   feed-forward is matched against the input-state words (no received IV columns).
//!   Interactions may read the next row, so one message can carry values of two rows.
//! * Carries are range-checked by polynomial, so the [0, 64) range table and its 18
//!   lookups per row are gone.  Signed carries (e = a - T2 + d) carry an offset of 4.
//! * Carries and received values used by the constraint for row x+1 are stored on row x,
//!   so they are only ever referenced at the current row.
//!
//! Layout and measurements: research/near-compression/results/pq384-sha-air2/README.md.
#![allow(clippy::needless_range_loop)]
use openvm_stark_backend::{PartitionedBaseAir, interaction::InteractionBuilder};
use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, BaseAirWithPublicValues};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::Matrix;

pub const ROWS: usize = 43;
/// Carry columns hold c + CARRY_OFF for the signed (e) equations; every carry column is
/// range-checked to [0, CARRY_RANGE).
pub const CARRY_RANGE: u64 = 8;
pub const CARRY_OFF: i64 = 4;

pub const BUS_CTL: u16 = 0;
pub const BUS_K: u16 = 1;
pub const BUS_LB: u16 = 2;
pub const BUS_IF: u16 = 3;
pub const TAG_V: u64 = 0;
pub const TAG_W7: u64 = 1;
pub const TAG_DA: u64 = 3;
pub const TAG_ST: u64 = 10;

pub const K: [u64; 80] = [
    0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817,
];

/// Column layout for digit width k.  Word slots first, then the 44 other columns.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Layout {
    pub k: usize,
    pub nd: usize,
    /// Limb boundaries (bits); every boundary is a digit boundary.
    pub limb_off: [usize; 4],
    pub a0: usize,
    pub a1: usize,
    pub e0: usize,
    pub e1: usize,
    pub w0: usize,
    pub w1: usize,
    pub ndig: usize,
    /// Partial sum h + Σ1 + Ch + Σ0 + Maj for slot 0 of the next row, defined on every row.
    pub sa: usize,
    /// Packed copy of the previous row's E1 word (h for slot 1 of the next row).
    pub de: usize,
    /// Received V = W[t-16] + σ0(W[t-15]) for the next row's two W slots.  On row 42 they
    /// hold e_76 and e_77 for the feed-forward of row 43.
    pub v0: usize,
    pub v1: usize,
    /// Carries of the next row's additions (stored +CARRY_OFF for the e equations).
    pub c1a: usize,
    pub c1e: usize,
    pub c0a: usize,
    pub c0e: usize,
    pub cw0: usize,
    pub cw1: usize,
    pub r: usize,
    pub g: usize,
    /// Flags, in control-table order: F_IV, F_ROUND, F_SCHED, F_OUT, F_TAIL, F_S01, F_S2.
    pub flags: usize,
    pub width: usize,
}
pub const NFLAGS: usize = 7;
pub const FI_IV: usize = 0;
pub const FI_ROUND: usize = 1;
pub const FI_SCHED: usize = 2;
pub const FI_OUT: usize = 3;
pub const FI_TAIL: usize = 4;
pub const FI_S01: usize = 5;
pub const FI_S2: usize = 6;

impl Layout {
    pub fn new(k: usize) -> Self {
        assert!((1..=3).contains(&k));
        let nd = 64usize.div_ceil(k);
        let limb_off = match k {
            1 | 2 => [0, 22, 44, 64],
            _ => [0, 21, 42, 64],
        };
        let ndig = 6 * nd;
        let mut c = ndig;
        let mut take = |n: usize| {
            let v = c;
            c += n;
            v
        };
        let (sa, de, v0, v1) = (take(3), take(3), take(3), take(3));
        let (c1a, c1e, c0a, c0e, cw0, cw1) =
            (take(3), take(3), take(3), take(3), take(3), take(3));
        let (r, g, flags) = (take(1), take(1), take(NFLAGS));
        Layout {
            k,
            nd,
            limb_off,
            a0: 0,
            a1: nd,
            e0: 2 * nd,
            e1: 3 * nd,
            w0: 4 * nd,
            w1: 5 * nd,
            ndig,
            sa,
            de,
            v0,
            v1,
            c1a,
            c1e,
            c0a,
            c0e,
            cw0,
            cw1,
            r,
            g,
            flags,
            width: c,
        }
    }
    pub fn slots(&self) -> [usize; 4] {
        [self.a0, self.a1, self.e0, self.e1]
    }
    /// Number of bits in digit j.
    pub fn dsize(&self, j: usize) -> usize {
        (64 - self.k * j).min(self.k)
    }
    pub fn lw(&self, l: usize) -> usize {
        self.limb_off[l + 1] - self.limb_off[l]
    }
    /// Constraint degree of the AIR: Σ/Maj of bit polynomials, digit and carry range checks.
    pub fn degree(&self) -> usize {
        let bitdeg = (1usize << self.k) - 1;
        (3 * bitdeg).max(CARRY_RANGE as usize).max(1 << self.k)
    }
    pub fn digits(&self, x: u64) -> Vec<u64> {
        (0..self.nd)
            .map(|j| (x >> (self.k * j)) & ((1u64 << self.dsize(j)) - 1))
            .collect()
    }
    pub fn limbs(&self, x: u64) -> [u64; 3] {
        std::array::from_fn(|l| (x >> self.limb_off[l]) & ((1u64 << self.lw(l)) - 1))
    }
}

/// Control-table entry for table index i: (r, flags).  Exactly one of F_IV, F_ROUND, F_OUT
/// is set, so is_real = F_IV + F_ROUND + F_OUT is 1 on every real row; padding rows are all
/// zero and do not look up.  Indices >= ROWS repeat the last entry.
pub fn ctl_entry(i: usize) -> [u64; 1 + NFLAGS] {
    let i = i.min(ROWS - 1);
    let mut e = [0u64; 1 + NFLAGS];
    let f = |lo: usize, hi: usize| (lo..=hi).contains(&i) as u64;
    e[0] = i as u64;
    e[1 + FI_IV] = f(0, 1);
    e[1 + FI_ROUND] = f(2, 41);
    e[1 + FI_SCHED] = f(10, 41);
    e[1 + FI_OUT] = f(42, 42);
    // rows 40, 41.  Derived: F_FIN = F_TAIL (41 - r) (row 40 sends a_76, a_77, e_76, e_77
    // to row 0); F_DA = F_IV + F_ROUND - F_TAIL (rows 0..39 send d terms one row ahead).
    e[1 + FI_TAIL] = f(40, 41);
    e[1 + FI_S01] = f(2, 33); // V senders (received 7 rows later, for the row after)
    e[1 + FI_S2] = f(6, 37); // W[t-7] senders, both slots (received 3 rows later)
    e
}

/// K-table entry for index i: (i, K limbs of slot 0 and slot 1 of row i+1) if row i+1 is
/// a round row, else zeros.
pub fn k_entry(lay: &Layout, i: usize) -> [u64; 7] {
    let mut e = [0u64; 7];
    let i = i.min(ROWS - 1);
    e[0] = i as u64;
    let n = i + 1;
    if i < ROWS && (2..=41).contains(&n) {
        e[1..4].copy_from_slice(&lay.limbs(K[2 * n - 4]));
        e[4..7].copy_from_slice(&lay.limbs(K[2 * n - 3]));
    }
    e
}

// ---------- bit-level helpers over symbolic or concrete expressions ----------
//
// Bits are carried as signs σ = 1 - 2b ∈ {1, -1}: XOR is a product, and for an s-bit digit
// v every bit sign is an odd function of the centred digit u = v - (2^s - 1)/2 (complementing
// v negates u and flips every bit), so σ_t = u S_t(u^2) with deg S_t = 2^{s-1} - 1.  The
// degree of a bit is still 2^s - 1, but the expressions are much smaller.

/// Signs of Σ/σ: bit i = x[i+r1] ^ x[i+r2] ^ (x[i+r3] or the shifted-out zero).
fn rx<E: PrimeCharacteristicRing + Clone>(
    x: &[E],
    r1: usize,
    r2: usize,
    r3: usize,
    shr: bool,
) -> Vec<E> {
    (0..64)
        .map(|i| {
            let ab = x[(i + r1) % 64].clone() * x[(i + r2) % 64].clone();
            if shr && i + r3 >= 64 { ab } else { ab * x[(i + r3) % 64].clone() }
        })
        .collect()
}
pub fn big_sigma0<E: PrimeCharacteristicRing + Clone>(a: &[E]) -> Vec<E> {
    rx(a, 28, 34, 39, false)
}
pub fn big_sigma1<E: PrimeCharacteristicRing + Clone>(e: &[E]) -> Vec<E> {
    rx(e, 14, 18, 41, false)
}
pub fn small_sigma0<E: PrimeCharacteristicRing + Clone>(w: &[E]) -> Vec<E> {
    rx(w, 1, 8, 7, true)
}
pub fn small_sigma1<E: PrimeCharacteristicRing + Clone>(w: &[E]) -> Vec<E> {
    rx(w, 19, 61, 6, true)
}
/// 2 x sign of Ch(e, f, g) = (e ? f : g):  σf + σg + σe (σg - σf).
pub fn ch2<E: PrimeCharacteristicRing + Clone>(e: &[E], f: &[E], g: &[E]) -> Vec<E> {
    (0..64)
        .map(|i| f[i].clone() + g[i].clone() + e[i].clone() * (g[i].clone() - f[i].clone()))
        .collect()
}
/// 2 x sign of Maj(a, b, c):  σa + σb + σc - σa σb σc.
pub fn maj2<E: PrimeCharacteristicRing + Clone>(a: &[E], b: &[E], c: &[E]) -> Vec<E> {
    (0..64)
        .map(|i| {
            a[i].clone() + b[i].clone() + c[i].clone()
                - a[i].clone() * b[i].clone() * c[i].clone()
        })
        .collect()
}

/// Monomial coefficients of the polynomial P of degree < n with P(xs[m]) = ys[m].
pub fn interp<F: Field>(xs: &[F], ys: &[F]) -> Vec<F> {
    let n = xs.len();
    let mut out = vec![F::ZERO; n];
    for m in 0..n {
        let mut poly = vec![F::ONE];
        let mut den = F::ONE;
        for j in 0..n {
            if j == m {
                continue;
            }
            let mut next = vec![F::ZERO; poly.len() + 1];
            for (d, &c) in poly.iter().enumerate() {
                next[d + 1] += c;
                next[d] -= c * xs[j];
            }
            poly = next;
            den *= xs[m] - xs[j];
        }
        let s = ys[m] * den.inverse();
        for (d, c) in poly.into_iter().enumerate() {
            out[d] += c * s;
        }
    }
    out
}

/// For an s-bit digit (s >= 2): (centre c, [S_t coefficients in w = u^2] per bit t), with
/// σ_t(v) = (v - c) S_t((v - c)^2).
pub fn sign_coefs<F: Field>(s: usize) -> (F, Vec<Vec<F>>) {
    let half = F::from_u32(2).inverse();
    let c = F::from_u64((1u64 << s) - 1) * half;
    let top: Vec<u64> = ((1u64 << (s - 1))..(1u64 << s)).collect();
    let us: Vec<F> = top.iter().map(|&v| F::from_u64(v) - c).collect();
    let ws: Vec<F> = us.iter().map(|&u| u * u).collect();
    let per_bit = (0..s)
        .map(|t| {
            let ys: Vec<F> = top
                .iter()
                .zip(&us)
                .map(|(&v, &u)| {
                    let sg = if (v >> t) & 1 == 1 { -F::ONE } else { F::ONE };
                    sg * u.inverse()
                })
                .collect();
            interp(&ws, &ys)
        })
        .collect();
    (c, per_bit)
}

/// Builder-agnostic view of one word's digits: bit signs (degree 2^s - 1 in each digit) and
/// limbs (linear).
pub struct Word<E> {
    pub sg: Vec<E>,
    pub limbs: [E; 3],
}

pub type SignCoefs<F> = Vec<(F, Vec<Vec<F>>)>;
pub fn all_sign_coefs<F: Field>(k: usize) -> SignCoefs<F> {
    (0..=k)
        .map(|s| if s < 2 { (F::ZERO, vec![]) } else { sign_coefs::<F>(s) })
        .collect()
}

/// Bit signs and limbs of the word whose digits start at `base` in `row`.
pub fn word<F: Field, E: PrimeCharacteristicRing + Clone + From<F>>(
    lay: &Layout,
    coef: &SignCoefs<F>,
    row: &[E],
    base: usize,
) -> Word<E> {
    let mut sg = Vec::with_capacity(64);
    for j in 0..lay.nd {
        let v = row[base + j].clone();
        let s = lay.dsize(j);
        if s == 1 {
            sg.push(E::ONE - v.double());
            continue;
        }
        let (c, per_bit) = &coef[s];
        let u = v - E::from(*c);
        let w = u.clone() * u.clone();
        let mut pw = vec![E::ONE, w.clone()];
        for d in 2..per_bit[0].len() {
            let p = pw[d - 1].clone() * w.clone();
            pw.push(p);
        }
        for t in 0..s {
            let cf = &per_bit[t];
            let mut acc = E::from(cf[0]);
            for d in 1..cf.len() {
                acc += pw[d].clone() * E::from(cf[d]);
            }
            sg.push(u.clone() * acc);
        }
    }
    let limbs = limbs_of_digits(lay, &row[base..base + lay.nd]);
    Word { sg, limbs }
}

/// Linear limbs of a word from its digits.
pub fn limbs_of_digits<E: PrimeCharacteristicRing + Clone>(lay: &Layout, d: &[E]) -> [E; 3] {
    std::array::from_fn(|l| {
        let (lo, hi) = (lay.limb_off[l], lay.limb_off[l + 1]);
        let mut acc = E::ZERO;
        for j in 0..lay.nd {
            let b = lay.k * j;
            if b >= lo && b < hi {
                acc += d[j].clone() * E::from_u64(1u64 << (b - lo));
            }
        }
        acc
    })
}
/// Limbs of the word whose bit signs are `scale * raw[b]`:
/// limb = sum 2^{b-off} (1 - σ_b) / 2 = (2^w - 1)/2 - scale/2 sum 2^{b-off} raw_b.
pub fn limbs_of_signs<F: Field, E: PrimeCharacteristicRing + Clone + From<F>>(
    lay: &Layout,
    raw: &[E],
    scale: F,
) -> [E; 3] {
    let half = F::from_u32(2).inverse();
    std::array::from_fn(|l| {
        let (lo, hi) = (lay.limb_off[l], lay.limb_off[l + 1]);
        let mut acc = E::from(F::from_u64((1u64 << (hi - lo)) - 1) * half);
        for b in lo..hi {
            acc -= raw[b].clone() * E::from(F::from_u64(1u64 << (b - lo)) * half * scale);
        }
        acc
    })
}

fn add3<E: PrimeCharacteristicRing + Clone>(xs: &[&[E; 3]]) -> [E; 3] {
    std::array::from_fn(|i| xs.iter().fold(E::ZERO, |a, x| a + x[i].clone()))
}
fn cols3<E: Clone>(row: &[E], c: usize) -> [E; 3] {
    std::array::from_fn(|i| row[c + i].clone())
}
/// out_i + 2^{w_i} c_i - c_{i-1}, with carries stored with offset `off`.
fn lhs<E: PrimeCharacteristicRing + Clone>(
    lay: &Layout,
    out: &[E; 3],
    carry: &[E; 3],
    off: i64,
) -> [E; 3] {
    let o = E::from_i64(off);
    std::array::from_fn(|i| {
        let mut v = out[i].clone() + (carry[i].clone() - o.clone()) * E::from_u64(1u64 << lay.lw(i));
        if i > 0 {
            v -= carry[i - 1].clone() - o.clone();
        }
        v
    })
}
fn sub3<E: PrimeCharacteristicRing + Clone>(x: &[E; 3], y: &[E; 3]) -> [E; 3] {
    std::array::from_fn(|i| x[i].clone() - y[i].clone())
}

#[derive(Clone, Copy, Debug)]
pub struct Sha512Air {
    pub lay: Layout,
}
impl<F> BaseAir<F> for Sha512Air {
    fn width(&self) -> usize {
        self.lay.width
    }
}
impl<F> PartitionedBaseAir<F> for Sha512Air {}
impl<F> BaseAirWithPublicValues<F> for Sha512Air {}

impl<AB: AirBuilderWithPublicValues + InteractionBuilder> Air<AB> for Sha512Air {
    fn eval(&self, b: &mut AB) {
        let lay = &self.lay;
        let main = b.main();
        let l: Vec<AB::Expr> = main.row_slice(0).unwrap().iter().map(|&v| v.into()).collect();
        let n: Vec<AB::Expr> = main.row_slice(1).unwrap().iter().map(|&v| v.into()).collect();
        let one = AB::Expr::ONE;
        let c = |v: u64| AB::Expr::from_u64(v);
        let fl = |x: &[AB::Expr], i: usize| x[lay.flags + i].clone();
        let real = |x: &[AB::Expr]| fl(x, FI_IV) + fl(x, FI_ROUND) + fl(x, FI_OUT);
        let pad = |x: &[AB::Expr]| one.clone() - real(x);
        // Row 0 of a segment: holds H'2, H'3 (W slots) and its carries serve row 1's H'6, H'7.
        let row0 = |x: &[AB::Expr]| fl(x, FI_IV) * (one.clone() - x[lay.r].clone());
        let coef = all_sign_coefs::<AB::F>(lay.k);

        // ---- range checks and zero cells ----
        for j in 0..lay.ndig {
            let s = lay.dsize(j % lay.nd);
            let v = l[j].clone();
            let mut p = v.clone();
            for m in 1..(1u64 << s) {
                p *= v.clone() - c(m);
            }
            b.assert_zero(p);
        }
        for col in lay.c1a..lay.cw1 + 3 {
            let v = l[col].clone();
            let mut p = v.clone();
            for m in 1..CARRY_RANGE {
                p *= v.clone() - c(m);
            }
            b.assert_zero(p);
        }
        let padl = pad(&l);
        for col in 0..lay.w0 {
            b.assert_zero(padl.clone() * l[col].clone());
        }
        let no_w = one.clone() - fl(&l, FI_ROUND) - fl(&l, FI_IV);
        for col in lay.w0..lay.ndig {
            b.assert_zero(no_w.clone() * l[col].clone());
        }
        let no_rc = one.clone() - fl(&n, FI_ROUND) - fl(&n, FI_OUT) - row0(&l);
        for col in lay.c1a..lay.cw0 {
            b.assert_zero(no_rc.clone() * l[col].clone());
        }
        let no_sched = one.clone() - fl(&n, FI_SCHED);
        for col in lay.cw0..lay.cw1 + 3 {
            b.assert_zero(no_sched.clone() * l[col].clone());
        }
        let no_v = no_sched.clone();
        for col in lay.v0..lay.v1 + 3 {
            b.assert_zero(no_v.clone() * l[col].clone());
        }

        // Padding rows are all zero: r, g and every flag vanish where is_real = 0 (digits,
        // carries and V by the rules above; S_A and DE by their definitions).
        for col in [lay.r, lay.g].into_iter().chain(lay.flags..lay.flags + NFLAGS) {
            b.assert_zero(padl.clone() * l[col].clone());
        }

        // ---- row sequencing: segments 0..42 back to back from row 0, then zero rows ----
        let last = c(ROWS as u64 - 1);
        b.when_first_row().assert_zero(l[lay.r].clone());
        b.when_first_row().assert_zero(l[lay.g].clone());
        b.when_last_row()
            .assert_zero((l[lay.r].clone() - last.clone()) * real(&l));
        {
            let (r, g) = (lay.r, lay.g);
            let mut t = b.when_transition();
            t.assert_zero(real(&n) * (n[g].clone() - l[g].clone() - one.clone()));
            t.assert_zero(real(&n) * (n[r].clone() - l[r].clone() - one.clone()) * n[r].clone());
            t.assert_zero(pad(&n) * real(&l) * (l[r].clone() - last.clone()));
            t.assert_zero((one.clone() - n[r].clone()) * fl(&n, FI_IV) * (l[r].clone() - last));
            t.assert_zero(pad(&l) * real(&n));
        }

        // ---- words ----
        let wl = |base: usize| word::<AB::F, AB::Expr>(lay, &coef, &l, base);
        let wn = |base: usize| word::<AB::F, AB::Expr>(lay, &coef, &n, base);
        let (a0l, a1l, e0l, e1l, w0l, w1l) =
            (wl(lay.a0), wl(lay.a1), wl(lay.e0), wl(lay.e1), wl(lay.w0), wl(lay.w1));
        let (a0n, a1n, e0n, e1n, w0n, w1n) =
            (wn(lay.a0), wn(lay.a1), wn(lay.e0), wn(lay.e1), wn(lay.w0), wn(lay.w1));
        let one_f = AB::F::ONE;
        let half_f = AB::F::from_u32(2).inverse();
        let lb = |sg: &[AB::Expr]| limbs_of_signs::<AB::F, AB::Expr>(lay, sg, one_f);
        let lb2 = |sg: &[AB::Expr]| limbs_of_signs::<AB::F, AB::Expr>(lay, sg, half_f);

        // S (row n) = partial sums for slot 0 of row n+1; DE (row n) = E1 of row l.
        // Defined on every row, cyclically.  The terms that do not vanish when row n is zero
        // (h and Ch's g input) are gated by is_real(n), degree 15 < 21, so the row after the
        // last real row is all zero too.
        {
            let rn = real(&n);
            let s1 = lb(&big_sigma1(&e1n.sg));
            let chv = lb2(&ch2(&e1n.sg, &e0n.sg, &e1l.sg));
            let s0 = lb(&big_sigma0(&a1n.sg));
            let mj = lb2(&maj2(&a1n.sg, &a0n.sg, &a1l.sg));
            for i in 0..3 {
                let sa = rn.clone() * (e0l.limbs[i].clone() + chv[i].clone())
                    + s1[i].clone()
                    + s0[i].clone()
                    + mj[i].clone();
                b.assert_zero(n[lay.sa + i].clone() - sa);
                b.assert_zero(n[lay.de + i].clone() - rn.clone() * e1l.limbs[i].clone());
            }
        }
        // d - T2 for slot 0 of row n+1, sent from this window (row l) to row n.
        let d_minus_t2 = {
            let s0 = lb(&big_sigma0(&a1n.sg));
            let mj = lb2(&maj2(&a1n.sg, &a0n.sg, &a1l.sg));
            sub3(&a0l.limbs, &add3(&[&s0, &mj]))
        };

        let nround = fl(&n, FI_ROUND);
        let nsched = fl(&n, FI_SCHED);
        let nout = fl(&n, FI_OUT);
        // Round, slot 0 of row n: a = S_A + W + K (K by lookup), e = a + (d - T2) (by bus).
        let res_a0 = sub3(
            &lhs(lay, &a0n.limbs, &cols3(&l, lay.c0a), 0),
            &add3(&[&cols3(&l, lay.sa), &w0n.limbs]),
        );
        let res_e0 = sub3(&lhs(lay, &e0n.limbs, &cols3(&l, lay.c0e), CARRY_OFF), &a0n.limbs);
        // Round, slot 1 of row n: j-1 = slot 0 of n, j-2/j-3 = slots 1/0 of l, h = DE(l),
        // d = A1 two rows back (bus).  a = T1 + T2 (K by lookup), e = a - T2 + d.
        let t2 = {
            let s0 = lb(&big_sigma0(&a0n.sg));
            let mj = lb2(&maj2(&a0n.sg, &a1l.sg, &a0l.sg));
            add3(&[&s0, &mj])
        };
        let res_a1 = {
            let s1 = lb(&big_sigma1(&e0n.sg));
            let chv = lb2(&ch2(&e0n.sg, &e1l.sg, &e0l.sg));
            let rhs = add3(&[&cols3(&l, lay.de), &s1, &chv, &w1n.limbs, &t2]);
            sub3(&lhs(lay, &a1n.limbs, &cols3(&l, lay.c1a), 0), &rhs)
        };
        let res_e1 = sub3(
            &add3(&[&lhs(lay, &e1n.limbs, &cols3(&l, lay.c1e), CARRY_OFF), &t2]),
            &a1n.limbs,
        );
        // Schedule for row n's W slots: W = σ1(W[t-2]) + V + W[t-7] (W[t-7] by bus).
        let res_w0 = sub3(
            &lhs(lay, &w0n.limbs, &cols3(&l, lay.cw0), 0),
            &add3(&[&lb(&small_sigma1(&w0l.sg)), &cols3(&l, lay.v0)]),
        );
        let res_w1 = sub3(
            &lhs(lay, &w1n.limbs, &cols3(&l, lay.cw1), 0),
            &add3(&[&lb(&small_sigma1(&w1l.sg)), &cols3(&l, lay.v1)]),
        );
        // Feed-forward.  OUT row 42 (window 41, 42): slot q = slot q of row 41 + IV word of
        // row 1 (by bus).  Row 0 (window 0, 1): W0/W1 of row 0 = H2/H3 + a_77/a_76 and W0/W1
        // of row 1 = H6/H7 + e_77/e_76 (H from row 0's slots, final words by bus from row 40).
        let res_out: Vec<[AB::Expr; 3]> = {
            let fin = [&a0l.limbs, &a1l.limbs, &e0l.limbs, &e1l.limbs];
            let outs = [&a0n.limbs, &a1n.limbs, &e0n.limbs, &e1n.limbs];
            let carries = [lay.c0a, lay.c1a, lay.c0e, lay.c1e];
            (0..4)
                .map(|q| sub3(&lhs(lay, outs[q], &cols3(&l, carries[q]), 0), fin[q]))
                .collect()
        };
        // in the order row 40 sends: a_76, a_77, e_76, e_77
        let res_row0: Vec<[AB::Expr; 3]> = vec![
            sub3(&lhs(lay, &w1l.limbs, &cols3(&l, lay.c1a), 0), &a0l.limbs),
            sub3(&lhs(lay, &w0l.limbs, &cols3(&l, lay.c0a), 0), &a1l.limbs),
            sub3(&lhs(lay, &w1n.limbs, &cols3(&l, lay.c1e), 0), &e0l.limbs),
            sub3(&lhs(lay, &w0n.limbs, &cols3(&l, lay.c0e), 0), &e1l.limbs),
        ];

        // ---- interactions ----
        let mut ctl = vec![l[lay.r].clone()];
        ctl.extend((0..NFLAGS).map(|i| fl(&l, i)));
        b.push_interaction(BUS_CTL, ctl, real(&l), 1);
        let mut kmsg = vec![l[lay.r].clone()];
        kmsg.extend(res_a0.iter().cloned());
        kmsg.extend(res_a1.iter().cloned());
        b.push_interaction(BUS_K, kmsg, nround.clone(), 1);

        // Interface bus: (compression id, pair index, limbs of word 2m, limbs of word 2m+1).
        // Pairs 0..3 input state, 4..11 block, 12..15 output state.  Row 0/1 W slots carry
        // output pairs 13 (H'2, H'3) and 15 (H'6, H'7); row 42 carries pairs 12 and 14.
        let cid = l[lay.g].clone() - l[lay.r].clone();
        let idx_a = row0(&l) + fl(&l, FI_OUT) * c(12);
        let st_mult = fl(&l, FI_IV) + fl(&l, FI_OUT);
        for (idx, hi, lo) in [
            (idx_a.clone(), &a1l, &a0l),
            (idx_a.clone() + c(2), &e1l, &e0l),
        ] {
            let mut msg = vec![cid.clone(), idx];
            msg.extend(hi.limbs.iter().cloned());
            msg.extend(lo.limbs.iter().cloned());
            b.push_interaction(BUS_IF, msg, st_mult.clone(), 1);
        }
        {
            let blk = fl(&l, FI_ROUND) - fl(&l, FI_SCHED);
            let idx = blk.clone() * (l[lay.r].clone() + c(2))
                + fl(&l, FI_IV) * (c(13) + l[lay.r].clone().double());
            let mut msg = vec![cid.clone(), idx];
            msg.extend(w0l.limbs.iter().cloned());
            msg.extend(w1l.limbs.iter().cloned());
            b.push_interaction(BUS_IF, msg, blk + fl(&l, FI_IV), 1);
        }

        // Lookback bus (permutation), keyed by the sender's global row g.
        let g = l[lay.g].clone();
        let send = |b: &mut AB, key: AB::Expr, tag: u64, fields: Vec<AB::Expr>, m: AB::Expr| {
            let mut msg = vec![key, c(tag)];
            msg.extend(fields);
            b.push_interaction(BUS_LB, msg, m, 1);
        };
        let flat = |xs: &[&[AB::Expr; 3]]| -> Vec<AB::Expr> {
            xs.iter().flat_map(|x| x.iter().cloned()).collect()
        };
        // state words: row 1 (IV for row 42) and row 40 (final words for row 0)
        let f_fin = fl(&l, FI_TAIL) * (c(41) - l[lay.r].clone());
        let f_da = fl(&l, FI_IV) + fl(&l, FI_ROUND) - fl(&l, FI_TAIL);
        send(
            b,
            g.clone(),
            TAG_ST,
            flat(&[&a0l.limbs, &a1l.limbs, &e0l.limbs, &e1l.limbs]),
            fl(&l, FI_IV) * l[lay.r].clone() + f_fin,
        );
        // d for slot 1 and d - T2 for slot 0 of the row after next
        send(b, g.clone(), TAG_DA, flat(&[&a1l.limbs, &d_minus_t2]), f_da);
        {
            let v0 = add3(&[&w0l.limbs, &lb(&small_sigma0(&w1l.sg))]);
            let v1 = add3(&[&w1l.limbs, &lb(&small_sigma0(&w0n.sg))]);
            send(b, g.clone(), TAG_V, flat(&[&v0, &v1]), fl(&l, FI_S01));
        }
        // W[t-7] for slot 0 (W1 of this row) and slot 1 (W0 of the next row), 3 rows later
        send(b, g.clone(), TAG_W7, flat(&[&w1l.limbs, &w0n.limbs]), fl(&l, FI_S2));
        // receivers
        send(
            b,
            g.clone() - c(40),
            TAG_ST,
            res_out.iter().flat_map(|x| x.iter().cloned()).collect(),
            -nout.clone(),
        );
        send(
            b,
            g.clone() + c(40),
            TAG_ST,
            res_row0.iter().flat_map(|x| x.iter().cloned()).collect(),
            -row0(&l),
        );
        send(b, g.clone() - c(1), TAG_DA, flat(&[&res_e1, &res_e0]), -nround.clone());
        send(
            b,
            g.clone() - c(7),
            TAG_V,
            flat(&[&cols3(&l, lay.v0), &cols3(&l, lay.v1)]),
            -nsched.clone(),
        );
        send(b, g - c(3), TAG_W7, flat(&[&res_w0, &res_w1]), -nsched);
    }
}

/// Control + round-constant table: 64 rows, entry index i = u + 4v + 16w (mod 48) with
/// one-hot u[4], v[4], w[3] advanced by transition constraints, so its content is pinned
/// without a preprocessed commitment.  Columns: u, v, w, mult_ctl, mult_k.
#[derive(Clone, Copy, Debug)]
pub struct TableAir {
    pub lay: Layout,
}
pub const T_U: usize = 0;
pub const T_V: usize = 4;
pub const T_W: usize = 8;
pub const T_MC: usize = 11;
pub const T_MK: usize = 12;
pub const T_WIDTH: usize = 13;
pub const T_ENTRIES: usize = 48;
pub fn table_index(row: usize) -> usize {
    row % T_ENTRIES
}
impl<F> BaseAir<F> for TableAir {
    fn width(&self) -> usize {
        T_WIDTH
    }
}
impl<F> PartitionedBaseAir<F> for TableAir {}
impl<F> BaseAirWithPublicValues<F> for TableAir {}
impl<AB: AirBuilderWithPublicValues + InteractionBuilder> Air<AB> for TableAir {
    fn eval(&self, b: &mut AB) {
        let main = b.main();
        let l: Vec<AB::Expr> = main.row_slice(0).unwrap().iter().map(|&v| v.into()).collect();
        let n: Vec<AB::Expr> = main.row_slice(1).unwrap().iter().map(|&v| v.into()).collect();
        for k in 0..11 {
            b.assert_bool(l[k].clone());
        }
        let sum = |lo: usize, cnt: usize| (lo..lo + cnt).fold(AB::Expr::ZERO, |a, k| a + l[k].clone());
        b.assert_one(sum(T_U, 4));
        b.assert_one(sum(T_V, 4));
        b.assert_one(sum(T_W, 3));
        b.when_first_row().assert_one(l[T_U].clone());
        b.when_first_row().assert_one(l[T_V].clone());
        b.when_first_row().assert_one(l[T_W].clone());
        {
            let mut t = b.when_transition();
            let wrap_u = l[T_U + 3].clone();
            let wrap_uv = l[T_U + 3].clone() * l[T_V + 3].clone();
            for k in 0..4 {
                t.assert_zero(n[T_U + k].clone() - l[T_U + (k + 3) % 4].clone());
                t.assert_zero(
                    n[T_V + k].clone()
                        - l[T_V + k].clone()
                        - wrap_u.clone() * (l[T_V + (k + 3) % 4].clone() - l[T_V + k].clone()),
                );
            }
            for k in 0..3 {
                t.assert_zero(
                    n[T_W + k].clone()
                        - l[T_W + k].clone()
                        - wrap_uv.clone() * (l[T_W + (k + 2) % 3].clone() - l[T_W + k].clone()),
                );
            }
        }
        let field = |vals: &dyn Fn(usize) -> u64| -> AB::Expr {
            let mut acc = AB::Expr::ZERO;
            for i in 0..T_ENTRIES {
                let v = vals(i);
                if v != 0 {
                    acc += l[T_U + i % 4].clone()
                        * l[T_V + (i / 4) % 4].clone()
                        * l[T_W + i / 16].clone()
                        * AB::Expr::from_u64(v);
                }
            }
            acc
        };
        let ce: Vec<_> = (0..T_ENTRIES).map(ctl_entry).collect();
        let msg: Vec<AB::Expr> = (0..1 + NFLAGS).map(|f| field(&|i| ce[i][f])).collect();
        b.push_interaction(BUS_CTL, msg, -l[T_MC].clone(), 0);
        let ke: Vec<_> = (0..T_ENTRIES).map(|i| k_entry(&self.lay, i)).collect();
        let msg: Vec<AB::Expr> = (0..7).map(|f| field(&|i| ke[i][f])).collect();
        b.push_interaction(BUS_K, msg, -l[T_MK].clone(), 0);
    }
}

/// Test consumer of the interface bus: one row per (compression, word pair).
/// Columns: cid, pair index, 3 + 3 limbs, multiplicity.
#[derive(Clone, Copy, Debug)]
pub struct HarnessAir;
pub const H_WIDTH: usize = 9;
impl<F> BaseAir<F> for HarnessAir {
    fn width(&self) -> usize {
        H_WIDTH
    }
}
impl<F> PartitionedBaseAir<F> for HarnessAir {}
impl<F> BaseAirWithPublicValues<F> for HarnessAir {}
impl<AB: AirBuilderWithPublicValues + InteractionBuilder> Air<AB> for HarnessAir {
    fn eval(&self, b: &mut AB) {
        let main = b.main();
        let l: Vec<AB::Expr> = main.row_slice(0).unwrap().iter().map(|&v| v.into()).collect();
        b.assert_bool(l[8].clone());
        b.push_interaction(BUS_IF, l[0..8].to_vec(), -l[8].clone(), 1);
    }
}
