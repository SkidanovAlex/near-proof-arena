//! Narrow SHA-512 compression AIR (FIPS 180-4 §6.4.2); SHA-384 is the same
//! compression with the SHA-384 IV and a 48-byte truncation, both chosen by the
//! consumer of the interface bus.
//!
//! Layout: one segment of `ROWS` = 44 rows per compression, two rounds per row.
//! Words are carried as bits (needed by Σ/σ/Ch/Maj); 64-bit additions use
//! three limbs (22/21/21 bits) with carries range-checked by lookup.  History
//! further than one row back moves over a permutation bus keyed by the global
//! row counter, so no column holds a duplicated word.  Layout, alternatives
//! and measurements: research/near-compression/results/pq384-sha-air/README.md.
// Column-range loops read clearer than iterator chains here.
#![allow(clippy::needless_range_loop)]
use openvm_stark_backend::{PartitionedBaseAir, interaction::InteractionBuilder};
use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, BaseAirWithPublicValues};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;

pub const ROWS: usize = 44;
pub const PAD_R: u32 = 44;
pub const LIMB_OFF: [usize; 4] = [0, 22, 43, 64];

// Main AIR columns.
pub const A0: usize = 0;
pub const A1: usize = 64;
pub const E0: usize = 128;
pub const E1: usize = 192;
pub const W0: usize = 256;
pub const W1: usize = 320;
pub const NBITS: usize = 384;
pub const SLOTS: [usize; 4] = [A0, A1, E0, E1];
/// Unnormalised partial sums for slot 0 of the next row (a, e).
pub const SA: usize = 384;
pub const SE: usize = 387;
/// Packed copy of the previous row's slot-1 words (a, e).
pub const DA: usize = 390;
pub const DE: usize = 393;
/// Carries: slot-1 a/e, slot-0 a/e, schedule words 0/1.
pub const C1A: usize = 396;
pub const C1E: usize = 399;
pub const C0A: usize = 402;
pub const C0E: usize = 405;
pub const CW0: usize = 408;
pub const CW1: usize = 411;
pub const NCARRY: usize = 18;
/// Received schedule terms: V0/V1 (W[t-16] + σ0(W[t-15])), W[t-7] for slots 0/1.
pub const RV0: usize = 414;
pub const RV1: usize = 417;
pub const R7A: usize = 420;
pub const R7B: usize = 423;
/// Round constants (limbs) for slots 0/1, from the control table.
pub const K0: usize = 426;
pub const K1: usize = 429;
pub const R: usize = 432;
pub const G: usize = 433;
pub const F_IV: usize = 434;
pub const F_ROUND: usize = 435;
pub const F_SCHED: usize = 436;
pub const F_OUT: usize = 437;
pub const F_FIN: usize = 438;
pub const F_S01: usize = 439;
pub const F_S2: usize = 440;
pub const F_S3: usize = 441;
pub const WIDTH: usize = 442;
// OUT rows reuse: received IV words at RV0+3q, received final words at SA+3q,
// feed-forward carries at C1A+3q.
pub const OUT_IV: usize = RV0;
pub const OUT_FIN: usize = SA;
pub const OUT_C: usize = C1A;

pub const BUS_CTL: u16 = 0;
pub const BUS_RNG: u16 = 1;
pub const BUS_LB: u16 = 2;
pub const BUS_IF: u16 = 3;
/// Range table [0, 64) bounds every carry.
pub const RANGE: usize = 64;
pub const CTL_FIELDS: usize = 15;

pub const K: [u64; 80] = [
    0x428a2f98d728ae22,
    0x7137449123ef65cd,
    0xb5c0fbcfec4d3b2f,
    0xe9b5dba58189dbbc,
    0x3956c25bf348b538,
    0x59f111f1b605d019,
    0x923f82a4af194f9b,
    0xab1c5ed5da6d8118,
    0xd807aa98a3030242,
    0x12835b0145706fbe,
    0x243185be4ee4b28c,
    0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f,
    0x80deb1fe3b1696b1,
    0x9bdc06a725c71235,
    0xc19bf174cf692694,
    0xe49b69c19ef14ad2,
    0xefbe4786384f25e3,
    0x0fc19dc68b8cd5b5,
    0x240ca1cc77ac9c65,
    0x2de92c6f592b0275,
    0x4a7484aa6ea6e483,
    0x5cb0a9dcbd41fbd4,
    0x76f988da831153b5,
    0x983e5152ee66dfab,
    0xa831c66d2db43210,
    0xb00327c898fb213f,
    0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2,
    0xd5a79147930aa725,
    0x06ca6351e003826f,
    0x142929670a0e6e70,
    0x27b70a8546d22ffc,
    0x2e1b21385c26c926,
    0x4d2c6dfc5ac42aed,
    0x53380d139d95b3df,
    0x650a73548baf63de,
    0x766a0abb3c77b2a8,
    0x81c2c92e47edaee6,
    0x92722c851482353b,
    0xa2bfe8a14cf10364,
    0xa81a664bbc423001,
    0xc24b8b70d0f89791,
    0xc76c51a30654be30,
    0xd192e819d6ef5218,
    0xd69906245565a910,
    0xf40e35855771202a,
    0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8,
    0x1e376c085141ab53,
    0x2748774cdf8eeb99,
    0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63,
    0x4ed8aa4ae3418acb,
    0x5b9cca4f7763e373,
    0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc,
    0x78a5636f43172f60,
    0x84c87814a1f0ab72,
    0x8cc702081a6439ec,
    0x90befffa23631e28,
    0xa4506cebde82bde9,
    0xbef9a3f7b2c67915,
    0xc67178f2e372532b,
    0xca273eceea26619c,
    0xd186b8c721c0c207,
    0xeada7dd6cde0eb1e,
    0xf57d4f7fee6ed178,
    0x06f067aa72176fba,
    0x0a637dc5a2c898a6,
    0x113f9804bef90dae,
    0x1b710b35131c471b,
    0x28db77f523047d84,
    0x32caab7b40c72493,
    0x3c9ebe0a15c9bebc,
    0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6,
    0x597f299cfc657e2a,
    0x5fcb6fab3ad6faec,
    0x6c44198c4a475817,
];

pub fn limbs3(x: u64) -> [u64; 3] {
    std::array::from_fn(|i| (x >> LIMB_OFF[i]) & ((1u64 << (LIMB_OFF[i + 1] - LIMB_OFF[i])) - 1))
}

/// Control-table entry for table index i in [0, 64): (r, flags..., K0 limbs, K1 limbs).
/// Indices >= 44 all describe the padding row (r = 44, every flag 0).
pub fn ctl_entry(i: usize) -> [u64; CTL_FIELDS] {
    let mut e = [0u64; CTL_FIELDS];
    if i >= ROWS {
        e[0] = PAD_R as u64;
        return e;
    }
    let f = |lo: usize, hi: usize| (lo..=hi).contains(&i) as u64;
    e[0] = i as u64;
    e[1] = f(0, 1); // f_iv
    e[2] = f(2, 41); // f_round
    e[3] = f(10, 41); // f_sched
    e[4] = f(42, 43); // f_out
    e[5] = f(40, 41); // f_fin: rows whose words feed the feed-forward
    e[6] = f(2, 33); // f_s01: senders of V0/V1 (received 8 rows later)
    e[7] = f(6, 37); // f_s2: senders of W[t-7] for slot 0 (4 rows later)
    e[8] = f(7, 38); // f_s3: senders of W[t-7] for slot 1 (3 rows later)
    if e[2] == 1 {
        e[9..12].copy_from_slice(&limbs3(K[2 * i - 4]));
        e[12..15].copy_from_slice(&limbs3(K[2 * i - 3]));
    }
    e
}

fn xor2<E: PrimeCharacteristicRing + Clone>(x: &E, y: &E) -> E {
    x.clone() + y.clone() - (x.clone() * y.clone()).double()
}
fn xor3<E: PrimeCharacteristicRing + Clone>(x: &E, y: &E, z: &E) -> E {
    let xy = x.clone() * y.clone();
    x.clone() + y.clone() + z.clone()
        - (xy.clone() + x.clone() * z.clone() + y.clone() * z.clone()).double()
        + (xy * z.clone()) * E::from_u32(4)
}
/// Bitwise rotate-xor family: bit i = x[i+r1] ^ x[i+r2] ^ (x[i+r3] or shr bit).
fn rx<E: PrimeCharacteristicRing + Clone>(
    x: &[E],
    r1: usize,
    r2: usize,
    r3: usize,
    shr: bool,
) -> Vec<E> {
    (0..64)
        .map(|i| {
            let a = &x[(i + r1) % 64];
            let b = &x[(i + r2) % 64];
            if shr {
                if i + r3 < 64 {
                    xor3(a, b, &x[i + r3])
                } else {
                    xor2(a, b)
                }
            } else {
                xor3(a, b, &x[(i + r3) % 64])
            }
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
pub fn ch<E: PrimeCharacteristicRing + Clone>(e: &[E], f: &[E], g: &[E]) -> Vec<E> {
    (0..64)
        .map(|i| g[i].clone() + e[i].clone() * (f[i].clone() - g[i].clone()))
        .collect()
}
pub fn maj<E: PrimeCharacteristicRing + Clone>(a: &[E], b: &[E], c: &[E]) -> Vec<E> {
    (0..64)
        .map(|i| {
            let ab = a[i].clone() * b[i].clone();
            ab.clone() + a[i].clone() * c[i].clone() + b[i].clone() * c[i].clone()
                - (ab * c[i].clone()).double()
        })
        .collect()
}
pub fn pack3<E: PrimeCharacteristicRing + Clone>(bits: &[E]) -> [E; 3] {
    std::array::from_fn(|l| {
        (LIMB_OFF[l]..LIMB_OFF[l + 1]).fold(E::ZERO, |acc, b| {
            acc + bits[b].clone() * E::from_u64(1u64 << (b - LIMB_OFF[l]))
        })
    })
}
pub fn pack16<E: PrimeCharacteristicRing + Clone>(bits: &[E]) -> [E; 4] {
    std::array::from_fn(|l| {
        (0..16).fold(E::ZERO, |acc, b| {
            acc + bits[16 * l + b].clone() * E::from_u32(1 << b)
        })
    })
}
fn add3<E: PrimeCharacteristicRing + Clone>(x: &[E; 3], y: &[E; 3]) -> [E; 3] {
    std::array::from_fn(|i| x[i].clone() + y[i].clone())
}
fn cols3<E: Clone>(row: &[E], c: usize) -> [E; 3] {
    std::array::from_fn(|i| row[c + i].clone())
}

/// Limb-wise addition constraint: out + 2^{s_i} c_i - c_{i-1} == rhs_i (times gate).
fn add_constraint<AB: AirBuilder>(
    b: &mut AB,
    gate: &AB::Expr,
    out: &[AB::Expr; 3],
    carry: &[AB::Expr; 3],
    rhs: &[AB::Expr; 3],
) {
    for i in 0..3 {
        let w = LIMB_OFF[i + 1] - LIMB_OFF[i];
        let mut lhs = out[i].clone() + carry[i].clone() * AB::Expr::from_u64(1u64 << w);
        if i > 0 {
            lhs -= carry[i - 1].clone();
        }
        b.assert_zero(gate.clone() * (lhs - rhs[i].clone()));
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Sha512Air;
impl<F> BaseAir<F> for Sha512Air {
    fn width(&self) -> usize {
        WIDTH
    }
}
impl<F> PartitionedBaseAir<F> for Sha512Air {}
impl<F> BaseAirWithPublicValues<F> for Sha512Air {}

impl<AB: AirBuilderWithPublicValues + InteractionBuilder> Air<AB> for Sha512Air {
    fn eval(&self, b: &mut AB) {
        let main = b.main();
        let l: Vec<AB::Expr> = main
            .row_slice(0)
            .unwrap()
            .iter()
            .map(|&v| v.into())
            .collect();
        let n: Vec<AB::Expr> = main
            .row_slice(1)
            .unwrap()
            .iter()
            .map(|&v| v.into())
            .collect();
        let one = AB::Expr::ONE;
        let c = |v: u64| AB::Expr::from_u64(v);
        let f_pad = |x: &[AB::Expr]| {
            AB::Expr::ONE - x[F_IV].clone() - x[F_ROUND].clone() - x[F_OUT].clone()
        };
        let s = |x: &[AB::Expr], base: usize| x[base..base + 64].to_vec();

        // Bits, and zero cells wherever a column has no role, so that every cell
        // of an accepted trace is determined by (input state, block).
        for col in 0..NBITS {
            b.assert_bool(l[col].clone());
        }
        let not_round = one.clone() - l[F_ROUND].clone();
        for col in W0..NBITS {
            b.assert_zero(not_round.clone() * l[col].clone());
        }
        let pad = f_pad(&l);
        for col in 0..W0 {
            b.assert_zero(pad.clone() * l[col].clone());
        }
        let no_rc = one.clone() - l[F_ROUND].clone() - l[F_OUT].clone();
        for col in C1A..CW0 {
            b.assert_zero(no_rc.clone() * l[col].clone());
        }
        for col in CW0..RV0 {
            b.assert_zero((one.clone() - l[F_SCHED].clone()) * l[col].clone());
        }
        let no_recv = one.clone() - l[F_SCHED].clone() - l[F_OUT].clone();
        for col in RV0..K0 {
            b.assert_zero(no_recv.clone() * l[col].clone());
        }

        // Row sequencing: segments 0..43 back to back, then padding (r = 44) to the end.
        b.when_first_row().assert_zero(l[R].clone());
        b.when_first_row().assert_zero(l[G].clone());
        b.when_last_row()
            .assert_zero((l[R].clone() - c(43)) * (one.clone() - f_pad(&l)));
        {
            let mut t = b.when_transition();
            t.assert_zero(n[G].clone() - l[G].clone() - one.clone());
            t.assert_zero(
                (n[R].clone() - l[R].clone() - one.clone())
                    * (one.clone() - f_pad(&n))
                    * n[R].clone(),
            );
            t.assert_zero(f_pad(&n) * (one.clone() - f_pad(&l)) * (l[R].clone() - c(43)));
            t.assert_zero((one.clone() - n[R].clone()) * n[F_IV].clone() * (l[R].clone() - c(43)));
            t.assert_zero(f_pad(&l) * (one.clone() - f_pad(&n)));
        }

        let (a0l, a1l, e0l, e1l, w0l, w1l) = (
            s(&l, A0),
            s(&l, A1),
            s(&l, E0),
            s(&l, E1),
            s(&l, W0),
            s(&l, W1),
        );
        let (a0n, a1n, e0n, e1n, w0n, w1n) = (
            s(&n, A0),
            s(&n, A1),
            s(&n, E0),
            s(&n, E1),
            s(&n, W0),
            s(&n, W1),
        );

        // S (next row) = partial sums for slot 0 of the row after next, from (local, next);
        // D (next row) = packed slot-1 words of local.  Cyclic, disabled on OUT rows.
        let keep = one.clone() - n[F_OUT].clone();
        {
            let sig1 = pack3(&big_sigma1(&e1n));
            let chv = pack3(&ch(&e1n, &e0n, &e1l));
            let sig0 = pack3(&big_sigma0(&a1n));
            let mj = pack3(&maj(&a1n, &a0n, &a1l));
            let h = pack3(&e0l);
            let d = pack3(&a0l);
            for i in 0..3 {
                let t1 = h[i].clone() + sig1[i].clone() + chv[i].clone();
                b.assert_zero(
                    keep.clone()
                        * (n[SA + i].clone() - (t1.clone() + sig0[i].clone() + mj[i].clone())),
                );
                b.assert_zero(keep.clone() * (n[SE + i].clone() - (t1 + d[i].clone())));
            }
            let pa = pack3(&a1l);
            let pe = pack3(&e1l);
            for i in 0..3 {
                b.assert_zero(keep.clone() * (n[DA + i].clone() - pa[i].clone()));
                b.assert_zero(keep.clone() * (n[DE + i].clone() - pe[i].clone()));
            }
        }

        // Round, slot 1 of next row: j-1 = next slot 0, j-2/j-3 = local slots 1/0, j-4 from D(local).
        let g_round = n[F_ROUND].clone();
        {
            let sig1 = pack3(&big_sigma1(&e0n));
            let chv = pack3(&ch(&e0n, &e1l, &e0l));
            let sig0 = pack3(&big_sigma0(&a0n));
            let mj = pack3(&maj(&a0n, &a1l, &a0l));
            let w = pack3(&w1n);
            let t1: [AB::Expr; 3] = std::array::from_fn(|i| {
                l[DE + i].clone()
                    + sig1[i].clone()
                    + chv[i].clone()
                    + n[K1 + i].clone()
                    + w[i].clone()
            });
            let ra: [AB::Expr; 3] =
                std::array::from_fn(|i| t1[i].clone() + sig0[i].clone() + mj[i].clone());
            let re: [AB::Expr; 3] = std::array::from_fn(|i| t1[i].clone() + l[DA + i].clone());
            add_constraint(b, &g_round, &pack3(&a1n), &cols3(&n, C1A), &ra);
            add_constraint(b, &g_round, &pack3(&e1n), &cols3(&n, C1E), &re);
        }
        // Round, slot 0 of next row: partial sum S(local) + W + K.
        {
            let w = pack3(&w0n);
            let ra: [AB::Expr; 3] =
                std::array::from_fn(|i| l[SA + i].clone() + w[i].clone() + n[K0 + i].clone());
            let re: [AB::Expr; 3] =
                std::array::from_fn(|i| l[SE + i].clone() + w[i].clone() + n[K0 + i].clone());
            add_constraint(b, &g_round, &pack3(&a0n), &cols3(&n, C0A), &ra);
            add_constraint(b, &g_round, &pack3(&e0n), &cols3(&n, C0E), &re);
        }
        // Message schedule for the next row's W slots: σ1(W[t-2]) (local) + W[t-7] + V (received).
        {
            let g_sched = n[F_SCHED].clone();
            for (wl, wn, cw, r7, rv) in [(&w0l, &w0n, CW0, R7A, RV0), (&w1l, &w1n, CW1, R7B, RV1)] {
                let s1 = pack3(&small_sigma1(wl));
                let rhs: [AB::Expr; 3] =
                    std::array::from_fn(|i| s1[i].clone() + n[r7 + i].clone() + n[rv + i].clone());
                add_constraint(b, &g_sched, &pack3(wn), &cols3(&n, cw), &rhs);
            }
        }
        // Feed-forward on OUT rows: slot q = IV word q + final word q (both received).
        for (q, &base) in SLOTS.iter().enumerate() {
            let rhs = add3(&cols3(&l, OUT_IV + 3 * q), &cols3(&l, OUT_FIN + 3 * q));
            add_constraint(
                b,
                &l[F_OUT],
                &pack3(&l[base..base + 64]),
                &cols3(&l, OUT_C + 3 * q),
                &rhs,
            );
        }

        // ---- interactions ----
        let mut ctl = vec![l[R].clone()];
        ctl.extend((F_IV..=F_S3).map(|col| l[col].clone()));
        ctl.extend((K0..K0 + 6).map(|col| l[col].clone()));
        b.push_interaction(BUS_CTL, ctl, one.clone(), 1);
        for col in C1A..C1A + NCARRY {
            b.push_interaction(BUS_RNG, [l[col].clone()], one.clone(), 1);
        }
        // Interface bus: (compression id, word index 0..31, four 16-bit limbs).
        // 0..7 input state, 8..23 block, 24..31 output state.
        let cid = l[G].clone() - l[R].clone();
        let two_r = l[R].clone().double();
        for (q, &base) in SLOTS.iter().enumerate() {
            let civ = [3u64, 2, 7, 6][q];
            let cout = [59u64, 60, 55, 56][q];
            let idx = l[F_IV].clone() * (c(civ) - two_r.clone())
                + l[F_OUT].clone() * (two_r.clone() - c(cout));
            let mut msg = vec![cid.clone(), idx];
            msg.extend(pack16(&l[base..base + 64]));
            b.push_interaction(BUS_IF, msg, l[F_IV].clone() + l[F_OUT].clone(), 1);
        }
        for (k, base) in [W0, W1].into_iter().enumerate() {
            let mut msg = vec![cid.clone(), two_r.clone() + c(4 + k as u64)];
            msg.extend(pack16(&l[base..base + 64]));
            b.push_interaction(BUS_IF, msg, l[F_ROUND].clone() - l[F_SCHED].clone(), 1);
        }
        // Lookback bus (permutation), keyed by the sender's global row g.
        for (q, &base) in SLOTS.iter().enumerate() {
            let mut msg = vec![l[G].clone(), c(10 + q as u64)];
            msg.extend(pack3(&l[base..base + 64]));
            b.push_interaction(BUS_LB, msg, l[F_IV].clone() + l[F_FIN].clone(), 1);
        }
        {
            let v0 = add3(&pack3(&w0l), &pack3(&small_sigma0(&w1l)));
            let v1 = add3(&pack3(&w1l), &pack3(&small_sigma0(&w0n)));
            let mut msg = vec![l[G].clone(), c(0)];
            msg.extend(v0);
            msg.extend(v1);
            b.push_interaction(BUS_LB, msg, l[F_S01].clone(), 1);
            let mut msg = vec![l[G].clone(), c(1)];
            msg.extend(pack3(&w1l));
            b.push_interaction(BUS_LB, msg, l[F_S2].clone(), 1);
            let mut msg = vec![l[G].clone(), c(2)];
            msg.extend(pack3(&w0l));
            b.push_interaction(BUS_LB, msg, l[F_S3].clone(), 1);
        }
        {
            let neg = -l[F_SCHED].clone();
            let mut msg = vec![l[G].clone() - c(8), c(0)];
            msg.extend((RV0..RV0 + 6).map(|col| l[col].clone()));
            b.push_interaction(BUS_LB, msg, neg.clone(), 1);
            let mut msg = vec![l[G].clone() - c(4), c(1)];
            msg.extend(cols3(&l, R7A));
            b.push_interaction(BUS_LB, msg, neg.clone(), 1);
            let mut msg = vec![l[G].clone() - c(3), c(2)];
            msg.extend(cols3(&l, R7B));
            b.push_interaction(BUS_LB, msg, neg, 1);
        }
        let neg_out = -l[F_OUT].clone();
        for q in 0..4 {
            let mut msg = vec![l[G].clone() - two_r.clone() + c(43), c(10 + q as u64)];
            msg.extend(cols3(&l, OUT_IV + 3 * q));
            b.push_interaction(BUS_LB, msg, neg_out.clone(), 1);
            let mut msg = vec![l[G].clone() - two_r.clone() + c(83), c(10 + q as u64)];
            msg.extend(cols3(&l, OUT_FIN + 3 * q));
            b.push_interaction(BUS_LB, msg, neg_out.clone(), 1);
        }
    }
}

/// Fixed control + range table: 64 rows, row index i = 8*v + u with one-hot u, v
/// rotated by transition constraints, so its content is pinned without a
/// preprocessed commitment.  Columns: u[8], v[8], mult_ctl, mult_rng.
#[derive(Clone, Copy, Debug)]
pub struct TableAir;
pub const T_U: usize = 0;
pub const T_V: usize = 8;
pub const T_MC: usize = 16;
pub const T_MR: usize = 17;
pub const T_WIDTH: usize = 18;
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
        let l: Vec<AB::Expr> = main
            .row_slice(0)
            .unwrap()
            .iter()
            .map(|&v| v.into())
            .collect();
        let n: Vec<AB::Expr> = main
            .row_slice(1)
            .unwrap()
            .iter()
            .map(|&v| v.into())
            .collect();
        let one = AB::Expr::ONE;
        for k in 0..16 {
            b.assert_bool(l[k].clone());
        }
        b.assert_one((0..8).fold(AB::Expr::ZERO, |a, k| a + l[T_U + k].clone()));
        b.assert_one((0..8).fold(AB::Expr::ZERO, |a, k| a + l[T_V + k].clone()));
        b.when_first_row().assert_one(l[T_U].clone());
        b.when_first_row().assert_one(l[T_V].clone());
        {
            let mut t = b.when_transition();
            for k in 0..8 {
                t.assert_zero(n[T_U + k].clone() - l[T_U + (k + 7) % 8].clone());
                t.assert_zero(
                    n[T_V + k].clone()
                        - l[T_V + k].clone()
                        - l[T_U + 7].clone() * (l[T_V + (k + 7) % 8].clone() - l[T_V + k].clone()),
                );
            }
        }
        let _ = one;
        let field = |vals: &dyn Fn(usize) -> u64| -> AB::Expr {
            let mut acc = AB::Expr::ZERO;
            for i in 0..64 {
                let v = vals(i);
                if v != 0 {
                    acc += l[T_U + i % 8].clone() * l[T_V + i / 8].clone() * AB::Expr::from_u64(v);
                }
            }
            acc
        };
        let entries: Vec<[u64; CTL_FIELDS]> = (0..64).map(ctl_entry).collect();
        let msg: Vec<AB::Expr> = (0..CTL_FIELDS).map(|f| field(&|i| entries[i][f])).collect();
        b.push_interaction(BUS_CTL, msg, -l[T_MC].clone(), 0);
        let idx = (0..8).fold(AB::Expr::ZERO, |a, k| {
            a + l[T_U + k].clone() * AB::Expr::from_u64(k as u64)
                + l[T_V + k].clone() * AB::Expr::from_u64(8 * k as u64)
        });
        b.push_interaction(BUS_RNG, [idx], -l[T_MR].clone(), 0);
    }
}

/// Test consumer of the interface bus: one row per (compression, word).
/// Columns: cid, idx, four 16-bit limbs, multiplicity.
#[derive(Clone, Copy, Debug)]
pub struct HarnessAir;
pub const H_WIDTH: usize = 7;
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
        let l: Vec<AB::Expr> = main
            .row_slice(0)
            .unwrap()
            .iter()
            .map(|&v| v.into())
            .collect();
        b.assert_bool(l[6].clone());
        b.push_interaction(BUS_IF, l[0..6].to_vec(), -l[6].clone(), 1);
    }
}
