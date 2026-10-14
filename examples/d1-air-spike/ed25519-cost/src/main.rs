//! D1-AIR design spike (docs/zk-formal/V3-D1-DESIGN.md §4.3, §5.3): what an in-AIR Ed25519
//! verification with nearcore's semantics (ed25519-dalek 2.2.0 `verify`, cofactorless,
//! non-canonical `y` accepted, `R` compared byte-for-byte; spec/near-chunk-validation-d1.md §2,
//! `NearSpecV3.Ed25519.verify`) costs, measured by running two schedules on every vector of
//! `oracle/fixtures/v3/ed25519/*.jsonl` and comparing with nearcore's own verdict
//! (`verify_raw`, recorded by `near-arena-oracle-v3-d1 ed25519-judge`):
//!
//! * **faithful** — exactly the Lean spec's operation sequence (`F.sqrtRatio` via `pow`,
//!   `smul` = 256-step MSB-first double-and-add with the unified `Point.add`, `encode` via
//!   `F.inv = pow (p−2)`). An AIR that replays this sequence is equal to the spec value step by
//!   step: no group-law, primality or Euler-criterion theorem is needed.
//! * **optimized** — hinted square root / non-square witness, fixed-base comb for `[s]B`,
//!   4-bit window for `[k](−A)`, dedicated doubling, hinted inverse. Cheaper, but proving it
//!   equal to the spec needs the group law (associativity), unique square roots and Fermat
//!   (primality of `p`) in Lean without Mathlib.
//!
//! Every field multiplication of the first `--gadget N` vectors (default 200) is also run
//! through the 32 × 8-bit limb gadget (product convolution, `2^256 ≡ 38` fold, signed carry
//! chain), checking the gadget identity in BabyBear and over ℤ and the result against the
//! reference; random inputs with every limb at its maximum (`2^9 − 1`, one lazy addition of
//! headroom) give the worst-case coefficient and carry magnitudes.
//!
//! No dependencies: own 256/512-bit arithmetic and SHA-512 (checked on `sha512.jsonl`).

// Limb arithmetic indexes several arrays in lock-step; `to_cached` mirrors dalek naming.
#![allow(clippy::needless_range_loop, clippy::wrong_self_convention)]

use std::fs;
use std::path::Path;
use std::time::Instant;

// ---------------------------------------------------------------- 256-bit integers

type U256 = [u64; 4];

const P: U256 = [
    0xFFFF_FFFF_FFFF_FFED,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
    0x7FFF_FFFF_FFFF_FFFF,
];
/// ℓ = 2^252 + 27742317777372353535851937790883648493
const L: U256 = [
    0x5812_631A_5CF5_D3ED,
    0x14DE_F9DE_A2F7_9CD6,
    0,
    0x1000_0000_0000_0000,
];
const D: U256 = hex32("52036cee2b6ffe738cc740797779e89800700a4d4141d8ab75eb4dca135978a3");
const SQRT_M1: U256 = hex32("2b8324804fc1df0b2b4d00993dfbd7a72f431806ad2fe478c4ee1b274a0ea0b0");
const BX: U256 = hex32("216936d3cd6e53fec0a4e231fdd6dc5c692cc7609525a7b2c9562d608f25d51a");
const BY: U256 = hex32("6666666666666666666666666666666666666666666666666666666666666658");
const ZERO: U256 = [0; 4];
const ONE: U256 = [1, 0, 0, 0];

/// Big-endian hex (64 digits) to little-endian limbs, at compile time.
const fn hex32(s: &str) -> U256 {
    let b = s.as_bytes();
    let mut out = [0u64; 4];
    let mut i = 0;
    while i < 64 {
        let c = b[i];
        let v = if c >= b'a' { c - b'a' + 10 } else { c - b'0' } as u64;
        let bit = (63 - i) * 4; // nibble position from the least significant end
        out[bit / 64] |= v << (bit % 64);
        i += 1;
    }
    out
}

fn ge(a: &U256, b: &U256) -> bool {
    for i in (0..4).rev() {
        if a[i] != b[i] {
            return a[i] > b[i];
        }
    }
    true
}

fn sub_raw(a: &U256, b: &U256) -> U256 {
    let mut r = [0u64; 4];
    let mut borrow = 0u64;
    for i in 0..4 {
        let (x, b1) = a[i].overflowing_sub(b[i]);
        let (y, b2) = x.overflowing_sub(borrow);
        r[i] = y;
        borrow = (b1 || b2) as u64;
    }
    r
}

fn add_raw(a: &U256, b: &U256) -> (U256, u64) {
    let mut r = [0u64; 4];
    let mut carry = 0u64;
    for i in 0..4 {
        let s = a[i] as u128 + b[i] as u128 + carry as u128;
        r[i] = s as u64;
        carry = (s >> 64) as u64;
    }
    (r, carry)
}

fn bit(a: &U256, i: usize) -> bool {
    (a[i / 64] >> (i % 64)) & 1 == 1
}

fn from_le_bytes(b: &[u8]) -> U256 {
    let mut r = [0u64; 4];
    for (i, x) in b.iter().enumerate().take(32) {
        r[i / 8] |= (*x as u64) << (8 * (i % 8));
    }
    r
}

fn to_le_bytes(a: &U256) -> [u8; 32] {
    let mut r = [0u8; 32];
    for (i, x) in r.iter_mut().enumerate() {
        *x = (a[i / 8] >> (8 * (i % 8))) as u8;
    }
    r
}

/// `x mod ℓ` for a 512-bit little-endian `x` (bitwise long division).
fn mod_l_512(x: &[u8; 64]) -> U256 {
    let mut r: U256 = ZERO;
    for i in (0..512).rev() {
        // r = 2r + bit; r < ℓ < 2^253 so 2r + 1 < 2^254 fits
        let top = r[3] >> 63;
        debug_assert_eq!(top, 0);
        r = [
            (r[0] << 1) | ((x[i / 8] >> (i % 8)) & 1) as u64,
            (r[1] << 1) | (r[0] >> 63),
            (r[2] << 1) | (r[1] >> 63),
            (r[3] << 1) | (r[2] >> 63),
        ];
        if ge(&r, &L) {
            r = sub_raw(&r, &L);
        }
    }
    r
}

// ---------------------------------------------------------------- operation counters

#[derive(Default, Clone, Copy, Debug)]
struct Ops {
    mul: u64,  // variable × variable (incl. squarings): one degree-2 gadget each
    cmul: u64, // variable × constant: linear, carries only
    lin: u64,  // additions, subtractions, negations
    cmp: u64,  // canonicality / range comparisons on 32-byte values
    point_add: u64,
    point_dbl: u64,
    sha512_blocks: u64,
}

impl std::ops::AddAssign for Ops {
    fn add_assign(&mut self, o: Ops) {
        self.mul += o.mul;
        self.cmul += o.cmul;
        self.lin += o.lin;
        self.cmp += o.cmp;
        self.point_add += o.point_add;
        self.point_dbl += o.point_dbl;
        self.sha512_blocks += o.sha512_blocks;
    }
}

// ---------------------------------------------------------------- 𝔽_p reference arithmetic

struct Fp<'a> {
    ops: &'a mut Ops,
    gadget: Option<&'a mut GadgetStats>,
}

fn reduce_once(a: U256) -> U256 {
    if ge(&a, &P) {
        sub_raw(&a, &P)
    } else {
        a
    }
}

fn mul_ref(a: &U256, b: &U256) -> U256 {
    let mut prod = [0u128; 8];
    for i in 0..4 {
        let mut carry = 0u128;
        for j in 0..4 {
            let t = prod[i + j] + (a[i] as u128) * (b[j] as u128) + carry;
            prod[i + j] = t & 0xFFFF_FFFF_FFFF_FFFF;
            carry = t >> 64;
        }
        prod[i + 4] += carry;
    }
    // fold 2^256 ≡ 38
    let mut r = [0u128; 5];
    let mut carry = 0u128;
    for i in 0..4 {
        let t = prod[i] + 38 * prod[i + 4] + carry;
        r[i] = t & 0xFFFF_FFFF_FFFF_FFFF;
        carry = t >> 64;
    }
    r[4] = carry;
    let mut out = [0u64; 4];
    let mut c = 38 * r[4];
    for i in 0..4 {
        let t = r[i] + c;
        out[i] = t as u64;
        c = t >> 64;
    }
    // c ≤ 1: one more fold
    let mut o2 = out;
    if c > 0 {
        let (s, c2) = add_raw(&out, &[38, 0, 0, 0]);
        debug_assert_eq!(c2, 0);
        o2 = s;
    }
    reduce_once(reduce_once(o2))
}

impl Fp<'_> {
    fn add(&mut self, a: &U256, b: &U256) -> U256 {
        self.ops.lin += 1;
        let (s, c) = add_raw(a, b);
        debug_assert_eq!(c, 0);
        reduce_once(s)
    }
    fn sub(&mut self, a: &U256, b: &U256) -> U256 {
        self.ops.lin += 1;
        if ge(a, b) {
            sub_raw(a, b)
        } else {
            add_raw(&sub_raw(&P, b), a).0
        }
    }
    fn neg(&mut self, a: &U256) -> U256 {
        self.ops.lin += 1;
        if *a == ZERO {
            ZERO
        } else {
            sub_raw(&P, a)
        }
    }
    fn mul(&mut self, a: &U256, b: &U256) -> U256 {
        self.ops.mul += 1;
        let r = mul_ref(a, b);
        if let Some(g) = self.gadget.as_deref_mut() {
            g.check(a, b, &r);
        }
        r
    }
    fn cmul(&mut self, a: &U256, k: &U256) -> U256 {
        self.ops.cmul += 1;
        mul_ref(a, k)
    }
    /// Spec `F.pow` (`powAux 256`): MSB-first square-and-multiply over all 256 bits of `e`.
    fn pow(&mut self, b: &U256, e: &U256) -> U256 {
        let mut r = ONE;
        for i in (0..256).rev() {
            r = self.mul(&r, &r);
            if bit(e, i) {
                r = self.mul(&r, b);
            }
        }
        r
    }
}

// ---------------------------------------------------------------- the limb gadget

const BB: i64 = 2_013_265_921; // BabyBear

#[derive(Default)]
struct GadgetStats {
    checked: u64,
    max_t: i64,
    max_c: i64,
}

fn limbs(a: &U256) -> [i64; 32] {
    let b = to_le_bytes(a);
    let mut r = [0i64; 32];
    for i in 0..32 {
        r[i] = b[i] as i64;
    }
    r
}

/// `r ≡ a·b (mod p)` as 32 limbs `< 2^8` with signed carries `c`:
/// `t_k + c_{k−1} = r_k + 2^8·c_k` (k ≥ 1), `t_0 + 38·c_31 = r_0 + 2^8·c_0`, where
/// `t_k = Σ_{i+j=k} a_i b_j + 38·Σ_{i+j=k+32} a_i b_j`. Returns (r, c, max |t|).
fn gadget_mul(a: &[i64; 32], b: &[i64; 32]) -> ([i64; 32], [i64; 32], i64) {
    let mut t = [0i64; 32];
    for i in 0..32 {
        for j in 0..32 {
            let k = i + j;
            if k < 32 {
                t[k] += a[i] * b[j];
            } else {
                t[k - 32] += 38 * a[i] * b[j];
            }
        }
    }
    let max_t = t.iter().map(|x| x.abs()).max().unwrap();
    let mut r = [0i64; 32];
    let mut c = [0i64; 32];
    let mut top = 0i64;
    for _pass in 0..8 {
        let mut carry = 38 * top;
        for k in 0..32 {
            let v = t[k] + carry;
            r[k] = v.rem_euclid(256);
            c[k] = (v - r[k]) / 256;
            carry = c[k];
        }
        if c[31] == top {
            break;
        }
        top = c[31];
    }
    (r, c, max_t)
}

impl GadgetStats {
    fn check(&mut self, a: &U256, b: &U256, expect: &U256) {
        let (al, bl) = (limbs(a), limbs(b));
        self.check_limbs(&al, &bl, Some(expect));
    }

    fn check_limbs(&mut self, al: &[i64; 32], bl: &[i64; 32], expect: Option<&U256>) {
        let (r, c, max_t) = gadget_mul(al, bl);
        // recompute t and verify every equation over ℤ and in BabyBear
        let mut t = [0i64; 32];
        for i in 0..32 {
            for j in 0..32 {
                let k = i + j;
                if k < 32 {
                    t[k] += al[i] * bl[j];
                } else {
                    t[k - 32] += 38 * al[i] * bl[j];
                }
            }
        }
        for k in 0..32 {
            let cin = if k == 0 { 38 * c[31] } else { c[k - 1] };
            let lhs = t[k] + cin;
            let rhs = r[k] + 256 * c[k];
            assert_eq!(lhs, rhs, "gadget equation {k} over Z");
            assert_eq!(
                lhs.rem_euclid(BB),
                rhs.rem_euclid(BB),
                "gadget equation {k} in BabyBear"
            );
            assert!(
                lhs.abs() < BB / 2 && rhs.abs() < BB / 2,
                "no wrap in BabyBear"
            );
            assert!((0..256).contains(&r[k]));
        }
        self.max_t = self.max_t.max(max_t);
        self.max_c = self.max_c.max(c.iter().map(|x| x.abs()).max().unwrap());
        self.checked += 1;
        if let Some(e) = expect {
            let mut rb = [0u8; 32];
            for k in 0..32 {
                rb[k] = r[k] as u8;
            }
            let rv = reduce_once(reduce_once(from_le_bytes(&rb)));
            assert_eq!(&rv, e, "gadget result ≢ a·b mod p");
        }
    }
}

// ---------------------------------------------------------------- SHA-512

const K512: [u64; 80] = [
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

fn sha512(msg: &[u8], blocks: &mut u64) -> [u8; 64] {
    let mut h: [u64; 8] = [
        0x6a09e667f3bcc908,
        0xbb67ae8584caa73b,
        0x3c6ef372fe94f82b,
        0xa54ff53a5f1d36f1,
        0x510e527fade682d1,
        0x9b05688c2b3e6c1f,
        0x1f83d9abfb41bd6b,
        0x5be0cd19137e2179,
    ];
    let mut m = msg.to_vec();
    m.push(0x80);
    while m.len() % 128 != 112 {
        m.push(0);
    }
    m.extend_from_slice(&0u64.to_be_bytes());
    m.extend_from_slice(&((msg.len() as u64) * 8).to_be_bytes());
    for chunk in m.chunks(128) {
        *blocks += 1;
        let mut w = [0u64; 80];
        for i in 0..16 {
            w[i] = u64::from_be_bytes(chunk[8 * i..8 * i + 8].try_into().unwrap());
        }
        for i in 16..80 {
            let s0 = w[i - 15].rotate_right(1) ^ w[i - 15].rotate_right(8) ^ (w[i - 15] >> 7);
            let s1 = w[i - 2].rotate_right(19) ^ w[i - 2].rotate_right(61) ^ (w[i - 2] >> 6);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let mut v = h;
        for i in 0..80 {
            let s1 = v[4].rotate_right(14) ^ v[4].rotate_right(18) ^ v[4].rotate_right(41);
            let ch = (v[4] & v[5]) ^ (!v[4] & v[6]);
            let t1 = v[7]
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K512[i])
                .wrapping_add(w[i]);
            let s0 = v[0].rotate_right(28) ^ v[0].rotate_right(34) ^ v[0].rotate_right(39);
            let maj = (v[0] & v[1]) ^ (v[0] & v[2]) ^ (v[1] & v[2]);
            let t2 = s0.wrapping_add(maj);
            v = [
                t1.wrapping_add(t2),
                v[0],
                v[1],
                v[2],
                v[3].wrapping_add(t1),
                v[4],
                v[5],
                v[6],
            ];
        }
        for i in 0..8 {
            h[i] = h[i].wrapping_add(v[i]);
        }
    }
    let mut out = [0u8; 64];
    for i in 0..8 {
        out[8 * i..8 * i + 8].copy_from_slice(&h[i].to_be_bytes());
    }
    out
}

// ---------------------------------------------------------------- points

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Pt {
    x: U256,
    y: U256,
    z: U256,
    t: U256,
}

const IDENT: Pt = Pt {
    x: ZERO,
    y: ONE,
    z: ONE,
    t: ZERO,
};

impl Fp<'_> {
    /// Spec `Point.add` (add-2008-hwcd-3, complete for a = −1), operation for operation.
    fn padd_spec(&mut self, p: &Pt, q: &Pt) -> Pt {
        self.ops.point_add += 1;
        let two: U256 = [2, 0, 0, 0];
        let a = {
            let l = self.sub(&p.y, &p.x);
            let r = self.sub(&q.y, &q.x);
            self.mul(&l, &r)
        };
        let b = {
            let l = self.add(&p.y, &p.x);
            let r = self.add(&q.y, &q.x);
            self.mul(&l, &r)
        };
        let two_d = mul_ref(&two, &D); // constant (`F.mul 2 d`, folded)
        let c = {
            let l = self.cmul(&p.t, &two_d);
            self.mul(&l, &q.t)
        };
        let dd = {
            let l = self.cmul(&p.z, &two); // ×2: linear
            self.mul(&l, &q.z)
        };
        let e = self.sub(&b, &a);
        let f = self.sub(&dd, &c);
        let g = self.add(&dd, &c);
        let h = self.add(&b, &a);
        Pt {
            x: self.mul(&e, &f),
            y: self.mul(&g, &h),
            z: self.mul(&f, &g),
            t: self.mul(&e, &h),
        }
    }

    fn pneg(&mut self, p: &Pt) -> Pt {
        Pt {
            x: self.neg(&p.x),
            y: p.y,
            z: p.z,
            t: self.neg(&p.t),
        }
    }

    /// Spec `smul` = `smulAux 256`: MSB-first double-and-add over all 256 bits.
    fn smul_spec(&mut self, n: &U256, p: &Pt) -> Pt {
        let mut q = IDENT;
        for i in (0..256).rev() {
            q = self.padd_spec(&q, &q);
            if bit(n, i) {
                q = self.padd_spec(&q, p);
            }
        }
        q
    }

    /// Spec `F.sqrtRatio`.
    fn sqrt_ratio_spec(&mut self, u: &U256, v: &U256) -> Option<U256> {
        let v2 = self.mul(v, v);
        let v3 = self.mul(&v2, v);
        let v6 = self.mul(&v3, &v3);
        let v7 = self.mul(&v6, v);
        let uv3 = self.mul(u, &v3);
        let uv7 = self.mul(u, &v7);
        // (p − 5)/8
        let mut e = sub_raw(&P, &[5, 0, 0, 0]);
        e = [
            (e[0] >> 3) | (e[1] << 61),
            (e[1] >> 3) | (e[2] << 61),
            (e[2] >> 3) | (e[3] << 61),
            e[3] >> 3,
        ];
        let pw = self.pow(&uv7, &e);
        let r = self.mul(&uv3, &pw);
        let rr = self.mul(&r, &r);
        let check = self.mul(v, &rr);
        let nu = self.neg(u);
        let root = if check == *u {
            r
        } else if check == nu {
            self.cmul(&r, &SQRT_M1)
        } else {
            return None;
        };
        self.ops.cmp += 1; // isNeg / abs on the canonical value
        Some(if root[0] & 1 == 1 {
            self.neg(&root)
        } else {
            root
        })
    }

    /// Spec `decode` (dalek `decompress`).
    fn decode_spec(&mut self, b: &[u8; 32]) -> Option<Pt> {
        let n = from_le_bytes(b);
        let sign = bit(&n, 255);
        let mut y = n;
        y[3] &= 0x7FFF_FFFF_FFFF_FFFF;
        self.ops.cmp += 1; // y mod p (non-canonical y accepted)
        let y = reduce_once(y);
        let yy = self.mul(&y, &y);
        let u = self.sub(&yy, &ONE);
        let dyy = self.cmul(&yy, &D);
        let v = self.add(&dyy, &ONE);
        let x0 = self.sqrt_ratio_spec(&u, &v)?;
        let x = if sign { self.neg(&x0) } else { x0 };
        let t = self.mul(&x, &y);
        Some(Pt { x, y, z: ONE, t })
    }

    fn encode_spec(&mut self, p: &Pt) -> [u8; 32] {
        let pm2 = sub_raw(&P, &[2, 0, 0, 0]);
        let zi = self.pow(&p.z, &pm2);
        let x = self.mul(&p.x, &zi);
        let y = self.mul(&p.y, &zi);
        self.ops.cmp += 2;
        let mut out = to_le_bytes(&y);
        out[31] |= ((x[0] & 1) as u8) << 7;
        out
    }
}

fn verify_spec(pk: &[u8], sig: &[u8], msg: &[u8], f: &mut Fp) -> bool {
    if pk.len() != 32 || sig.len() != 64 {
        return false;
    }
    let pkb: [u8; 32] = pk.try_into().unwrap();
    let Some(a) = f.decode_spec(&pkb) else {
        return false;
    };
    let s = from_le_bytes(&sig[32..64]);
    f.ops.cmp += 1; // s < ℓ (`Scalar::from_canonical_bytes`)
    if ge(&s, &L) {
        return false;
    }
    let mut hin = sig[..32].to_vec();
    hin.extend_from_slice(pk);
    hin.extend_from_slice(msg);
    let h = sha512(&hin, &mut f.ops.sha512_blocks);
    let k = mod_l_512(&h);
    let b = Pt {
        x: BX,
        y: BY,
        z: ONE,
        t: mul_ref(&BX, &BY),
    };
    let sb = f.smul_spec(&s, &b);
    let na = f.pneg(&a);
    let ka = f.smul_spec(&k, &na);
    let r = f.padd_spec(&sb, &ka);
    f.encode_spec(&r) == sig[..32]
}

// ---------------------------------------------------------------- optimized schedule

/// Affine-Niels `(y+x, y−x, 2d·x·y)`.
#[derive(Clone, Copy)]
struct Niels {
    ypx: U256,
    ymx: U256,
    xy2d: U256,
}

/// Cached `(Y+X, Y−X, 2Z, 2d·T)`.
#[derive(Clone, Copy)]
struct Cached {
    ypx: U256,
    ymx: U256,
    z2: U256,
    t2d: U256,
}

fn two_d() -> U256 {
    mul_ref(&[2, 0, 0, 0], &D)
}

impl Fp<'_> {
    fn madd(&mut self, p: &Pt, q: &Niels) -> Pt {
        self.ops.point_add += 1;
        let a = {
            let l = self.sub(&p.y, &p.x);
            self.mul(&l, &q.ymx)
        };
        let b = {
            let l = self.add(&p.y, &p.x);
            self.mul(&l, &q.ypx)
        };
        let c = self.mul(&p.t, &q.xy2d);
        let d = self.add(&p.z, &p.z);
        let e = self.sub(&b, &a);
        let f = self.sub(&d, &c);
        let g = self.add(&d, &c);
        let h = self.add(&b, &a);
        Pt {
            x: self.mul(&e, &f),
            y: self.mul(&g, &h),
            z: self.mul(&f, &g),
            t: self.mul(&e, &h),
        }
    }

    fn cadd(&mut self, p: &Pt, q: &Cached) -> Pt {
        self.ops.point_add += 1;
        let a = {
            let l = self.sub(&p.y, &p.x);
            self.mul(&l, &q.ymx)
        };
        let b = {
            let l = self.add(&p.y, &p.x);
            self.mul(&l, &q.ypx)
        };
        let c = self.mul(&p.t, &q.t2d);
        let d = self.mul(&p.z, &q.z2);
        let e = self.sub(&b, &a);
        let f = self.sub(&d, &c);
        let g = self.add(&d, &c);
        let h = self.add(&b, &a);
        Pt {
            x: self.mul(&e, &f),
            y: self.mul(&g, &h),
            z: self.mul(&f, &g),
            t: self.mul(&e, &h),
        }
    }

    /// dbl-2008-hwcd for a = −1 (4M + 4S).
    fn pdbl(&mut self, p: &Pt) -> Pt {
        self.ops.point_dbl += 1;
        let a = self.mul(&p.x, &p.x);
        let b = self.mul(&p.y, &p.y);
        let zz = self.mul(&p.z, &p.z);
        let c = self.add(&zz, &zz);
        let d = self.neg(&a);
        let xy = self.add(&p.x, &p.y);
        let xy2 = self.mul(&xy, &xy);
        let e0 = self.sub(&xy2, &a);
        let e = self.sub(&e0, &b);
        let g = self.add(&d, &b);
        let f = self.sub(&g, &c);
        let h = self.sub(&d, &b);
        Pt {
            x: self.mul(&e, &f),
            y: self.mul(&g, &h),
            z: self.mul(&f, &g),
            t: self.mul(&e, &h),
        }
    }

    fn to_cached(&mut self, p: &Pt) -> Cached {
        Cached {
            ypx: self.add(&p.y, &p.x),
            ymx: self.sub(&p.y, &p.x),
            z2: self.add(&p.z, &p.z),
            t2d: self.cmul(&p.t, &two_d()),
        }
    }

    /// Decompression with a hinted root: square case `v·x0² = u` (x0 canonical, even), else a
    /// non-square witness `v·w² = √−1·u` (`u ≠ 0`). The hint is computed natively here.
    fn decode_hinted(&mut self, b: &[u8; 32]) -> Option<Pt> {
        let n = from_le_bytes(b);
        let sign = bit(&n, 255);
        let mut y = n;
        y[3] &= 0x7FFF_FFFF_FFFF_FFFF;
        self.ops.cmp += 1;
        let y = reduce_once(y);
        let yy = self.mul(&y, &y);
        let u = self.sub(&yy, &ONE);
        let dyy = self.cmul(&yy, &D);
        let v = self.add(&dyy, &ONE);
        // native hint (not counted)
        let mut scratch = Ops::default();
        let hint = Fp {
            ops: &mut scratch,
            gadget: None,
        }
        .sqrt_ratio_spec(&u, &v);
        match hint {
            Some(x0) => {
                let x2 = self.mul(&x0, &x0);
                let chk = self.mul(&v, &x2);
                assert_eq!(chk, u, "square-root hint");
                self.ops.cmp += 1; // x0 < p and parity
                let x = if sign { self.neg(&x0) } else { x0 };
                let t = self.mul(&x, &y);
                Some(Pt { x, y, z: ONE, t })
            }
            None => {
                // w = sqrt(√−1·u / v) exists when u/v is a non-square
                let iu = mul_ref(&SQRT_M1, &u);
                let w = Fp {
                    ops: &mut scratch,
                    gadget: None,
                }
                .sqrt_ratio_spec(&iu, &v)
                .expect("non-square witness");
                let w2 = self.mul(&w, &w);
                let chk = self.mul(&v, &w2);
                let iu2 = self.cmul(&u, &SQRT_M1);
                assert_eq!(chk, iu2, "non-square witness");
                None
            }
        }
    }
}

struct Tables {
    comb: Vec<[Niels; 16]>, // comb[i][j] = j·16^i·B
}

fn build_tables() -> Tables {
    let mut ops = Ops::default();
    let mut f = Fp {
        ops: &mut ops,
        gadget: None,
    };
    let b = Pt {
        x: BX,
        y: BY,
        z: ONE,
        t: mul_ref(&BX, &BY),
    };
    let mut base = b;
    let mut comb = Vec::new();
    for _i in 0..64 {
        let mut row = [Niels {
            ypx: ONE,
            ymx: ONE,
            xy2d: ZERO,
        }; 16];
        let mut acc = IDENT;
        for item in row.iter_mut().skip(1) {
            acc = f.padd_spec(&acc, &base);
            // affine
            let zi = f.pow(&acc.z, &sub_raw(&P, &[2, 0, 0, 0]));
            let x = mul_ref(&acc.x, &zi);
            let y = mul_ref(&acc.y, &zi);
            *item = Niels {
                ypx: reduce_once(add_raw(&y, &x).0),
                ymx: if ge(&y, &x) {
                    sub_raw(&y, &x)
                } else {
                    add_raw(&sub_raw(&P, &x), &y).0
                },
                xy2d: mul_ref(&mul_ref(&x, &y), &two_d()),
            };
        }
        comb.push(row);
        for _ in 0..4 {
            base = f.padd_spec(&base, &base);
        }
    }
    Tables { comb }
}

fn nibble(a: &U256, i: usize) -> usize {
    ((a[i / 16] >> (4 * (i % 16))) & 0xF) as usize
}

fn verify_opt(pk: &[u8], sig: &[u8], msg: &[u8], f: &mut Fp, tb: &Tables) -> bool {
    if pk.len() != 32 || sig.len() != 64 {
        return false;
    }
    let pkb: [u8; 32] = pk.try_into().unwrap();
    let Some(a) = f.decode_hinted(&pkb) else {
        return false;
    };
    let s = from_le_bytes(&sig[32..64]);
    f.ops.cmp += 1;
    if ge(&s, &L) {
        return false;
    }
    let mut hin = sig[..32].to_vec();
    hin.extend_from_slice(pk);
    hin.extend_from_slice(msg);
    let h = sha512(&hin, &mut f.ops.sha512_blocks);
    let k = mod_l_512(&h);
    // [s]B: fixed-base comb, 64 mixed additions
    let mut sb = IDENT;
    for i in 0..64 {
        sb = f.madd(&sb, &tb.comb[i][nibble(&s, i)]);
    }
    // [k](−A): 4-bit fixed window
    let na = f.pneg(&a);
    let mut pts = [IDENT; 16];
    pts[1] = na;
    pts[2] = f.pdbl(&na);
    let c1 = f.to_cached(&na);
    for j in 3..16 {
        pts[j] = f.cadd(&pts[j - 1], &c1);
    }
    let mut cached = [Cached {
        ypx: ONE,
        ymx: ONE,
        z2: [2, 0, 0, 0],
        t2d: ZERO,
    }; 16];
    for j in 1..16 {
        cached[j] = f.to_cached(&pts[j]);
    }
    let mut acc = pts[nibble(&k, 63)];
    for i in (0..63).rev() {
        for _ in 0..4 {
            acc = f.pdbl(&acc);
        }
        acc = f.cadd(&acc, &cached[nibble(&k, i)]);
    }
    let cs = f.to_cached(&sb);
    let r = f.cadd(&acc, &cs);
    // hinted inverse: Z·zi = 1
    let zi = Fp {
        ops: &mut Ops::default(),
        gadget: None,
    }
    .pow(&r.z, &sub_raw(&P, &[2, 0, 0, 0]));
    let one = f.mul(&r.z, &zi);
    assert_eq!(one, ONE);
    let x = f.mul(&r.x, &zi);
    let y = f.mul(&r.y, &zi);
    f.ops.cmp += 2;
    let mut out = to_le_bytes(&y);
    out[31] |= ((x[0] & 1) as u8) << 7;
    out == sig[..32]
}

// ---------------------------------------------------------------- vectors

fn field<'a>(line: &'a str, key: &str) -> Option<&'a str> {
    let pat = format!("\"{key}\": ");
    let i = line.find(&pat)? + pat.len();
    let rest = &line[i..];
    if let Some(r) = rest.strip_prefix('"') {
        let j = r.find('"')?;
        Some(&r[..j])
    } else {
        let j = rest.find([',', '}']).unwrap_or(rest.len());
        Some(rest[..j].trim())
    }
}

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
        .collect()
}

#[derive(Default)]
struct Agg {
    n: u64,
    sum: Ops,
    max_mul: u64,
    max_total: u64,
    agree: u64,
    disagree: u64,
    accepted: u64,
}

fn total(o: &Ops) -> u64 {
    o.mul + o.cmul
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let dir = args
        .get(1)
        .cloned()
        .unwrap_or_else(|| "oracle/fixtures/v3/ed25519".into());
    let gadget_n: u64 = args
        .iter()
        .position(|a| a == "--gadget")
        .and_then(|i| args.get(i + 1))
        .map(|s| s.parse().unwrap())
        .unwrap_or(200);

    // constants
    {
        let mut ops = Ops::default();
        let mut f = Fp {
            ops: &mut ops,
            gadget: None,
        };
        let m1 = f.neg(&ONE);
        assert_eq!(mul_ref(&SQRT_M1, &SQRT_M1), m1, "sqrt(-1)^2 = -1");
        let n121666 = f.neg(&[121666, 0, 0, 0]);
        assert_eq!(
            mul_ref(&D, &n121666),
            [121665, 0, 0, 0],
            "d = -121665/121666"
        );
        let (xx, yy) = (mul_ref(&BX, &BX), mul_ref(&BY, &BY));
        let lhs = f.sub(&yy, &xx);
        let rhs = f.add(&ONE, &mul_ref(&D, &mul_ref(&xx, &yy)));
        assert_eq!(lhs, rhs, "B on the curve");
    }

    // SHA-512 vectors
    let mut sha_ok = 0;
    if let Ok(text) = fs::read_to_string(Path::new(&dir).join("sha512.jsonl")) {
        for line in text.lines() {
            let msg = unhex(field(line, "msg").unwrap());
            let want = unhex(field(line, "sha512").unwrap());
            let mut nb = 0;
            assert_eq!(
                sha512(&msg, &mut nb).to_vec(),
                want,
                "{}",
                field(line, "id").unwrap()
            );
            sha_ok += 1;
        }
    }

    let tables = build_tables();
    let mut spec = Agg::default();
    let mut opt = Agg::default();
    let mut gstats = GadgetStats::default();
    let mut t_spec = 0f64;
    let mut t_opt = 0f64;
    let mut files: Vec<_> = fs::read_dir(&dir)
        .expect("vector dir")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "jsonl") && !p.ends_with("sha512.jsonl"))
        .collect();
    files.sort();
    let mut idx = 0u64;
    for path in &files {
        let text = fs::read_to_string(path).unwrap();
        for line in text.lines() {
            let pk = unhex(field(line, "pk").unwrap());
            let sig = unhex(field(line, "sig").unwrap());
            let msg = unhex(field(line, "msg").unwrap());
            let want = field(line, "verify_raw").unwrap() == "true";
            for (which, agg, tsum) in [(0, &mut spec, &mut t_spec), (1, &mut opt, &mut t_opt)] {
                let mut ops = Ops::default();
                let use_gadget = which == 0 && idx < gadget_n;
                let t0 = Instant::now();
                let got = {
                    let mut f = Fp {
                        ops: &mut ops,
                        gadget: if use_gadget { Some(&mut gstats) } else { None },
                    };
                    if which == 0 {
                        verify_spec(&pk, &sig, &msg, &mut f)
                    } else {
                        verify_opt(&pk, &sig, &msg, &mut f, &tables)
                    }
                };
                if !use_gadget {
                    *tsum += t0.elapsed().as_secs_f64();
                }
                agg.n += 1;
                if got == want {
                    agg.agree += 1;
                } else {
                    agg.disagree += 1;
                    eprintln!(
                        "DISAGREE ({}) {}",
                        ["spec", "opt"][which],
                        field(line, "id").unwrap()
                    );
                }
                if got {
                    agg.accepted += 1;
                }
                // count only full verifications (decoding succeeded, s < ℓ) for the maxima
                agg.max_mul = agg.max_mul.max(ops.mul);
                agg.max_total = agg.max_total.max(total(&ops));
                agg.sum += ops;
            }
            idx += 1;
        }
    }

    // worst-case gadget bounds: every limb at the lazy-addition maximum 2^9 − 1, and random
    let mut wstats = GadgetStats::default();
    let maxl = [511i64; 32];
    wstats.check_limbs(&maxl, &maxl, None);
    let mut seed = 0x9E37_79B9_7F4A_7C15u64;
    for _ in 0..100_000 {
        let mut a = [0i64; 32];
        let mut b = [0i64; 32];
        for i in 0..32 {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            a[i] = (seed % 512) as i64;
            b[i] = ((seed >> 20) % 512) as i64;
        }
        wstats.check_limbs(&a, &b, None);
    }

    let mean = |a: &Agg, f: fn(&Ops) -> u64| f(&a.sum) as f64 / a.n as f64;
    println!("{{");
    println!("  \"vectors\": {},", spec.n);
    println!("  \"sha512_vectors_ok\": {sha_ok},");
    for (name, a, t) in [("faithful_spec", &spec, t_spec), ("optimized", &opt, t_opt)] {
        println!("  \"{name}\": {{");
        println!(
            "    \"agree_with_nearcore\": {}, \"disagree\": {}, \"accepted\": {},",
            a.agree, a.disagree, a.accepted
        );
        println!(
            "    \"mean_mul\": {:.1}, \"max_mul\": {},",
            mean(a, |o| o.mul),
            a.max_mul
        );
        println!(
            "    \"mean_cmul\": {:.1}, \"mean_lin\": {:.1}, \"mean_cmp\": {:.1},",
            mean(a, |o| o.cmul),
            mean(a, |o| o.lin),
            mean(a, |o| o.cmp)
        );
        println!("    \"mean_point_add\": {:.1}, \"mean_point_dbl\": {:.1}, \"mean_sha512_blocks\": {:.2},", mean(a, |o| o.point_add), mean(a, |o| o.point_dbl), mean(a, |o| o.sha512_blocks));
        println!("    \"max_mul_plus_cmul\": {},", a.max_total);
        println!(
            "    \"reference_rust_us_per_verify\": {:.1}",
            1e6 * t / a.n as f64
        );
        println!("  }},");
    }
    println!("  \"gadget\": {{ \"products_checked_on_vectors\": {}, \"max_t_vectors\": {}, \"max_carry_vectors\": {},", gstats.checked, gstats.max_t, gstats.max_c);
    println!("    \"random_max_limb_products\": {}, \"max_t_worst\": {}, \"max_t_worst_log2\": {:.2}, \"max_carry_worst\": {}, \"max_carry_worst_log2\": {:.2}, \"babybear_half\": {} }}",
        wstats.checked, wstats.max_t, (wstats.max_t as f64).log2(), wstats.max_c, (wstats.max_c as f64).log2(), BB / 2);
    println!("}}");
    if spec.disagree + opt.disagree > 0 {
        std::process::exit(1);
    }
}
