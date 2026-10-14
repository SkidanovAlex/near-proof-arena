//! `NearSpecV3.Ed25519.verify` (nearcore / ed25519-dalek 2.2.0 `verify`: cofactorless,
//! non-canonical `y` accepted, `s < ℓ`, `R` compared byte for byte), the spec's operation
//! sequence: `F.sqrtRatio` via `pow`, `smul` = 256-step MSB-first double-and-add with the
//! unified `Point.add`, `encode` via `F.inv = pow (p − 2)`.  Ported from the D1 spike
//! (`examples/d1-air-spike/ed25519-cost`, "faithful" schedule: 7,265 / 7,265 nearcore vectors
//! agree) without its counters; SHA-512 from the `sha2` crate.

#![allow(clippy::needless_range_loop)]

use sha2::{Digest, Sha512};

type U256 = [u64; 4];

const P: U256 = [
    0xFFFF_FFFF_FFFF_FFED,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
    0x7FFF_FFFF_FFFF_FFFF,
];
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

const fn hex32(s: &str) -> U256 {
    let b = s.as_bytes();
    let mut out = [0u64; 4];
    let mut i = 0;
    while i < 64 {
        let c = b[i];
        let v = if c >= b'a' { c - b'a' + 10 } else { c - b'0' } as u64;
        let bit = (63 - i) * 4;
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

/// `x mod ℓ` for a 512-bit little-endian `x`.
fn mod_l_512(x: &[u8]) -> U256 {
    let mut r: U256 = ZERO;
    for i in (0..512).rev() {
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

fn reduce_once(a: U256) -> U256 {
    if ge(&a, &P) { sub_raw(&a, &P) } else { a }
}

fn mul(a: &U256, b: &U256) -> U256 {
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
    let mut o2 = out;
    if c > 0 {
        o2 = add_raw(&out, &[38, 0, 0, 0]).0;
    }
    reduce_once(reduce_once(o2))
}

fn add(a: &U256, b: &U256) -> U256 {
    reduce_once(add_raw(a, b).0)
}

fn sub(a: &U256, b: &U256) -> U256 {
    if ge(a, b) {
        sub_raw(a, b)
    } else {
        add_raw(&sub_raw(&P, b), a).0
    }
}

fn neg(a: &U256) -> U256 {
    if *a == ZERO { ZERO } else { sub_raw(&P, a) }
}

fn pow(b: &U256, e: &U256) -> U256 {
    let mut r = ONE;
    for i in (0..256).rev() {
        r = mul(&r, &r);
        if bit(e, i) {
            r = mul(&r, b);
        }
    }
    r
}

#[derive(Clone, Copy)]
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

/// Spec `Point.add` (add-2008-hwcd-3).
fn padd(p: &Pt, q: &Pt) -> Pt {
    let two_d = mul(&[2, 0, 0, 0], &D);
    let a = mul(&sub(&p.y, &p.x), &sub(&q.y, &q.x));
    let b = mul(&add(&p.y, &p.x), &add(&q.y, &q.x));
    let c = mul(&mul(&p.t, &two_d), &q.t);
    let dd = mul(&mul(&p.z, &[2, 0, 0, 0]), &q.z);
    let e = sub(&b, &a);
    let f = sub(&dd, &c);
    let g = add(&dd, &c);
    let h = add(&b, &a);
    Pt {
        x: mul(&e, &f),
        y: mul(&g, &h),
        z: mul(&f, &g),
        t: mul(&e, &h),
    }
}

fn smul(n: &U256, p: &Pt) -> Pt {
    let mut q = IDENT;
    for i in (0..256).rev() {
        q = padd(&q, &q);
        if bit(n, i) {
            q = padd(&q, p);
        }
    }
    q
}

fn sqrt_ratio(u: &U256, v: &U256) -> Option<U256> {
    let v2 = mul(v, v);
    let v3 = mul(&v2, v);
    let v6 = mul(&v3, &v3);
    let v7 = mul(&v6, v);
    let uv3 = mul(u, &v3);
    let uv7 = mul(u, &v7);
    let mut e = sub_raw(&P, &[5, 0, 0, 0]);
    e = [
        (e[0] >> 3) | (e[1] << 61),
        (e[1] >> 3) | (e[2] << 61),
        (e[2] >> 3) | (e[3] << 61),
        e[3] >> 3,
    ];
    let r = mul(&uv3, &pow(&uv7, &e));
    let check = mul(v, &mul(&r, &r));
    let root = if check == *u {
        r
    } else if check == neg(u) {
        mul(&r, &SQRT_M1)
    } else {
        return None;
    };
    Some(if root[0] & 1 == 1 { neg(&root) } else { root })
}

fn decode(b: &[u8; 32]) -> Option<Pt> {
    let n = from_le_bytes(b);
    let sign = bit(&n, 255);
    let mut y = n;
    y[3] &= 0x7FFF_FFFF_FFFF_FFFF;
    let y = reduce_once(y);
    let yy = mul(&y, &y);
    let u = sub(&yy, &ONE);
    let v = add(&mul(&yy, &D), &ONE);
    let x0 = sqrt_ratio(&u, &v)?;
    let x = if sign { neg(&x0) } else { x0 };
    Some(Pt {
        x,
        y,
        z: ONE,
        t: mul(&x, &y),
    })
}

fn encode(p: &Pt) -> [u8; 32] {
    let zi = pow(&p.z, &sub_raw(&P, &[2, 0, 0, 0]));
    let x = mul(&p.x, &zi);
    let y = mul(&p.y, &zi);
    let mut out = to_le_bytes(&y);
    out[31] |= ((x[0] & 1) as u8) << 7;
    out
}

/// `Ed25519.verify pk sig msg`.
pub fn verify(pk: &[u8], sig: &[u8], msg: &[u8]) -> bool {
    if pk.len() != 32 || sig.len() != 64 {
        return false;
    }
    let pkb: [u8; 32] = pk.try_into().unwrap();
    let Some(a) = decode(&pkb) else {
        return false;
    };
    let s = from_le_bytes(&sig[32..64]);
    if ge(&s, &L) {
        return false;
    }
    let mut h = Sha512::new();
    h.update(&sig[..32]);
    h.update(pk);
    h.update(msg);
    let k = mod_l_512(&h.finalize());
    let b = Pt {
        x: BX,
        y: BY,
        z: ONE,
        t: mul(&BX, &BY),
    };
    let sb = smul(&s, &b);
    let na = Pt {
        x: neg(&a.x),
        y: a.y,
        z: a.z,
        t: neg(&a.t),
    };
    let ka = smul(&k, &na);
    encode(&padd(&sb, &ka)) == sig[..32]
}
