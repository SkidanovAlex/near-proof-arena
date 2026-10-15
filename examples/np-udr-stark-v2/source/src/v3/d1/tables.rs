//! Honest traces of the D1 tables of `nearAirV3D1` (lane v3-d1-tables):
//! `txV3` (25), `akmV3` (26), `kibV3` (27), `plfV3` (28), `ridV3` (29), column layouts as
//! `ZkFormal/NearV3/D1/Tables/{TxDefs,AkmDefs,RelayDefs}.lean`.  Heights are the roll-aligned
//! `padLog22 (logOf rows)`; padding rows are zero.
//!
//! The entry lists (`TxE`, `AkmE`, …) are the tables' inputs; [`super::entries`] builds them
//! from the native run, and their JSON is what the Lean dumper's differential compares.

use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use serde::{Deserialize, Serialize};

use crate::field::F;
use crate::v3::{Tab, log_of, pad_log22};

fn inv(x: i128) -> u64 {
    let p = crate::field::P as i128;
    F::from_u64(x.rem_euclid(p) as u64)
        .try_inverse()
        .unwrap_or(F::ZERO)
        .as_canonical_u32() as u64
}

fn fe(x: i128) -> u64 {
    x.rem_euclid(crate::field::P as i128) as u64
}

fn tab(rows: usize, width: usize) -> Tab {
    let log = pad_log22(log_of(rows.max(1)));
    Tab {
        log,
        width,
        cells: vec![0; width << log],
    }
}

fn set_bits(t: &mut Tab, r: usize, c0: usize, n: usize, x: u128) {
    for j in 0..n {
        t.set(r, c0 + j, ((x >> j) & 1) as u64);
    }
}

// ------------------------------------------------------------------------------- txV3

pub const TX_WIDTH: usize = 147;

/// One `txV3` op: the public fields and the memory values it reads.
#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct TxE {
    pub kind: u64,
    pub strict: u64,
    pub ok: u64,
    pub tov: u64,
    pub stage: u64,
    pub cok: u64,
    pub valid: u64,
    pub nonce: u64,
    pub bound: u128,
    pub amount: u128,
    pub vid_a: u64,
    pub tp_a: u64,
    /// account bytes `amount ‖ locked ‖ storage` read (`0` if `stage = 0`)
    pub amt: u128,
    pub lk: u128,
    pub st: u64,
    pub vid_k: u64,
    pub tp_k: u64,
    pub kn: u64,
    pub fa: u64,
}

const S_LE: [u64; 8] = [0, 0, 232, 137, 4, 35, 199, 138];

fn by(x: u128, i: usize) -> u64 {
    if i < 16 {
        ((x >> (8 * i)) & 0xff) as u64
    } else {
        0
    }
}

pub fn tx_trace(ops: &[TxE]) -> Tab {
    let mut t = tab(16 * ops.len(), TX_WIDTH);
    for (o, e) in ops.iter().enumerate() {
        let s1 = (e.stage >= 1) as u64;
        let s2 = (e.stage == 2) as u64;
        let cand = e.valid * e.cok;
        let wr = if e.kind == 1 { 1 } else { e.ok * (1 - e.tov) };
        let g_w = if e.kind == 1 { 1 } else { cand };
        let g_k = (1 - e.kind) * s1;
        let fa = if s2 == 1 { e.fa } else { 0 };
        let (amt, lk, st) = if s1 == 1 {
            (e.amt, e.lk, e.st as u128)
        } else {
            (0, 0, 0)
        };
        let kn = if s2 == 1 { e.kn as u128 } else { 0 };
        let nn = e.nonce as u128;
        // chains (lane values)
        let (mut bo_n, mut bo_b, mut co_c, mut co_t, mut cq, mut bo_q, mut bo_s) =
            (1i128, 1i128, 0i128, 0i128, 0i128, 0i128, 0i128);
        let mut z = 1u64;
        let mut msum: i128 = 0;
        let c770 = [2i128, 3];
        let rows: Vec<usize> = (0..16).map(|i| 16 * o + i).collect();
        let mut st_hist: Vec<i128> = vec![];
        let mut fin = [0i128; 7];
        for i in 0..16 {
            let r = rows[i];
            let set = |t: &mut Tab, c: usize, x: u64| t.set(r, c, x);
            set(&mut t, 0, 1);
            set(&mut t, 1, (i == 0) as u64);
            set(&mut t, 2, (i == 15) as u64);
            set(&mut t, 3, i as u64);
            set(&mut t, 4, (16 * o + i) as u64);
            set(&mut t, 5, o as u64);
            let (x_n, x_b, x_c) = (
                by(nn, i) as i128,
                by(e.bound, i) as i128,
                by(e.amount, i) as i128,
            );
            for (c, x) in [
                (6, e.kind),
                (7, e.strict),
                (8, e.ok),
                (9, e.tov),
                (10, e.stage),
                (11, e.cok),
            ] {
                set(&mut t, c, x);
            }
            set(&mut t, 12, x_n as u64);
            set(&mut t, 13, x_b as u64);
            set(&mut t, 14, x_c as u64);
            for (c, x) in [
                (15, e.valid),
                (16, s1),
                (17, s2),
                (18, cand),
                (19, wr),
                (20, fa),
            ] {
                set(&mut t, c, x);
            }
            set(&mut t, 21, if s1 == 1 { e.vid_a } else { 0 });
            set(&mut t, 22, if s2 == 1 { e.vid_k } else { 0 });
            set(&mut t, 23, if s1 == 1 { e.tp_a } else { 0 });
            set(&mut t, 24, if s2 == 1 { e.tp_k } else { 0 });
            let (a_i, l_i, s_i) = (by(amt, i) as i128, by(lk, i) as i128, by(st, i) as i128);
            let k_i = if i < 8 { by(kn, i) as i128 } else { 0 };
            set(&mut t, 25, a_i as u64);
            set(&mut t, 26, l_i as u64);
            set(&mut t, 27, s_i as u64);
            set(&mut t, 29, k_i as u64);
            // chain N
            let cin = bo_n;
            let mut d = x_n - k_i - cin;
            bo_n = (d < 0) as i128;
            d += 256 * bo_n;
            set_bits(&mut t, r, 50, 8, d as u128);
            set(&mut t, 58, bo_n as u64);
            let e_n = (d == 0) as u64;
            set(&mut t, 59, e_n);
            set(&mut t, 60, inv(d));
            z *= e_n;
            set(&mut t, 61, z);
            // chain B
            let cin = bo_b;
            let mut d = x_b - x_n - cin;
            bo_b = (d < 0) as i128;
            d += 256 * bo_b;
            set_bits(&mut t, r, 62, 8, d as u128);
            set(&mut t, 70, bo_b as u64);
            // chain C
            let cin = co_c;
            let rc = if e.kind == 0 {
                let mut d = a_i - x_c - cin;
                co_c = (d < 0) as i128;
                d += 256 * co_c;
                d
            } else {
                let s = a_i + x_c + cin;
                co_c = s / 256;
                s % 256
            };
            set_bits(&mut t, r, 71, 8, rc as u128);
            set(&mut t, 79, co_c as u64);
            set(&mut t, 28, (a_i + wr as i128 * (rc - a_i)) as u64);
            set(
                &mut t,
                30,
                (k_i + if i < 8 { wr as i128 * (x_n - k_i) } else { 0 }) as u64,
            );
            // chain T
            let s = rc + l_i + co_t;
            co_t = s / 256;
            let tt = s % 256;
            set_bits(&mut t, r, 80, 8, tt as u128);
            set(&mut t, 88, co_t as u64);
            // chain Q
            let mut conv = 0i128;
            for (j, sj) in S_LE.iter().enumerate() {
                let sv = if j == 0 {
                    s_i
                } else if i >= j {
                    st_hist[i - j]
                } else {
                    0
                };
                conv += *sj as i128 * sv;
            }
            for j in 0..7 {
                let v = if i > j { st_hist[i - 1 - j] } else { 0 };
                set(&mut t, 109 + j, v as u64);
            }
            st_hist.push(s_i);
            let s = conv + cq;
            cq = s / 256;
            let q = s % 256;
            set_bits(&mut t, r, 89, 8, q as u128);
            set_bits(&mut t, r, 97, 12, cq as u128);
            // chain D
            let mut d = tt - q - bo_q;
            bo_q = (d < 0) as i128;
            d += 256 * bo_q;
            set_bits(&mut t, r, 116, 8, d as u128);
            set(&mut t, 124, bo_q as u64);
            // chain S
            let c = if i < 2 { c770[i] } else { 0 };
            let mut d = c - s_i - bo_s;
            bo_s = (d < 0) as i128;
            d += 256 * bo_s;
            set_bits(&mut t, r, 125, 8, d as u128);
            set(&mut t, 133, bo_s as u64);
            // credit: Σ (255 − aft)
            msum += 255 - rc;
            set(&mut t, 134, fe(msum));
            set(&mut t, 135, inv(msum));
            // lanes
            set_bits(&mut t, r, 31, 4, i as u128);
            set(&mut t, 35, (i == 1) as u64);
            if i == 0 && s1 == 1 {
                set_bits(&mut t, r, 36, 14, (o as u64 - e.tp_a) as u128);
            }
            if i == 1 && s2 == 1 {
                set_bits(&mut t, r, 36, 14, (o as u64 - e.tp_k) as u128);
            }
            // gates
            set(&mut t, 142, g_w);
            set(&mut t, 143, g_k);
            set(&mut t, 144, s2 * (i < 8) as u64);
            set(&mut t, 145, (i == 0) as u64 * g_w);
            set(&mut t, 146, (i == 0) as u64 * g_k);
            if i == 15 {
                fin = [bo_n, bo_b, co_c, co_t, bo_q, bo_s, z as i128];
            }
        }
        // verdict on the last lane
        let r = rows[15];
        let [bo_n, bo_b, co_c, co_t, bo_q, bo_s, z] = fin.map(|x| x as u64);
        let h_n = (1 - bo_n) * (1 - e.strict + e.strict * z);
        let h_s = (1 - co_t) * (1 - bo_q * bo_s);
        let h1 = s2 * fa;
        let h2 = h1 * h_n;
        let h3 = h2 * (1 - bo_b) * (1 - co_c);
        let ok_c = h3 * h_s;
        for (c, x) in [
            (136, h_n),
            (137, h_s),
            (138, h1),
            (139, h2),
            (140, h3),
            (141, ok_c),
        ] {
            t.set(r, c, x);
        }
    }
    t
}

/// The verdict `txV3` recomputes for a debit op (for the native cross-check).
pub fn tx_verdict(e: &TxE) -> bool {
    if e.kind != 0 || e.stage != 2 || e.fa != 1 {
        return false;
    }
    let n = e.nonce as u128;
    let kn = e.kn as u128;
    let nonce_ok = n > kn && (e.strict == 0 || n == kn + 1) && n < e.bound;
    if e.amt < e.amount {
        return false;
    }
    let new = e.amt - e.amount;
    let Some(tot) = new.checked_add(e.lk) else {
        return false;
    };
    let q = 10_000_000_000_000_000_000u128 * e.st as u128;
    nonce_ok && (tot >= q || e.st <= 770)
}

// ------------------------------------------------------------------------------ akmV3

pub const AKM_WIDTH: usize = 70;

/// One access-key value record read by a transaction.
#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct AkmE {
    pub vid: u64,
    pub bytes: Vec<u8>,
    pub tlast: u64,
    /// final nonce bytes (8)
    pub post: Vec<u8>,
    #[serde(rename = "U")]
    pub u: u64,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum St {
    N,
    T,
    G,
    O,
    A,
    L,
    S,
    C,
}

fn st_col(s: St) -> usize {
    13 + s as usize
}

fn st_len(s: St) -> usize {
    match s {
        St::N => 8,
        St::T | St::O => 1,
        St::G => 18,
        St::A => 16,
        St::L | St::C => 4,
        St::S => 0,
    }
}

/// The `akmV3` rows of one value (`None` if it does not decode).
fn akm_rows(e: &AkmE) -> Option<Vec<[u64; AKM_WIDTH]>> {
    let bs = &e.bytes;
    let tag = *bs.get(8)? as usize;
    if tag > 3 {
        return None;
    }
    let mut out = vec![];
    let (mut s, mut ix, mut rem, mut mth, mut vc) = (St::N, 0usize, 0u64, 0u64, 0u64);
    let (mut acc, mut pw) = (0u64, 1u64);
    let (mut uc, mut pf) = (0i64, [0u64; 4]);
    for (p, &b) in bs.iter().enumerate() {
        let mut rw = [0u64; AKM_WIDTH];
        let bv = b as u64;
        rw[0] = 1;
        rw[1] = (p == 0) as u64;
        rw[3] = e.vid;
        rw[4] = p as u64;
        for x in 0..8 {
            rw[5 + x] = (bv >> x) & 1;
        }
        rw[st_col(s)] = 1;
        rw[21] = mth;
        rw[22] = ix as u64;
        rw[30] = vc;
        for x in 0..4 {
            rw[33 + x] = (x == tag) as u64;
        }
        rw[37] = e.tlast;
        rw[39] = e.u;
        let last: i128 = if s == St::S {
            rem as i128 - 1
        } else {
            ix as i128 - (st_len(s) as i128 - 1)
        };
        let fe_ = last == 0;
        rw[23] = fe_ as u64;
        rw[24] = inv(last);
        if s == St::S {
            rw[25] = rem;
        }
        if matches!(s, St::L | St::C) {
            if ix == 0 {
                pw = 1;
                acc = bv;
            } else {
                pw *= 256;
                acc += pw * bv;
            }
            rw[26] = pw;
            rw[27] = acc;
            if fe_ {
                rw[28] = (acc == 0) as u64;
                rw[29] = inv(acc as i128);
                if bv != 0 {
                    return None;
                }
            }
        }
        let z_a = matches!(s, St::L | St::C) && fe_ && acc == 0;
        // UTF-8
        let lo = bv & 15;
        let lo3 = bv & 7;
        rw[46] = (lo == 0) as u64;
        rw[47] = inv(lo as i128);
        rw[48] = (lo == 13) as u64;
        rw[49] = inv(lo as i128 - 13);
        rw[50] = (lo3 == 0) as u64;
        rw[51] = inv(lo3 as i128);
        rw[52] = (lo3 == 4) as u64;
        rw[53] = inv(lo3 as i128 - 4);
        if s == St::S {
            let class = if bv < 0x80 {
                40
            } else if bv < 0xC0 {
                41
            } else if (0xC2..=0xDF).contains(&bv) {
                42
            } else if (0xE0..=0xEF).contains(&bv) {
                43
            } else if (0xF0..=0xF4).contains(&bv) {
                44
            } else {
                return None;
            };
            rw[class] = 1;
            if class == 42 {
                rw[45] = inv(((bv >> 1) & 15) as i128);
            }
            rw[54..58].copy_from_slice(&pf);
            rw[58] = fe(uc as i128);
            let ucn = match class {
                41 => uc - 1,
                42 => 1,
                43 => 2,
                44 => 3,
                _ => 0,
            };
            if class != 41 && uc != 0 {
                return None;
            }
            rw[59] = fe(ucn as i128);
            let nf = [
                (class == 43 && lo == 0) as u64,
                (class == 43 && lo == 13) as u64,
                (class == 44 && lo3 == 0) as u64,
                (class == 44 && lo3 == 4) as u64,
            ];
            // second-byte ranges
            let b5 = (bv >> 5) & 1;
            let b4 = (bv >> 4) & 1;
            if (pf[0] == 1 && b5 != 1)
                || (pf[1] == 1 && b5 != 0)
                || (pf[2] == 1 && b5 == 0 && b4 == 0)
                || (pf[3] == 1 && (b5 != 0 || b4 != 0))
            {
                return None;
            }
            uc = ucn;
            pf = nf;
            if fe_ && uc != 0 {
                return None;
            }
        }
        let sd = (s == St::L && z_a) || (s == St::S && fe_);
        let md = sd && mth == 1;
        let z_v = md && vc == 1;
        rw[60] = sd as u64;
        rw[61] = md as u64;
        if md {
            rw[31] = z_v as u64;
            rw[32] = inv(vc as i128 - 1);
        }
        let end = (s == St::T && tag == 1)
            || (s == St::G && fe_ && tag == 3)
            || (s == St::C && fe_ && z_a)
            || z_v;
        rw[62] = end as u64;
        rw[2] = end as u64;
        rw[63] = (fe_ && !end) as u64;
        let e_s = s == St::L && fe_ && !end && !z_a;
        let e_c = s == St::C && fe_ && !end && !z_a;
        let e_m = md && !z_v;
        rw[64] = e_s as u64;
        rw[65] = e_c as u64;
        rw[66] = e_m as u64;
        let t1 = (tag == 1) as u64;
        rw[67] = (p == 0) as u64 * t1;
        rw[68] = (s == St::N) as u64 * t1;
        rw[69] = (s == St::T) as u64 * t1;
        if s == St::N {
            rw[38] = if tag == 1 {
                *e.post.get(p).unwrap_or(&0) as u64
            } else {
                bv
            };
        }
        out.push(rw);
        if end {
            return (p + 1 == bs.len()).then_some(out);
        }
        // next state
        if !fe_ {
            ix += 1;
            if s == St::S {
                rem -= 1;
            }
            continue;
        }
        ix = 0;
        let string_done = |mth: u64, vc: &mut u64| -> St {
            if mth == 0 {
                St::C
            } else {
                *vc -= 1;
                St::L
            }
        };
        s = match s {
            St::N => St::T,
            St::T => {
                if tag == 0 {
                    St::O
                } else {
                    St::G
                }
            }
            St::G => St::O,
            St::O => match bv {
                0 => {
                    mth = 0;
                    St::L
                }
                1 => St::A,
                _ => return None,
            },
            St::A => {
                mth = 0;
                St::L
            }
            St::L => {
                if z_a {
                    string_done(mth, &mut vc)
                } else {
                    rem = acc;
                    uc = 0;
                    pf = [0; 4];
                    St::S
                }
            }
            St::S => string_done(mth, &mut vc),
            St::C => {
                vc = acc;
                mth = 1;
                St::L
            }
        };
        if md {
            mth = 1;
        }
    }
    None
}

pub fn akm_trace(es: &[AkmE]) -> Result<Tab, String> {
    let mut rows = vec![];
    for e in es {
        rows.extend(akm_rows(e).ok_or_else(|| format!("akmV3: value {} does not decode", e.vid))?);
    }
    let mut t = tab(rows.len(), AKM_WIDTH);
    for (r, rw) in rows.iter().enumerate() {
        for (c, &x) in rw.iter().enumerate() {
            t.set(r, c, x);
        }
    }
    Ok(t)
}

// ---------------------------------------------------------------------------- relays

/// `kibV3` rows: the `PKEY` records `[w₀, w₁, w₂, t, sym, last]`.
pub fn kib_trace(recs: &[Vec<u8>]) -> Tab {
    let mut t = tab(recs.len(), 7);
    for (r, x) in recs.iter().enumerate() {
        t.set(r, 0, 1);
        for (c, &v) in x.iter().enumerate() {
            t.set(r, 1 + c, v as u64);
        }
    }
    t
}

/// `plfV3` rows: `(pos, digest)`.
pub fn plf_trace(leaves: &[Vec<u8>]) -> Tab {
    let mut t = tab(leaves.len(), 34);
    for (r, d) in leaves.iter().enumerate() {
        t.set(r, 0, 1);
        t.set(r, 1, r as u64);
        for (c, &v) in d.iter().enumerate() {
            t.set(r, 2 + c, v as u64);
        }
    }
    t
}

/// `ridV3` rows: `(j, l, i bits, b, l bits)` for the local id bytes.
pub fn rid_trace(ids: &[Vec<u8>]) -> Tab {
    let n: usize = ids.iter().map(|d| d.len()).sum();
    let mut t = tab(n, 21);
    let mut r = 0;
    for (l, d) in ids.iter().enumerate() {
        for (i, &b) in d.iter().enumerate() {
            t.set(r, 0, 1);
            t.set(r, 1, (32 * l + i) as u64);
            t.set(r, 2, l as u64);
            set_bits(&mut t, r, 3, 5, i as u128);
            t.set(r, 8, b as u64);
            // the slot's 12 bits (range check of `l`, lane v3-d1-a7b)
            set_bits(&mut t, r, 9, 12, l as u128);
            r += 1;
        }
    }
    t
}
