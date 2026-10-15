//! The unread-key tables of `nearAirV3D1` (plan §5 R-5 → (B), lane v3-d1-a7b): the honest
//! entries and traces of
//! * `walkU` (30): the walks of every `txKeys` entry over the main pre trie, with the stub
//!   terminal `mT` (`SEDGE`) where a child or a value is not revealed;
//! * the stub windows of `nodeD1` (table 2, columns 188–191: `su`, `sI`, `sZ`, `mSt`);
//! * the gap lookups of `uniqD1` (table 6, columns 53–55: `sidx`, `lt`, `mG`);
//! * `nmemV3` (31): one 32-row segment per stub window's `NMQ (τ, h)`;
//! * `uvalV3` (32): the bytes of the values revealed only for unread keys;
//! * `kibD1` (27): `kibV3` with the bits of `w₂` (routing to `UKEYNIB`).
//!
//! Column layouts as `ZkFormal/NearV3/D1/Tables/{NodeStubDefs,UniqGapDefs,WalkUDefs,NmemDefs,
//! UvalDefs,KibUDefs}.lean`.

use std::collections::HashMap;

use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use serde::Serialize;

use crate::field::F;
use crate::v3::node::{NODE_A7_WIDTH, NodeS3};
use crate::v3::walks::{MODE_STUB, SYM_WILD};
use crate::v3::{Tab, UEnt, WStep3, WalkR, log_of, pad_log22};

const SYM_END: u64 = 16;

fn b(x: bool) -> u64 {
    x as u64
}
fn at(e: &[u64], i: usize) -> u64 {
    e.get(i).copied().unwrap_or(0)
}
fn tab(rows: usize, width: usize) -> Tab {
    let log = pad_log22(log_of(rows.max(1)));
    Tab {
        log,
        width,
        cells: vec![0; width << log],
    }
}

// ---------------------------------------------------------------------- kibD1 (27)

pub const KIB_D1_WIDTH: usize = 15;

/// `kibD1` rows: the `PKEY` record and the bits of `w₂`.
pub fn kib_d1_trace(recs: &[Vec<u8>]) -> Tab {
    let mut t = tab(recs.len(), KIB_D1_WIDTH);
    for (r, x) in recs.iter().enumerate() {
        t.set(r, 0, 1);
        for (c, &v) in x.iter().enumerate() {
            t.set(r, 1 + c, v as u64);
        }
        let w2 = x.get(2).copied().unwrap_or(0) as u64;
        for j in 0..8 {
            t.set(r, 7 + j, (w2 >> j) & 1);
        }
    }
    t
}

// ---------------------------------------------------------------------- walkU (30)

pub const WALKU_WIDTH: usize = 58;

fn inv_of(s: &WStep3) -> u64 {
    let d = F::from_u64(s.sym) - F::from_u64(at(&s.e, 2));
    d.try_inverse().unwrap_or(F::ZERO).as_canonical_u32() as u64
}

/// `walkU` rows: as `walkV3`'s (`walk_aligned`), with the stub mode `mT` (56), its wildcard
/// flag `mW` (57), and `fk`, `kk` left `0` (no `FINAL`).
pub fn walku_trace(ws: &[WalkR]) -> Tab {
    let rows: usize = ws.iter().map(|w| w.steps.len()).sum();
    let mut t = tab(rows, WALKU_WIDTH);
    let mut q = 0;
    for wv in ws {
        let n = wv.steps.len();
        for (j, s) in wv.steps.iter().enumerate() {
            let last = j + 1 == n;
            let stub = s.mode == MODE_STUB;
            let mut row = [0u64; WALKU_WIDTH];
            row[..22].copy_from_slice(&[
                1,
                b(j == 0),
                b(last),
                b(j != 0),
                wv.w,
                wv.tau,
                j.saturating_sub(1) as u64,
                s.sym,
                at(&s.e, 0),
                at(&s.e, 1),
                at(&s.e, 2),
                at(&s.e, 3),
                at(&s.e, 4),
                at(&s.e, 5),
                s.u,
                b(s.mode == 0),
                b(s.mode == 1),
                b(s.mode == 2),
                b(s.mode == 3),
                if s.mode == 1 { inv_of(s) } else { 0 },
                if s.mode == 2 { s.hv } else { 0 },
                s.ub,
            ]);
            for i in 0..16 {
                row[24 + i] = if s.mode == 2 { (s.bm >> i) & 1 } else { 0 };
                row[40 + i] = b(s.mode == 2 && !last && s.sym == i as u64);
            }
            row[56] = b(stub);
            row[57] = b(stub && at(&s.e, 2) == SYM_WILD);
            for (c, x) in row.into_iter().enumerate() {
                t.set(q, c, x);
            }
            q += 1;
        }
    }
    t
}

// ------------------------------------------------------------- nodeD1 stub windows (2)

pub const NODE_D1_WIDTH: usize = 192;

/// One stub window: its record, `SEDGE` key, use count, and `NMQ (τ, h)`.
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct StubW {
    pub nid: u64,
    pub i: u64,
    pub z: u64,
    pub uses: u64,
    pub tau: u64,
    pub h: Vec<u64>,
}

/// The stub windows of the node records `vs` used by the `SEDGE` keys `uses`, in record /
/// window order.  Every key must name an unrevealed child or value window.
pub fn stub_windows(
    vs: &[NodeS3],
    uses: &HashMap<[u64; 3], u64>,
) -> Result<Vec<StubW>, String> {
    let mut out = vec![];
    let mut found = 0usize;
    for (n, s) in vs.iter().enumerate() {
        for (key, h) in crate::v3::node::unrevealed_windows(n as u64, &s.v) {
            if let Some(&k) = uses.get(&key) {
                found += 1;
                out.push(StubW {
                    nid: n as u64,
                    i: key[1],
                    z: key[2],
                    uses: k,
                    tau: s.tau,
                    h,
                });
            }
        }
    }
    if found != uses.len() {
        return Err(format!(
            "nodeD1: {} of {} stub keys name an unrevealed window",
            found,
            uses.len()
        ));
    }
    Ok(out)
}

/// `nodeD1`: `nodeA7` (`base`, width 188) with the stub windows' columns `su`, `sI`, `sZ`,
/// `mSt` on their first rows.
pub fn node_d1(base: &Tab, vs: &[NodeS3], stubs: &[StubW]) -> Result<Tab, String> {
    if base.width != NODE_A7_WIDTH {
        return Err("nodeD1: base is not nodeA7".into());
    }
    let mut t = crate::v3::widen(base, NODE_D1_WIDTH);
    let rows = crate::v3::node::window_rows(vs);
    for s in stubs {
        let q = *rows
            .get(&[s.nid, s.i, s.z])
            .ok_or_else(|| format!("nodeD1: no window row for stub {:?}", (s.nid, s.i, s.z)))?;
        t.set(q, 188, 1);
        t.set(q, 189, s.i);
        t.set(q, 190, s.z);
        t.set(q, 191, s.uses);
    }
    Ok(t)
}

// ---------------------------------------------------------- uniqD1 gaps (6), nmemV3 (31)

pub const UNIQ_D1_WIDTH: usize = 56;
pub const NMEM_WIDTH: usize = 67;

type U256 = [u8; 32];

fn u256(xs: &[u64]) -> U256 {
    let mut o = [0u8; 32];
    for (i, x) in xs.iter().take(32).enumerate() {
        o[i] = *x as u8;
    }
    o
}

/// `x < y` for little-endian 256-bit numbers.
fn lt256(x: &U256, y: &U256) -> bool {
    x.iter().rev().cmp(y.iter().rev()) == std::cmp::Ordering::Less
}

/// `x − y − 1` (requires `y < x`).
fn sub1(x: &U256, y: &U256) -> U256 {
    let mut out = [0u8; 32];
    let mut borrow = 1i32;
    for i in 0..32 {
        let d = x[i] as i32 - y[i] as i32 - borrow;
        out[i] = d.rem_euclid(256) as u8;
        borrow = (d < 0) as i32;
    }
    out
}

/// The carries of `x + y + 1`, byte by byte (`c[0] = 1`).
fn carries1(x: &U256, y: &U256) -> [u8; 33] {
    let mut c = [0u8; 33];
    c[0] = 1;
    for i in 0..32 {
        c[i + 1] = ((x[i] as u32 + y[i] as u32 + c[i] as u32) / 256) as u8;
    }
    c
}

/// One `nmemV3` query: `h` is not a digest of instance `tau`, shown by the gap at entry
/// `target` in mode `0` between, `1` below the first, `2` above the last.
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct NmemQ {
    pub tau: u64,
    pub h: Vec<u64>,
    pub target: u64,
    pub mode: u64,
    pub rank: u64,
}

/// Place every stub hash in `uniqV3`'s sorted entries `l`.
pub fn nmem_queries(l: &[UEnt], stubs: &[StubW]) -> Result<Vec<NmemQ>, String> {
    let keys: Vec<U256> = l.iter().map(|e| u256(&e.bytes)).collect();
    let mut ranks: HashMap<u64, u64> = HashMap::new();
    let mut out = vec![];
    for s in stubs {
        let h = u256(&s.h);
        // first entry with (τ, key) > (s.tau, h)
        let pos = l
            .iter()
            .zip(&keys)
            .position(|(e, k)| e.tau > s.tau || (e.tau == s.tau && !lt256(k, &h) && *k != h));
        if l.iter().zip(&keys).any(|(e, k)| e.tau == s.tau && *k == h) {
            return Err(format!("nmemV3: stub hash of record {} is in the store", s.nid));
        }
        let same = |i: usize| l.get(i).is_some_and(|e| e.tau == s.tau);
        let (target, mode) = match pos {
            Some(p) if same(p) => {
                if p > 0 && same(p - 1) {
                    (p, 0)
                } else {
                    (p, 1)
                }
            }
            Some(p) if p > 0 && same(p - 1) => (p - 1, 2),
            None if !l.is_empty() && same(l.len() - 1) => (l.len() - 1, 2),
            _ => return Err(format!("nmemV3: instance {} has no store entry", s.tau)),
        };
        let r = ranks.entry(target as u64).or_default();
        out.push(NmemQ {
            tau: s.tau,
            h: s.h.clone(),
            target: target as u64,
            mode,
            rank: *r,
        });
        *r += 1;
    }
    Ok(out)
}

/// `uniqD1`: `uniqV3` (`base`, width 53, entries `l`) with `sidx`, `lt`, `mG`.
pub fn uniq_d1(base: &Tab, l: &[UEnt], qs: &[NmemQ]) -> Result<Tab, String> {
    if base.width != 53 {
        return Err("uniqD1: base is not uniqV3".into());
    }
    let mut t = crate::v3::widen(base, UNIQ_D1_WIDTH);
    let h = t.height();
    let mut uses: HashMap<u64, u64> = HashMap::new();
    for q in qs {
        *uses.entry(q.target).or_default() += 1;
    }
    for (s, e) in l.iter().enumerate() {
        let lt = s + 1 == l.len() || l[s + 1].tau != e.tau;
        for i in 0..32 {
            let q = 32 * s + i;
            if q >= h {
                break;
            }
            t.set(q, 53, s as u64);
            t.set(q, 54, b(lt));
            t.set(q, 55, uses.get(&(s as u64)).copied().unwrap_or(0));
        }
    }
    Ok(t)
}

/// `nmemV3` rows.  `lo` is `uniqD1`'s delay-line byte `d 31` of the target row (the previous
/// entry's byte, or the wrapped padding byte for the first entry).
pub fn nmem_trace(l: &[UEnt], uniq_h: usize, qs: &[NmemQ]) -> Tab {
    let keys: Vec<U256> = l.iter().map(|e| u256(&e.bytes)).collect();
    let bb = |q: usize| -> u8 {
        if q < 32 * l.len() {
            keys[q / 32][q % 32]
        } else {
            0
        }
    };
    let mut t = tab(32 * qs.len(), NMEM_WIDTH);
    for (k, qy) in qs.iter().enumerate() {
        let s = qy.target as usize;
        let e = &l[s];
        let h = u256(&qy.h);
        let hi = keys[s];
        let lo: U256 = std::array::from_fn(|i| bb((32 * s + i + 2 * uniq_h - 32) % uniq_h));
        let ft = s == 0;
        let st = s != 0 && l[s - 1].tau != e.tau;
        let lt = s + 1 == l.len() || l[s + 1].tau != e.tau;
        let (ga, gb) = (qy.mode == 0 || qy.mode == 2, qy.mode == 0 || qy.mode == 1);
        let x = if qy.mode == 2 { hi } else { lo };
        let (da, ca) = if ga {
            let d = sub1(&h, &x);
            (d, carries1(&x, &d))
        } else {
            let mut c = [0u8; 33];
            c[0] = 1;
            ([0u8; 32], c)
        };
        let (db, cb) = if gb {
            let d = sub1(&hi, &h);
            (d, carries1(&h, &d))
        } else {
            let mut c = [0u8; 33];
            c[0] = 1;
            ([0u8; 32], c)
        };
        for i in 0..32 {
            let r = 32 * k + i;
            let mut row = vec![0u64; NMEM_WIDTH];
            row[0] = 1;
            row[1] = b(i == 0);
            row[2] = b(i == 31);
            row[3] = i as u64;
            row[4] = qy.tau;
            row[5] = qy.target;
            row[6] = b(qy.mode == 0);
            row[7] = b(qy.mode == 1);
            row[8] = b(qy.mode == 2);
            row[9] = lo[i] as u64;
            row[10] = hi[i] as u64;
            row[11] = b(ft);
            row[12] = b(st);
            row[13] = b(lt);
            row[14] = qy.rank;
            for j in 0..32 {
                row[15 + j] = if i + j < 32 { h[i + j] as u64 } else { 0 };
            }
            row[47] = ca[i] as u64;
            row[48] = ca[i + 1] as u64;
            row[49] = cb[i] as u64;
            row[50] = cb[i + 1] as u64;
            for j in 0..8 {
                row[51 + j] = ((da[i] >> j) & 1) as u64;
                row[59 + j] = ((db[i] >> j) & 1) as u64;
            }
            for (c, v) in row.into_iter().enumerate() {
                t.set(r, c, v);
            }
        }
    }
    t
}

// ---------------------------------------------------------------------- uvalV3 (32)

pub const UVAL_WIDTH: usize = 12;

/// `uvalV3` rows: `(vid, pos, byte, bits)` for each value revealed only for unread keys.
pub fn uval_trace(vals: &[(u64, Vec<u8>)]) -> Tab {
    let n: usize = vals.iter().map(|(_, v)| v.len()).sum();
    let mut t = tab(n, UVAL_WIDTH);
    let mut r = 0;
    for (vid, v) in vals {
        for (pos, &x) in v.iter().enumerate() {
            t.set(r, 0, 1);
            t.set(r, 1, *vid);
            t.set(r, 2, pos as u64);
            t.set(r, 3, x as u64);
            for j in 0..8 {
                t.set(r, 4 + j, ((x >> j) & 1) as u64);
            }
            r += 1;
        }
    }
    t
}

/// The stub keys of a list of unread walks, for the summary dump.
pub fn terminal_of(w: &WalkR) -> (u64, Vec<u64>) {
    let s = w.steps.iter().find(|s| s.mode >= 1).or(w.steps.last());
    match s {
        Some(s) => (s.mode, s.e.iter().take(3).copied().collect()),
        None => (0, vec![]),
    }
}
