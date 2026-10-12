//! Honest per-table trace generators for `nearAirV3` (part 2 of the v2 prover).
//!
//! Each `*_aligned` function is the Rust twin of a Lean aligned generator:
//! `ZkFormal.NearV3.Render.{bnd,akey,head,val}TraceAligned` (`Render/Padded.lean`)
//! and `{uniq,walk}TraceAligned` (`Render/PaddedTrie.lean`).  The input is the
//! table's entry list (the Lean structure of the same name, deserialized from
//! JSON with the Lean field names); the output is the trace at the aligned
//! height `padLog22 (logOf n)` with every cell reduced mod `P` (`Fp.ofNat`).
//! `conformance/run-v2.sh` compares the dumps with `np-lean-render-v3` byte for
//! byte.
//!
//! The Lean cells are functions of unbounded naturals; here the scalar fields
//! are `u64`.  The one place where that matters is `uniq`, whose cells compare
//! 256-bit keys: [`uniq_aligned`] requires the shape of `UOk.mem` (32 bytes,
//! each `< 256`) and returns an error otherwise.

use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use serde::Deserialize;

use crate::field::{F, P};

pub mod acct;
pub mod chacha;
pub mod collect;
pub mod d0;
pub mod entries;
pub mod hint;
pub mod mrksort;
pub mod node;
pub mod prep;
pub mod public;
pub mod prove;
pub mod qv;
pub mod rcpt;
pub mod sample;
pub mod sched;
pub mod sha;
pub mod size;
pub mod srcp;
pub mod ups;

/// A generated table: `2^log` rows of `width` canonical cells, row-major.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tab {
    pub log: usize,
    pub width: usize,
    pub cells: Vec<u32>,
}

impl Tab {
    fn zero(log: usize, width: usize) -> Tab {
        Tab {
            log,
            width,
            cells: vec![0; width << log],
        }
    }
    pub fn height(&self) -> usize {
        1 << self.log
    }
    pub fn set(&mut self, r: usize, c: usize, x: u64) {
        self.cells[r * self.width + c] = (x % P as u64) as u32;
    }
    /// The `np-render-v3-table` dump: `log, width`, then the cells (u32 LE).
    pub fn dump(&self) -> Vec<u8> {
        let mut b = Vec::with_capacity(8 + 4 * self.cells.len());
        b.extend_from_slice(&(self.log as u32).to_le_bytes());
        b.extend_from_slice(&(self.width as u32).to_le_bytes());
        for &x in &self.cells {
            b.extend_from_slice(&x.to_le_bytes());
        }
        b
    }
    pub fn to_matrix(&self) -> p3_matrix::dense::RowMajorMatrix<F> {
        p3_matrix::dense::RowMajorMatrix::new(
            self.cells.iter().map(|&x| F::from_u32(x)).collect(),
            self.width,
        )
    }
}

/// `clog2`, `logOf = max 1 ∘ clog2` (`Near/Render/Common.lean`).
pub fn log_of(n: usize) -> usize {
    crate::near::info::log_of(n)
}

/// `padLog22 l = 22 − 3·((22 − l) / 3)` (`Size/PadHeader.lean`, truncating `−`).
pub fn pad_log22(l: usize) -> usize {
    22 - 3 * (22usize.saturating_sub(l) / 3)
}

fn get(xs: &[u64], i: usize) -> u64 {
    xs.get(i).copied().unwrap_or(0)
}

fn b(x: bool) -> u64 {
    x as u64
}

// ---------------------------------------------------------------- bnd (19)

pub const BND_WIDTH: usize = 6;

#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct BndE {
    pub x: u64,
    pub lo: u64,
    pub hi: u64,
    pub hn: u64,
    #[serde(rename = "U")]
    pub u: u64,
}

/// `bndTraceAligned`: row `q < |es|` is `[1, x, lo, hi, hn, U]`.
pub fn bnd_aligned(es: &[BndE]) -> Tab {
    let mut t = Tab::zero(pad_log22(log_of(es.len())), BND_WIDTH);
    for (q, e) in es.iter().enumerate().take(t.height()) {
        for (c, x) in [1, e.x, e.lo, e.hi, e.hn, e.u].into_iter().enumerate() {
            t.set(q, c, x);
        }
    }
    t
}

// --------------------------------------------------------------- akey (18)

pub const AKEY_WIDTH: usize = 7;

#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct AkeyE {
    pub vid: u64,
    #[serde(rename = "U")]
    pub u: u64,
    pub bytes: Vec<u64>,
}

/// `akeyTraceAligned`: record `s` on rows `9s … 9s+8`, lane `p`:
/// `[1, [p=0], [p=8], vid, p, bytes[p], U]`.
pub fn akey_aligned(es: &[AkeyE]) -> Tab {
    let mut t = Tab::zero(pad_log22(log_of(9 * es.len())), AKEY_WIDTH);
    for q in 0..(9 * es.len()).min(t.height()) {
        let (e, p) = (&es[q / 9], q % 9);
        let row = [
            1,
            b(p == 0),
            b(p == 8),
            e.vid,
            p as u64,
            get(&e.bytes, p),
            e.u,
        ];
        for (c, x) in row.into_iter().enumerate() {
            t.set(q, c, x);
        }
    }
    t
}

// ---------------------------------------------------------------- head (3)

pub const HEAD_WIDTH: usize = 73;

#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct HeadE {
    pub tau: u64,
    pub rid: u64,
    pub rlen: u64,
    pub rres: u64,
    #[serde(rename = "mE")]
    pub m_e: u64,
    pub pre: Vec<u64>,
    pub post: Vec<u64>,
}

/// `headTraceAligned`: head `t` on rows `32t + i`: `[1, [i=0], [i=31], τ, rid, rlen,
/// rres, i, mE]`, then `reg m = pre[m+i]` and `preg m = post[m+i]` (`m < 32`).
pub fn head_aligned(hs: &[HeadE]) -> Tab {
    let mut t = Tab::zero(pad_log22(log_of(32 * hs.len())), HEAD_WIDTH);
    for q in 0..(32 * hs.len()).min(t.height()) {
        let (h, i) = (&hs[q / 32], q % 32);
        let head = [
            1,
            b(i == 0),
            b(i == 31),
            h.tau,
            h.rid,
            h.rlen,
            h.rres,
            i as u64,
            h.m_e,
        ];
        for (c, x) in head.into_iter().enumerate() {
            t.set(q, c, x);
        }
        for m in 0..32 {
            t.set(q, 9 + m, get(&h.pre, m + i));
            t.set(q, 41 + m, get(&h.post, m + i));
        }
    }
    t
}

// ----------------------------------------------------------------- val (4)

pub const VAL_WIDTH: usize = 15;

#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct ValE {
    pub vid: u64,
    pub len: u64,
    pub vz: bool,
    pub dup: bool,
    pub hd: bool,
    #[serde(rename = "repE")]
    pub rep_e: u64,
    pub bytes: Vec<u64>,
}

impl ValE {
    /// `nOf`: one row for an empty value, else `len`.
    fn n_of(&self) -> u64 {
        if self.vz { 1 } else { self.len }
    }
}

/// `valTraceAligned`: the record rows `(t, p)`, `p < nOf es[t]`, then the `SUM`
/// row (`sumr = 1`), then zero padding; column 11 (`sz`) is `szAt q` on every row.
pub fn val_aligned(es: &[ValE]) -> Tab {
    let r: u64 = es.iter().map(ValE::n_of).sum();
    let r = usize::try_from(r).expect("valV3: row count");
    let mut t = Tab::zero(pad_log22(log_of(r + 1)), VAL_WIDTH);
    let h = t.height();
    let mut q = 0usize;
    let mut sz = 0u64;
    'recs: for e in es {
        let n = e.n_of();
        let gw = b(!(e.vz || e.dup));
        for p in 0..n {
            if q >= h {
                break 'recs;
            }
            let row = [
                1,
                b(p == 0),
                b(p + 1 == n),
                e.vid,
                e.len,
                p,
                get(&e.bytes, p as usize),
                b(e.vz),
                b(e.dup),
                b(e.hd),
                e.rep_e,
                sz,
                0,
                b(!e.vz),
                b(p == 0 && e.dup),
            ];
            for (c, x) in row.into_iter().enumerate() {
                t.set(q, c, x);
            }
            sz += gw;
            q += 1;
        }
    }
    // `szAt q` for `q ≥ R` is the full sum; the `SUM` row is row `R`.
    for q in r.min(h)..h {
        t.set(q, 11, sz);
    }
    if r < h {
        t.set(r, 12, 1);
    }
    t
}

// ---------------------------------------------------------------- uniq (6)

pub const UNIQ_WIDTH: usize = 53;

#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct UEnt {
    pub eid: u64,
    pub tau: u64,
    pub bytes: Vec<u64>,
}

/// A 256-bit little-endian number (`le256` of 32 bytes).
type U256 = [u8; 32];

fn le256(bs: &[u64]) -> Result<U256, String> {
    if bs.len() != 32 || bs.iter().any(|&x| x >= 256) {
        return Err("uniqV3 entry: bytes must be 32 values < 256 (UOk.mem)".into());
    }
    Ok(std::array::from_fn(|i| bs[i] as u8))
}

/// `x − y − k` over naturals (`0` if negative).
fn sub256(x: &U256, y: &U256, k: u8) -> U256 {
    let mut out = [0u8; 32];
    let mut borrow = k as i32;
    for i in 0..32 {
        let d = x[i] as i32 - y[i] as i32 - borrow;
        out[i] = d.rem_euclid(256) as u8;
        borrow = (d < 0) as i32;
    }
    if borrow != 0 { [0; 32] } else { out }
}

/// `SortGen.carryFrom x y c i` for `i ≤ 32`: the carries of `x + y + c` byte by byte.
fn carries(x: &U256, y: &U256, c: u8) -> [u8; 33] {
    let mut out = [0u8; 33];
    out[0] = c;
    for i in 0..32 {
        out[i + 1] = ((x[i] as u32 + y[i] as u32 + out[i] as u32) / 256) as u8;
    }
    out
}

/// `uniqTraceAligned`: entry `t` on rows `32t + i` (columns 0–20, see
/// `UniqGen.actCell`); the delay line `d j` (column `21 + j`, `j < 32`) is `bb` of
/// row `(q + 2H − 1 − j) mod H` on every row, padding included.
pub fn uniq_aligned(l: &[UEnt]) -> Result<Tab, String> {
    let keys: Vec<U256> = l
        .iter()
        .map(|e| le256(&e.bytes))
        .collect::<Result<_, _>>()?;
    let mut t = Tab::zero(pad_log22(log_of(32 * l.len())), UNIQ_WIDTH);
    let h = t.height();
    let act = (32 * l.len()).min(h);
    let bb = |q: usize| {
        if q < 32 * l.len() {
            keys[q / 32][q % 32] as u64
        } else {
            0
        }
    };
    for (s, e) in l.iter().enumerate() {
        if 32 * s >= h {
            break;
        }
        let same = s != 0 && e.tau == l[s - 1].tau;
        let st = b(s != 0 && !same);
        let eq = same && keys[s] == keys[s - 1];
        let peid = if s == 0 { 0 } else { l[s - 1].eid };
        let k = 1 - eq as u8;
        let (diff, carry) = if same {
            let d = sub256(&keys[s], &keys[s - 1], k);
            let c = carries(&keys[s - 1], &d, k);
            (d, c)
        } else {
            let mut c = [0u8; 33];
            c[0] = 1;
            ([0u8; 32], c)
        };
        for i in 0..32 {
            let q = 32 * s + i;
            if q >= act {
                break;
            }
            let head = [
                1,
                b(i == 0),
                b(i == 31),
                b(s == 0),
                e.eid,
                peid,
                e.tau,
                st,
                eq as u64,
                i as u64,
                keys[s][i] as u64,
                carry[i] as u64,
                carry[i + 1] as u64,
            ];
            for (c, x) in head.into_iter().enumerate() {
                t.set(q, c, x);
            }
            for j in 0..8 {
                t.set(q, 13 + j, ((diff[i] >> j) & 1) as u64);
            }
        }
    }
    for q in 0..h {
        for j in 0..32 {
            // `(q + 2H − 1 − j) % H` with Lean's truncating subtraction.
            let src = (q + 2 * h).saturating_sub(1).saturating_sub(j) % h;
            t.set(q, 21 + j, bb(src));
        }
    }
    Ok(t)
}

// ---------------------------------------------------------------- walk (5)

pub const WALK_WIDTH: usize = 56;

#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct WStep3 {
    pub mode: u64,
    pub sym: u64,
    pub e: Vec<u64>,
    pub u: u64,
    pub bm: u64,
    pub hv: u64,
    pub ub: u64,
}

#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct WalkR {
    pub w: u64,
    pub tau: u64,
    pub steps: Vec<WStep3>,
}

/// `FK_VAL`, `FK_ABS` (`Near/Ids.lean`).
pub const FK_VAL: u64 = 0;
pub const FK_ABS: u64 = 1;

impl WalkR {
    fn last(&self) -> WStep3 {
        self.steps.last().cloned().unwrap_or_default()
    }
    /// `WalkR.fk`, `WalkR.k`.
    fn fk(&self) -> u64 {
        if self.last().mode == 0 {
            FK_VAL
        } else {
            FK_ABS
        }
    }
    fn k(&self) -> u64 {
        let l = self.last();
        if l.mode == 0 { get(&l.e, 3) } else { 0 }
    }
}

/// `invOf`: `(sym − nib)⁻¹` in `Fp` (`0 ↦ 0`).
fn inv_of(s: &WStep3) -> u64 {
    let d = F::from_u64(s.sym) - F::from_u64(get(&s.e, 2));
    d.try_inverse().unwrap_or(F::ZERO).as_canonical_u32() as u64
}

/// `walkTraceAligned`: one row per step `(wv, j)` in table order (`WalkGen.rowCell`).
pub fn walk_aligned(ws: &[WalkR]) -> Tab {
    let rows: usize = ws.iter().map(|w| w.steps.len()).sum();
    let mut t = Tab::zero(pad_log22(log_of(rows)), WALK_WIDTH);
    let h = t.height();
    let mut q = 0;
    'walks: for wv in ws {
        let n = wv.steps.len();
        let (fk, k) = (wv.fk(), wv.k());
        for (j, s) in wv.steps.iter().enumerate() {
            if q >= h {
                break 'walks;
            }
            let last = j + 1 == n;
            let mut row = [0u64; WALK_WIDTH];
            row[..24].copy_from_slice(&[
                1,
                b(j == 0),
                b(last),
                b(j != 0),
                wv.w,
                wv.tau,
                j.saturating_sub(1) as u64,
                s.sym,
                get(&s.e, 0),
                get(&s.e, 1),
                get(&s.e, 2),
                get(&s.e, 3),
                get(&s.e, 4),
                get(&s.e, 5),
                s.u,
                b(s.mode == 0),
                b(s.mode == 1),
                b(s.mode == 2),
                b(s.mode == 3),
                if s.mode == 1 { inv_of(s) } else { 0 },
                if s.mode == 2 { s.hv } else { 0 },
                s.ub,
                if last { fk } else { 0 },
                if last { k } else { 0 },
            ]);
            for i in 0..16 {
                row[24 + i] = if s.mode == 2 { (s.bm >> i) & 1 } else { 0 };
                row[40 + i] = b(s.mode == 2 && !last && s.sym == i as u64);
            }
            for (c, x) in row.into_iter().enumerate() {
                t.set(q, c, x);
            }
            q += 1;
        }
    }
    t
}

/// Table names accepted by [`render`] with their `nearAirV3` table index.
pub const TABLES: &[(&str, usize)] = &[
    ("head", 3),
    ("val", 4),
    ("walk", 5),
    ("uniq", 6),
    ("ups", 7),
    ("acct", 17),
    ("akey", 18),
    ("bnd", 19),
    ("size", 21),
    ("rcpt", 16),
    ("node", 2),
    ("srcp", 20),
    ("qv", 22),
    ("chacha", 8),
    ("rng", 9),
    ("shuf", 10),
    ("codec", 11),
    ("scandist", 12),
    ("proc", 13),
    ("mem", 14),
    ("cmp", 15),
    ("sha_t", 0),
    ("sha_r", 1),
    ("mrk", 23),
    ("sort", 24),
];

/// Parse `json` as the entry list of `table` and render its aligned trace.
pub fn render(table: &str, json: &str) -> Result<Tab, String> {
    fn p<T: for<'a> Deserialize<'a>>(s: &str) -> Result<Vec<T>, String> {
        serde_json::from_str(s).map_err(|e| e.to_string())
    }
    Ok(match table {
        "bnd" => bnd_aligned(&p(json)?),
        "akey" => akey_aligned(&p(json)?),
        "head" => head_aligned(&p(json)?),
        "val" => val_aligned(&p(json)?),
        "uniq" => uniq_aligned(&p(json)?)?,
        "walk" => walk_aligned(&p(json)?),
        "node" => node::node_aligned(&p(json)?),
        "chacha" => chacha::render(json)?,
        "rng" => chacha::render_rng(json)?,
        "shuf" => chacha::render_shuf(json)?,
        "ups" | "rcpt" | "srcp" | "qv" | "sched" | "acct" | "size" => match table {
            "ups" => ups::render(json),
            "rcpt" => rcpt::render(json),
            "srcp" => srcp::render(json),
            "qv" => qv::render(json),
            "sched" => sched::render(json),
            "acct" => acct::render(json),
            _ => size::render(json),
        }?,
        "codec" => sched::codec(json)?,
        "scandist" => sched::scandist(json)?,
        "proc" => sched::proc(json)?,
        "mem" => sched::mem(json)?,
        "cmp" => sched::cmp(json)?,
        "sha_t" | "sha_r" => sha::render(json)?,
        "mrk" => mrksort::render_mrk(json)?,
        "sort" => mrksort::render_sort(json)?,
        t => return Err(format!("unknown table {t}")),
    })
}

#[cfg(test)]
mod tests {
    use super::sample::Rng;
    use super::*;

    #[test]
    fn pad_log22_matches_lean() {
        // `22 − 3·((22 − l) / 3)`: rounds up to the residue 1 mod 3, capped at 22
        let want = [
            1, 1, 4, 4, 4, 7, 7, 7, 10, 10, 10, 13, 13, 13, 16, 16, 16, 19, 19, 19, 22, 22, 22,
        ];
        for (l, w) in want.iter().enumerate() {
            assert_eq!(pad_log22(l), *w, "l = {l}");
        }
        assert_eq!(pad_log22(30), 22);
    }

    #[test]
    fn u256_against_u128() {
        let mut r = Rng::new(5);
        let as_u128 = |x: &U256| x.iter().rev().fold(0u128, |a, &b| a * 256 + b as u128);
        for _ in 0..2000 {
            let mut x = [0u8; 32];
            let mut y = [0u8; 32];
            for i in 0..15 {
                x[i] = r.below(256) as u8;
                y[i] = r.below(256) as u8;
            }
            let k = r.below(2) as u8;
            let (xv, yv) = (as_u128(&x), as_u128(&y));
            let d = sub256(&x, &y, k);
            assert_eq!(as_u128(&d), xv.saturating_sub(yv + k as u128));
            let c = carries(&x, &y, k);
            for (i, &ci) in c.iter().enumerate().take(16) {
                // carry into byte i = ((x mod 256^i) + (y mod 256^i) + k) / 256^i
                let m = 1u128 << (8 * i);
                assert_eq!(ci as u128, ((xv % m) + (yv % m) + k as u128) / m, "i = {i}");
            }
        }
    }

    #[test]
    fn val_sum_row_and_sz() {
        let mut r = Rng::new(3);
        let es = sample::val(&mut r, 9);
        let t = val_aligned(&es);
        let rows: usize = es.iter().map(|e| e.n_of() as usize).sum();
        let total: u64 = es.iter().filter(|e| !e.vz && !e.dup).map(|e| e.len).sum();
        assert_eq!(t.cells[rows * VAL_WIDTH + 12], 1);
        assert_eq!(t.cells[rows * VAL_WIDTH], 0);
        assert_eq!(t.cells[(t.height() - 1) * VAL_WIDTH + 11] as u64, total);
    }
}
