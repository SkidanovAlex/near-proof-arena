//! Honest `srcpV3` trace generator for `nearAirV3` (table index 20), the Rust
//! twin of the Lean row generator `ZkFormal.NearV3.Render.SrcpGen`
//! (`Rcpt/Render/Srcp/Gen.lean`): the root row, 32 leaf rows and 64 rows per
//! path item of every source-proof block, then padding that carries the final
//! `sz` accumulator.  The aligned height is `padLog22 (logOf (R bs))`, the
//! wrapper used by `Render/PaddedSrcp.lean`'s `srcpTraceAligned`.
//!
//! Input: the `List SrcpB` entries, deserialized from JSON with the Lean field
//! names (`SrcpItem` is a nested object list).  `conformance/run-v2.sh` compares
//! the dump with `np-lean-render-v3` byte for byte.

use serde::Deserialize;

use super::{Tab, b, get, log_of, pad_log22};

pub const SRCP_WIDTH: usize = 56;

/// `ZkFormal.Near.Ids`: SHA message kinds (`Id = kind + 16·idx`).
const K_RC: u64 = 1;
const K_SRC: u64 = 13;

fn msg_id(kind: u64, idx: u64) -> u64 {
    kind + 16 * idx
}

/// `ZkFormal.NearV3.SrcpV3.{sz,gz}` (the last two columns).
const SZ: usize = 54;
const GZ: usize = 55;

// ---------------------------------------------------------------------------
// JSON mirrors (`ZkFormal.NearV3.{SrcpItem,SrcpB}`, `Rcpt/Extract/Srcp/Defs.lean`)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct SrcpItem {
    pub q: u64,
    pub dir: bool,
    pub sib: Vec<u64>,
    pub acc: Vec<u64>,
    pub pq: u64,
    pub pl: u64,
}

#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct SrcpB {
    pub j: u64,
    #[serde(rename = "L")]
    pub l: u64,
    pub dup: bool,
    pub root: Vec<u64>,
    pub qe: u64,
    pub le: u64,
    pub ql: u64,
    pub leaf: Vec<u64>,
    pub path: Vec<SrcpItem>,
}

// ---------------------------------------------------------------------------
// Frame (`SrcpGen.Frame` / `Frame.cell`)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, Default)]
struct Frame {
    rt: bool,
    sg: bool,
    lf: bool,
    wf: bool,
    wl: bool,
    wn: bool,
    sf: bool,
    sl: bool,
    pw: u64,
    q: u64,
    j: u64,
    l: u64,
    qe: u64,
    le: u64,
    dup: bool,
    dir: bool,
    aw: bool,
    pl: u64,
    b: u64,
    c_id: u64,
    c_len: u64,
    gd: bool,
    regs: Vec<u64>,
    sz: u64,
    gz: bool,
}

impl Frame {
    /// `Frame.cell`: the 56 cells of the row.
    fn cells(&self) -> [u64; SRCP_WIDTH] {
        let mut c = [0u64; SRCP_WIDTH];
        c[0] = b(self.rt);
        c[1] = b(self.sg);
        c[2] = b(self.lf);
        c[3] = b(self.wf);
        c[4] = b(self.wl);
        c[5] = b(self.wn);
        c[6] = b(self.sf);
        c[7] = b(self.sl);
        c[8] = self.pw;
        c[9] = self.q;
        c[10] = self.j;
        c[11] = self.l;
        c[12] = self.qe;
        c[13] = self.le;
        c[14] = b(self.dup);
        c[15] = b(self.dir);
        c[16] = b(self.aw);
        c[17] = self.pl;
        c[18] = self.b;
        c[19] = self.c_id;
        c[20] = self.c_len;
        c[21] = b(self.gd);
        for x in 0..32usize {
            c[22 + x] = get(&self.regs, x);
        }
        c[SZ] = self.sz;
        c[GZ] = b(self.gz);
        c
    }
}

/// `rootFrame B before`.
fn root_frame(e: &SrcpB, before: u64, gz: bool) -> Frame {
    Frame {
        rt: true,
        q: e.ql.saturating_sub(1),
        j: e.j,
        l: e.l,
        qe: e.qe,
        le: e.le,
        dup: e.dup,
        c_id: msg_id(K_SRC, e.qe),
        c_len: e.le,
        gd: true,
        regs: e.root.clone(),
        sz: before + e.l,
        gz,
        ..Frame::default()
    }
}

/// `leafFrame B before p`.
fn leaf_frame(e: &SrcpB, before: u64, p: u64, gz: bool) -> Frame {
    Frame {
        sg: true,
        lf: true,
        wf: p == 0,
        wl: p == 31,
        sf: p == 0,
        sl: p == 31,
        pw: p,
        q: e.ql,
        j: e.j,
        l: e.l,
        qe: e.qe,
        le: e.le,
        aw: true,
        b: get(&e.leaf, p as usize),
        c_id: msg_id(K_RC, e.j),
        c_len: e.l,
        gd: p == 0,
        regs: e.leaf.iter().skip(p as usize).copied().collect(),
        sz: before + e.l,
        gz,
        ..Frame::default()
    }
}

/// `pathFrame B before i o`.
fn path_frame(e: &SrcpB, before: u64, i: u64, o: u64, gz: bool) -> Frame {
    let it = e.path.get(i as usize).cloned().unwrap_or_default();
    let w = 32 <= o;
    let a = if it.dir { !w } else { w };
    let arm = if a { &it.acc } else { &it.sib };
    let pos = (o % 32) as usize;
    Frame {
        sg: true,
        wf: o % 32 == 0,
        wl: o % 32 == 31,
        wn: w,
        sf: o == 0,
        sl: o == 63,
        pw: o % 32,
        q: it.q,
        j: e.j,
        l: e.l,
        qe: e.qe,
        le: e.le,
        dir: it.dir,
        aw: a,
        pl: it.pl,
        b: get(arm, pos),
        c_id: msg_id(K_SRC, it.pq),
        c_len: it.pl,
        gd: o % 32 == 0 && a,
        regs: it.acc.iter().skip(pos).copied().collect(),
        sz: before + e.l + 33 * (i + 1),
        gz,
        ..Frame::default()
    }
}

/// `SrcpGen.R bs = (recs bs).length = Σ (33 + 64·|path|)`.
fn r_of(bs: &[SrcpB]) -> u64 {
    bs.iter().map(|e| 33 + 64 * e.path.len() as u64).sum()
}

/// `SrcpGen.cell bs pos x` at a row before `R bs` (the `Frame` of `recs[pos]`).
fn row_frame(e: &SrcpB, before: u64, kind: Kind, gz: bool) -> Frame {
    match kind {
        Kind::Root => root_frame(e, before, gz),
        Kind::Leaf(p) => leaf_frame(e, before, p, gz),
        Kind::Path(i, o) => path_frame(e, before, i, o, gz),
    }
}

/// `srcpSize bs = Σ (L + 33·|path|)` (the padding `sz` accumulator).
fn srcp_size(bs: &[SrcpB]) -> u64 {
    bs.iter().map(|e| e.l + 33 * e.path.len() as u64).sum()
}

/// `SrcpGen.Kind`.
#[derive(Clone, Copy, Debug)]
enum Kind {
    Root,
    Leaf(u64),
    Path(u64, u64),
}

/// Build the honest `srcpV3` trace at the aligned height.
pub fn srcp_aligned(bs: &[SrcpB]) -> Tab {
    let r = r_of(bs);
    let log = pad_log22(log_of(r as usize));
    let mut t = Tab::zero(log, SRCP_WIDTH);
    let h = t.height() as u64;
    let mut pos: u64 = 0;
    let mut before: u64 = 0;
    'blocks: for e in bs {
        let gz = |p: u64| p + 1 == r;
        // root row
        let f = row_frame(e, before, Kind::Root, gz(pos));
        if pos < h {
            for (c, x) in f.cells().into_iter().enumerate() {
                t.set(pos as usize, c, x);
            }
        }
        pos += 1;
        // 32 leaf rows
        for p in 0..32u64 {
            if pos >= h {
                break 'blocks;
            }
            let f = row_frame(e, before, Kind::Leaf(p), gz(pos));
            for (c, x) in f.cells().into_iter().enumerate() {
                t.set(pos as usize, c, x);
            }
            pos += 1;
        }
        // 64 rows per path item
        for i in 0..e.path.len() as u64 {
            for o in 0..64u64 {
                if pos >= h {
                    break 'blocks;
                }
                let f = row_frame(e, before, Kind::Path(i, o), gz(pos));
                for (c, x) in f.cells().into_iter().enumerate() {
                    t.set(pos as usize, c, x);
                }
                pos += 1;
            }
        }
        before += e.l + 33 * e.path.len() as u64;
    }
    // Padding: `cell bs pos x = if x = sz then srcpSize bs else 0`.
    let total: u64 = srcp_size(bs);
    for q in (pos as usize)..t.height() {
        t.set(q, SZ, total);
    }
    t
}

/// Parse `json` as `List SrcpB` and render the aligned trace.
pub fn render(json: &str) -> Result<Tab, String> {
    let bs: Vec<SrcpB> = serde_json::from_str(json).map_err(|e| e.to_string())?;
    Ok(srcp_aligned(&bs))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::v3::sample::Rng;

    #[test]
    fn root_and_leaf_rows() {
        let mut r = Rng::new(2);
        let bs = crate::v3::sample::srcp(&mut r, 2);
        let t = srcp_aligned(&bs);
        // first row is the root of block 0: rt = 1, j = 0, q = ql − 1
        assert_eq!(t.cells[0], 1);
        assert_eq!(t.cells[10], 0);
        assert_eq!(t.cells[9] as u64, bs[0].ql - 1);
        // the aligned height always fits the record count
        assert!(t.height() as u64 >= r_of(&bs));
    }
}
