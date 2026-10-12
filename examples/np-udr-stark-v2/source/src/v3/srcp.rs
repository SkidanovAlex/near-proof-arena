//! Honest table-20 trace generator for `nearAirV3` (`SrcpDD.table`,
//! `zk-formal/ZkFormal/NearV3/Rcpt/Tables/SrcpDD.lean`), the Rust twin of the
//! Lean honest render `srcpDDTrace bs rep` (`Render/PaddedSrcpDD.lean`):
//!
//! * columns `0 … 56` are `DedupRender.cell bs rep`
//!   (`Rcpt/Candidates/DedupRender.lean`): a computed block (`dup = false`) is
//!   the `srcpV3` block of `Rcpt/Render/Srcp/Gen.lean` (root row, 32 leaf rows,
//!   64 rows per path item); a `dup` occurrence is a single reference root row
//!   (`qe = ql − 1`, `le = cId = cLen = gD = 0`) whose `sz` step is `L` only;
//!   column `56` carries the repetition bit `rep` of the block on root rows;
//! * columns `57 … 62` are the A10 depth slack bits `db_e` = bit `e` of
//!   `DP0 − |path|` on every root row (`SrcpDDGen.depthVal`);
//! * padding carries the final `sz` accumulator `DedupRender.size bs`.
//!
//! The height is `padLog22 (logOf (DedupRender.R bs))`.
//!
//! Input: the `List SrcpB` entries with the Lean field names plus the per-block
//! repetition bit `rep` (`Rcpt/Candidates/SourceRepetition.lean`
//! `sourceRepeated p.lists j` = `Public.sourceRep`, the key of source `j` occurs
//! at least twice; `AcceptedV3.ddRep`), which the completeness assembly passes as
//! the function `rep : Nat → Bool` indexed by block position.
//! `conformance/run-v2.d/rcs.sh` compares the dump with
//! `np-lean-render-v3-rcs` byte for byte.

use serde::Deserialize;

use super::{Tab, b, get, log_of, pad_log22};

/// `SrcpDD.width`: the 57 `DedupTable` columns plus 6 depth slack bits.
pub const SRCP_WIDTH: usize = 63;
/// `DedupRender.width` (the frame cells `0 … 55` and the repetition bit `56`).
const DD_WIDTH: usize = 57;
/// `DedupTable.repeated`.
const REPEATED: usize = 56;
/// `SrcpDD.db 0` (the six slack bits are `57 … 62`).
const DB0: usize = 57;
/// `SrcpV3.DP0` (`Rcpt/Tables/SrcpD.lean`), the A10 path-depth bound.
pub const DP0: u64 = 32;

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
    /// The all-occurrence repetition bit of this block's source key
    /// (`sourceRepeated p.lists j`, column `56` of its root row).  Not a Lean
    /// `SrcpB` field: the Lean render takes it as `rep : Nat → Bool` by block
    /// position.  Defaults to `false` for older entry files.
    #[serde(default)]
    pub rep: bool,
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
    /// `Frame.cell`: the 56 frame cells of the row (columns `56 …` are `0`).
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

/// `DedupRender.frame B before .root`: `rootFrame B before`, and for a `dup`
/// occurrence the reference header `{ qe := ql − 1, le := 0, cId := 0,
/// cLen := 0, gD := false }`.
fn root_frame(e: &SrcpB, before: u64, gz: bool) -> Frame {
    let f = root_frame_computed(e, before, gz);
    if e.dup {
        Frame {
            qe: e.ql.saturating_sub(1),
            le: 0,
            c_id: 0,
            c_len: 0,
            gd: false,
            ..f
        }
    } else {
        f
    }
}

/// `SrcpGen.rootFrame B before`.
fn root_frame_computed(e: &SrcpB, before: u64, gz: bool) -> Frame {
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

/// `DedupRender.payloadRows B`: no rows after a `dup` header.
fn payload_rows(e: &SrcpB) -> u64 {
    if e.dup {
        0
    } else {
        32 + 64 * e.path.len() as u64
    }
}

/// `DedupRender.R bs = Σ (1 + payloadRows B)`.
pub fn r_of(bs: &[SrcpB]) -> u64 {
    bs.iter().map(|e| 1 + payload_rows(e)).sum()
}

/// `DedupRender.sizeStep B = L + (if dup then 0 else 33·|path|)`.
fn size_step(e: &SrcpB) -> u64 {
    e.l + if e.dup { 0 } else { 33 * e.path.len() as u64 }
}

/// `SrcpGen.cell bs pos x` at a row before `R bs` (the `Frame` of `recs[pos]`).
fn row_frame(e: &SrcpB, before: u64, kind: Kind, gz: bool) -> Frame {
    match kind {
        Kind::Root => root_frame(e, before, gz),
        Kind::Leaf(p) => leaf_frame(e, before, p, gz),
        Kind::Path(i, o) => path_frame(e, before, i, o, gz),
    }
}

/// `DedupRender.size bs = Σ sizeStep` (the padding `sz` accumulator).
fn srcp_size(bs: &[SrcpB]) -> u64 {
    bs.iter().map(size_step).sum()
}

/// `SrcpGen.Kind`.
#[derive(Clone, Copy, Debug)]
enum Kind {
    Root,
    Leaf(u64),
    Path(u64, u64),
}

/// Write the cells of a root row: the frame, the repetition bit and the depth
/// slack bits of `DP0 − |path|` (`SrcpDDGen.cell`).
fn set_root(t: &mut Tab, pos: usize, e: &SrcpB, f: &Frame) {
    let mut c = f.cells();
    c[REPEATED] = b(e.rep);
    let d = DP0.saturating_sub(e.path.len() as u64);
    for k in 0..(SRCP_WIDTH - DB0) {
        c[DB0 + k] = (d >> k) & 1;
    }
    for (x, v) in c.into_iter().enumerate() {
        t.set(pos, x, v);
    }
}

/// Build the honest table-20 trace `srcpDDTrace bs rep` at the aligned height
/// `padLog22 (logOf (DedupRender.R bs))`.
pub fn srcp_aligned(bs: &[SrcpB]) -> Tab {
    debug_assert_eq!(DD_WIDTH, REPEATED + 1);
    let r = r_of(bs);
    let log = pad_log22(log_of(r as usize));
    let mut t = Tab::zero(log, SRCP_WIDTH);
    let h = t.height() as u64;
    let mut pos: u64 = 0;
    let mut before: u64 = 0;
    'blocks: for e in bs {
        let gz = |p: u64| p + 1 == r;
        if pos >= h {
            break;
        }
        // root row (the whole block for a `dup` occurrence)
        let f = row_frame(e, before, Kind::Root, gz(pos));
        set_root(&mut t, pos as usize, e, &f);
        pos += 1;
        if !e.dup {
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
        }
        before += size_step(e);
    }
    // Padding: `cell bs pos x = if x = sz then size bs else 0`.
    let total: u64 = srcp_size(bs);
    for q in (pos.min(h) as usize)..t.height() {
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

    #[test]
    fn dup_reference_rows_and_depth_bits() {
        let at = |t: &Tab, r: usize, c: usize| t.cells[r * SRCP_WIDTH + c] as u64;
        for seed in 1..40u64 {
            let mut r = Rng::new(seed);
            let bs = crate::v3::sample::srcp(&mut r, 9);
            let t = srcp_aligned(&bs);
            assert_eq!(t.width, SRCP_WIDTH);
            let mut pos = 0usize;
            for e in &bs {
                // root row: rt, dup, rep, depth slack bits
                assert_eq!(at(&t, pos, 0), 1);
                assert_eq!(at(&t, pos, 14), b(e.dup));
                assert_eq!(at(&t, pos, REPEATED), b(e.rep));
                let d: u64 = (0..6).map(|k| at(&t, pos, DB0 + k) << k).sum();
                assert_eq!(d, DP0 - e.path.len() as u64);
                if e.dup {
                    assert!(e.rep && e.l == 12);
                    assert_eq!(at(&t, pos, 12), e.ql - 1); // qe = ql − 1
                    assert_eq!(at(&t, pos, 21), 0); // gD
                }
                pos += 1 + payload_rows(e) as usize;
                // non-root rows carry no rep/depth bits
                for q in (pos - payload_rows(e) as usize)..pos {
                    for c in REPEATED..SRCP_WIDTH {
                        assert_eq!(at(&t, q, c), 0);
                    }
                }
            }
            assert_eq!(pos as u64, r_of(&bs));
            assert_eq!(at(&t, t.height() - 1, SZ), srcp_size(&bs));
        }
    }

    #[test]
    fn empty_is_log1_padding() {
        let t = srcp_aligned(&[]);
        assert_eq!(t.log, 1);
        assert!(t.cells.iter().all(|&x| x == 0));
    }
}
