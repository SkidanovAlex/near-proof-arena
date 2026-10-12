//! Honest `upsV3` trace generator for `nearAirV3` (table index 7), the Rust twin
//! of the Lean table generator `ZkFormal.NearV3.Render.UpsGen.cell`
//! (`Render/Ups/Gen.lean`).
//!
//! Input: a JSON list of `UpsInst` instance descriptions (Lean field names,
//! with nested `WStep3` walks and `UpsPartI` parts).  Output: the trace at the
//! aligned height `padLog22 (logOf (R + 1))` (`Render/Ups/Local.lean:81`),
//! width 200, every cell reduced mod `P` (`Tab::set`).
//!
//! Row order per instance `τ`: `W0 W1 W2 W3`, the value rows `0 … L−1`, then
//! the parts' rows (`RecsI`).  `UPB` use counts `u` are global: the number of
//! earlier reads of the same `(sN, spos)` in table order (`Gen.lean:549`).

use serde::Deserialize;

use super::{Tab, b, get, log_of, pad_log22};

/// `UpsV3.width` (`Tables/Ups.lean:...`).
pub const UPS_WIDTH: usize = 200;

/// `ZkFormal.Near.SYM_START`, `SYM_END` (`Near/Ids.lean:49,53`).
const SYM_START: u64 = 18;
const SYM_END: u64 = 16;

// ---------------------------------------------------------------------------
// JSON mirrors (`UpsInst`, `UpsPartI`, `WStep3`)
// ---------------------------------------------------------------------------

/// One part (new node `Q_{k+1}`) of an instance (`Gen.lean:44`).
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct UpsPartI {
    /// kind index (`UKind` order: `RDB RDE RLP RBR RBV RBI MVL MVE NLF WEX SPB PT`).
    pub kind: u64,
    pub sd: u64,
    #[serde(rename = "sN")]
    pub s_n: u64,
    pub pdep: u64,
    pub rc: u64,
    #[serde(rename = "cN")]
    pub c_n: u64,
    /// the source record's post bytes and `cid` column.
    pub pb: Vec<u64>,
    pub pcid: Vec<u64>,
    /// node type of `Q`: `0` leaf, `1` extension, `2` branch, `3` branch with value.
    pub ty: u64,
    pub qhk: u64,
    pub qodd: u64,
    pub phk: u64,
    pub podd: u64,
    pub nochild: u64,
    /// fields `(state, length)`, states `TAG HPL HPF KEY VLEN VH BM CH MEM` = `0 … 8`.
    pub shape: Vec<(u64, u64)>,
    /// the bytes of `Q`.
    pub q: Vec<u64>,
    pub jm: u64,
    pub clen: u64,
    /// `MEMD` value: the child's exact new `memory_usage`.
    #[serde(rename = "mB")]
    pub m_b: u64,
    /// offset of the source's value length (`SR`).
    pub soff: u64,
    pub neg: u64,
}

/// One instance `τ` of the upsert (`Gen.lean:76`).
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct UpsInst {
    pub tau: u64,
    pub rid: u64,
    #[serde(rename = "N")]
    pub n: Vec<u64>,
    pub dep: Vec<u64>,
    pub walk: Vec<super::WStep3>,
    /// case index (`UCase` order: `LP BR BV BI LSa LSb LSc ESl0 ESl1 ESn0 ESn1`).
    pub ci: u64,
    #[serde(rename = "D")]
    pub d: u64,
    pub ts: u64,
    pub ti: u64,
    pub x: u64,
    pub v: Vec<u64>,
    pub mid: Vec<u64>,
    pub post: Vec<u64>,
    pub parts: Vec<UpsPartI>,
}

impl UpsInst {
    /// `UpsGen.L` (`Gen.lean:104`).
    pub fn l(&self) -> usize {
        self.v.len()
    }
    /// `UpsGen.nQ` (`Gen.lean:105`).
    pub fn n_q(&self) -> usize {
        self.parts.len()
    }
    /// `UpsGen.part` (`Gen.lean:106`): `parts.getD k default`.
    pub fn part(&self, k: usize) -> &UpsPartI {
        self.parts.get(k).unwrap_or(&DEFAULT_PART)
    }
    /// `UpsGen.step` (`Gen.lean:108`): `walk.getD t default`.
    fn step(&self, t: usize) -> &super::WStep3 {
        self.walk.get(t).unwrap_or(&DEFAULT_STEP)
    }
}

static DEFAULT_PART: UpsPartI = UpsPartI {
    kind: 0,
    sd: 0,
    s_n: 0,
    pdep: 0,
    rc: 0,
    c_n: 0,
    pb: Vec::new(),
    pcid: Vec::new(),
    ty: 0,
    qhk: 0,
    qodd: 0,
    phk: 0,
    podd: 0,
    nochild: 0,
    shape: Vec::new(),
    q: Vec::new(),
    jm: 0,
    clen: 0,
    m_b: 0,
    soff: 0,
    neg: 0,
};
static DEFAULT_STEP: super::WStep3 = super::WStep3 {
    mode: 0,
    sym: 0,
    e: Vec::new(),
    u: 0,
    bm: 0,
    hv: 0,
    ub: 0,
};

// ---------------------------------------------------------------------------
// Row enumeration (`RK`, `recsI`, `recs`, `R`)
// ---------------------------------------------------------------------------

/// A row of an instance: walk row `t`, value row `p`, row `p` of part `k`
/// (`Gen.lean:523`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rk {
    W(usize),
    V(usize),
    Q(usize, usize),
}

/// `UpsGen.recsI` (`Gen.lean:529`).
fn recs_i(i: &UpsInst) -> Vec<Rk> {
    let mut o = Vec::new();
    for t in 0..4 {
        o.push(Rk::W(t));
    }
    for p in 0..i.l() {
        o.push(Rk::V(p));
    }
    for k in 0..i.n_q() {
        for p in 0..i.part(k).q.len() {
            o.push(Rk::Q(k, p));
        }
    }
    o
}

/// `UpsGen.recs` (`Gen.lean:534`): all rows as `(instance, row)`.
fn recs(insts: &[UpsInst]) -> Vec<(usize, Rk)> {
    let mut o = Vec::new();
    for (i, inst) in insts.iter().enumerate() {
        for rk in recs_i(inst) {
            o.push((i, rk));
        }
    }
    o
}

/// `UpsGen.R` (`Gen.lean:561`): the number of active rows.
pub fn r(insts: &[UpsInst]) -> usize {
    recs(insts).len()
}

// ---------------------------------------------------------------------------
// Renderer
// ---------------------------------------------------------------------------

/// Build the honest `upsV3` trace (`UpsGen.cell`, `Gen.lean:564`).
pub fn ups_aligned(insts: &[UpsInst]) -> Tab {
    let log = pad_log22(log_of(r(insts) + 1));
    let t = Tab::zero(log, UPS_WIDTH);
    let _ = (SYM_START, SYM_END, b, get, insts);
    t
}

/// Parse `json` as a `List UpsInst` and render its aligned trace.
pub fn render(json: &str) -> Result<Tab, String> {
    let insts: Vec<UpsInst> = serde_json::from_str(json).map_err(|e| e.to_string())?;
    Ok(ups_aligned(&insts))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn inst() -> UpsInst {
        UpsInst {
            tau: 3,
            rid: 9,
            n: vec![1, 2, 3],
            dep: vec![0, 1, 2],
            walk: vec![Default::default(); 4],
            ci: 0,
            d: 2,
            ts: 3,
            ti: 0,
            x: 0,
            v: vec![7, 8],
            mid: vec![0; 32],
            post: vec![0; 32],
            parts: vec![
                UpsPartI {
                    kind: 2,
                    q: vec![1, 2, 3],
                    shape: vec![(0, 1)],
                    ..Default::default()
                },
                UpsPartI {
                    kind: 3,
                    q: vec![4, 5],
                    shape: vec![(0, 1)],
                    ..Default::default()
                },
            ],
        }
    }

    #[test]
    fn height_and_width() {
        let i = inst();
        let t = ups_aligned(std::slice::from_ref(&i));
        assert_eq!(t.width, UPS_WIDTH);
        // 4 walk rows + L value rows + Σ part byte lengths
        let rows = 4 + i.l() + 3 + 2;
        assert_eq!(r(std::slice::from_ref(&i)), rows);
        assert_eq!(t.log, pad_log22(log_of(rows + 1)));
        assert_eq!(t.height(), 1 << pad_log22(log_of(rows + 1)));
    }
}
