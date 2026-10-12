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

use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};

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
    /// `UpsGen.rlen` (`Gen.lean:107`): `(part (nQ − 1)).q.length`.
    fn rlen(&self) -> usize {
        self.part(self.n_q().saturating_sub(1)).q.len()
    }
}

// ---------------------------------------------------------------------------
// Segment constants (`UpsGen.segCell`, `Gen.lean:131`)
// ---------------------------------------------------------------------------

/// `UpsGen.ind` (`Gen.lean:97`): the `0`/`1` indicator.
fn ind(p: bool) -> u64 {
    b(p)
}

/// `UpsGen.Lb` (`Gen.lean:112`): bytes of `L` (`L0 L1 L2`, then `0`).
fn l_b(i: &UpsInst, j: usize) -> u64 {
    let l = i.l() as u64;
    match j {
        0 => l % 256,
        1 => l / 256 % 256,
        2 => l / 65536,
        _ => 0,
    }
}

/// `UpsGen.cin` (`Gen.lean:116`): `Σ ind (ci = n)`.
fn cin(i: &UpsInst, ns: &[u64]) -> u64 {
    ns.iter().map(|&n| ind(i.ci == n)).sum()
}

/// `UpsGen.xbit` (`Gen.lean:117`).
fn xbit(i: &UpsInst, k: u32) -> u64 {
    i.x / 2u64.pow(k) % 2
}

/// `UpsGen.pxV` (`Gen.lean:118`): `2^(x mod 8)`.
fn px_v(i: &UpsInst) -> u64 {
    2u64.pow((i.x % 8) as u32)
}

/// `UpsGen.bmLV` (`Gen.lean:123`).
fn bm_l_v(i: &UpsInst) -> u64 {
    let sp_yc = cin(i, &[4, 6, 9, 10]);
    (1 - cin(i, &[4])) * (1 - xbit(i, 3)) * px_v(i) + sp_yc * ind(i.ts == 1)
}

/// `UpsGen.bmHV` (`Gen.lean:124`).
fn bm_h_v(i: &UpsInst) -> u64 {
    let sp_yc = cin(i, &[4, 6, 9, 10]);
    (1 - cin(i, &[4])) * xbit(i, 3) * px_v(i) + 128 * (sp_yc * (1 - ind(i.ts == 1)))
}

/// `UpsGen.presV` (`Gen.lean:125`).
fn pres_v(i: &UpsInst) -> u64 {
    ind(i.step(3).mode == 0)
}

/// `UpsGen.vidV` (`Gen.lean:126`).
fn vid_v(i: &UpsInst) -> u64 {
    ind(i.step(3).mode == 0) * get(&i.step(3).e, 3)
}

/// `UpsGen.isSeg` (`Gen.lean:129`).
pub fn is_seg(col: usize) -> bool {
    (10..49).contains(&col) || (176..179).contains(&col) || col == 186
}

/// `UpsGen.segCell` (`Gen.lean:131`): the segment-constant columns.
pub fn seg_cell(i: &UpsInst, col: usize) -> u64 {
    if col == 10 {
        i.tau
    } else if col < 14 {
        get(&i.n, col - 11)
    } else if col < 17 {
        l_b(i, col - 14)
    } else if col < 28 {
        ind(i.ci == (col - 17) as u64)
    } else if col < 31 {
        ind(i.d == (col - 28) as u64)
    } else if col < 34 {
        ind(i.ts == (col - 30) as u64)
    } else if col < 37 {
        ind(i.ti == (col - 34) as u64)
    } else if col == 37 {
        i.x
    } else if col < 42 {
        xbit(i, (col - 38) as u32)
    } else if col == 42 {
        px_v(i)
    } else if col == 43 {
        bm_l_v(i)
    } else if col == 44 {
        bm_h_v(i)
    } else if col == 45 {
        pres_v(i)
    } else if col == 46 {
        vid_v(i)
    } else if col == 47 {
        i.n_q() as u64
    } else if col == 48 {
        i.rlen() as u64
    } else if col < 179 {
        get(&i.dep, col - 176)
    } else {
        i.rid
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
// Walk rows `W0 … W3` (`UpsGen.wCell`, `Gen.lean:167`)
// ---------------------------------------------------------------------------

/// `UpsGen.wsym` (`Gen.lean:109`): `[START, 0, 15, END].getD t 0`.
fn wsym(t: usize) -> u64 {
    [SYM_START, 0, 15, SYM_END].get(t).copied().unwrap_or(0)
}

/// `UpsGen.ent` (`Gen.lean:154`): a step enters a new record (lands on position `0`).
fn ent(i: &UpsInst, t: usize) -> u64 {
    ind((t == 1 || t == 2) && i.step(t).mode == 0 && get(&i.step(t).e, 4) == 0)
}

/// `UpsGen.lv` (`Gen.lean:158`): the level of walk row `t ≥ 1`.
fn lv(i: &UpsInst, t: usize) -> u64 {
    (if t >= 2 { ent(i, 1) } else { 0 }) + (if t >= 3 { ent(i, 2) } else { 0 })
}

/// `UpsGen.invV` (`Gen.lean:160`): `(wsym − nib)⁻¹` in `Fp`.
fn inv_v(i: &UpsInst, t: usize) -> u64 {
    let d = crate::field::F::from_u64(wsym(t)) - crate::field::F::from_u64(get(&i.step(t).e, 2));
    d.try_inverse()
        .unwrap_or(crate::field::F::ZERO)
        .as_canonical_u32() as u64
}

/// `UpsGen.upsIdV` (`Gen.lean:115`): `12 + 16·(512·τ + x)`.
fn ups_id_v(i: &UpsInst, x: u64) -> u64 {
    12 + 16 * (512 * i.tau + x)
}

/// `UpsGen.wReg` (`Gen.lean:163`): the 32-byte `reg` of a walk row.
fn w_reg(i: &UpsInst, t: usize, m: usize) -> u64 {
    if t == 0 {
        get(&i.mid, m)
    } else if t == 3 {
        get(&i.post, m)
    } else if i.step(t).mode == 2 && m < 16 {
        i.step(t).bm / 2u64.pow(m as u32) % 2
    } else {
        0
    }
}

/// `UpsGen.wCell` (`Gen.lean:167`).
fn w_cell(i: &UpsInst, t: usize, col: usize) -> i64 {
    let s = i.step(t);
    let x: u64 = match col {
        0 | 1 => 1,
        4 => ind(t == 0),
        5 => ind(t == 1),
        6 => ind(t == 2),
        7 => ind(t == 3),
        49 => get(&s.e, 0),
        50 => get(&s.e, 1),
        51 => get(&s.e, 2),
        52 => get(&s.e, 3),
        53 => get(&s.e, 4),
        54 => get(&s.e, 5),
        55 => {
            if s.mode == 1 {
                inv_v(i, t)
            } else {
                0
            }
        }
        56 => {
            if s.mode == 2 {
                s.hv
            } else {
                0
            }
        }
        57 => {
            if s.mode == 2 {
                s.bm
            } else {
                0
            }
        }
        58 => ent(i, t),
        59 => ind(t != 0 && lv(i, t) == 0),
        60 => ind(t != 0 && lv(i, t) == 1),
        61 => ind(t != 0 && lv(i, t) == 2),
        62 => ind(t != 0 && t as u64 == i.ts),
        105 => s.u,
        124 => ind(t == 3),
        125 => {
            if t == 3 {
                ups_id_v(i, i.n_q() as u64)
            } else {
                0
            }
        }
        126 => {
            if t == 3 {
                i.rlen() as u64
            } else {
                0
            }
        }
        173 => ind(s.mode == 0),
        174 => ind(s.mode == 1),
        175 => ind(s.mode == 2),
        _ => {
            if (129..161).contains(&col) {
                w_reg(i, t, col - 129)
            } else {
                0
            }
        }
    };
    x as i64
}

// ---------------------------------------------------------------------------
// Value rows (`UpsGen.vCell`, `Gen.lean:200`)
// ---------------------------------------------------------------------------

/// `UpsGen.vCell` (`Gen.lean:200`).
fn v_cell(i: &UpsInst, p: usize, col: usize) -> i64 {
    let x: u64 = match col {
        0 | 2 => 1,
        8 => ind(p == 0),
        9 => ind(p + 1 == i.l()),
        65 => ind(i.d == 0),
        66 => ind(i.d == 1),
        67 => ind(i.d == 2),
        68 => get(&i.n, i.d as usize),
        100 => p as u64,
        101 => get(&i.v, p),
        181 => i.d,
        182 => get(&i.dep, i.d as usize),
        _ => 0,
    };
    x as i64
}

/// A cell value reduced into `Fp` (`Tab::set` does the final `mod P`).
fn set_i(t: &mut Tab, r: usize, c: usize, x: i64) {
    t.set(r, c, x.rem_euclid(crate::field::P as i64) as u64);
}

// ---------------------------------------------------------------------------
// Renderer
// ---------------------------------------------------------------------------

/// Build the honest `upsV3` trace (`UpsGen.cell`, `Gen.lean:564`).
pub fn ups_aligned(insts: &[UpsInst]) -> Tab {
    let recs = recs(insts);
    let log = pad_log22(log_of(recs.len() + 1));
    let mut t = Tab::zero(log, UPS_WIDTH);
    let h = t.height();
    for (q, &(i, rk)) in recs.iter().enumerate() {
        if q >= h {
            break;
        }
        let inst = &insts[i];
        for col in 0..UPS_WIDTH {
            if is_seg(col) {
                t.set(q, col, seg_cell(inst, col));
            } else {
                let x = match rk {
                    Rk::W(t) => w_cell(inst, t, col),
                    Rk::V(p) => v_cell(inst, p, col),
                    Rk::Q(_, _) => 0,
                };
                set_i(&mut t, q, col, x);
            }
        }
    }
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

    #[test]
    fn seg_constants_match_seg_cell() {
        let i = inst();
        let t = ups_aligned(std::slice::from_ref(&i));
        for col in 0..UPS_WIDTH {
            if is_seg(col) {
                assert_eq!(
                    t.cells[col] as u64,
                    seg_cell(&i, col) % crate::field::P as u64,
                    "col {col}"
                );
            }
        }
    }

    #[test]
    fn walk_rows_match_w_cell() {
        let mut i = inst();
        i.mid = vec![11; 32];
        i.post = vec![22; 32];
        let t = ups_aligned(std::slice::from_ref(&i));
        for trow in 0..4 {
            for col in 0..UPS_WIDTH {
                if is_seg(col) {
                    continue;
                }
                let want = (w_cell(&i, trow, col).rem_euclid(crate::field::P as i64)) as u32;
                assert_eq!(t.cells[trow * UPS_WIDTH + col], want, "W{trow} col {col}");
            }
        }
        // spot checks: W0 reg = mid, W3 reg = post, W3 digest id/length
        assert_eq!(t.cells[129] as u64, 11);
        assert_eq!(t.cells[3 * UPS_WIDTH + 129] as u64, 22);
        assert_eq!(
            t.cells[3 * UPS_WIDTH + 125] as u64,
            ups_id_v(&i, i.n_q() as u64)
        );
        assert_eq!(t.cells[3 * UPS_WIDTH + 126] as u64, i.rlen() as u64);
    }

    #[test]
    fn value_rows_match_v_cell() {
        let i = inst();
        let t = ups_aligned(std::slice::from_ref(&i));
        for p in 0..i.l() {
            let row = 4 + p;
            for col in 0..UPS_WIDTH {
                if is_seg(col) {
                    continue;
                }
                let want = (v_cell(&i, p, col).rem_euclid(crate::field::P as i64)) as u32;
                assert_eq!(t.cells[row * UPS_WIDTH + col], want, "V{p} col {col}");
            }
        }
        // V0: `D` selector and `N[D]`, position/byte columns.
        assert_eq!(t.cells[4 * UPS_WIDTH + 67] as u64, 1);
        assert_eq!(t.cells[4 * UPS_WIDTH + 68] as u64, 3);
        assert_eq!(t.cells[4 * UPS_WIDTH + 101] as u64, 7);
    }
}
