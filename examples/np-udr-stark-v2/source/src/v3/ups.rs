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
//!
//! `nearAirV3` table 7 is the A7 extension `upsA7` (`Tables/UnfoldA7.lean`):
//! [`ups_a7`] / [`render`] append `s` (200) and `nD` (201); no new inputs.
//! `conformance/run-v2.d/a7.sh` compares with `np-lean-render-v3-a7 ups` on
//! shape-valid (not honest) sampled instances.

use serde::Deserialize;

use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};

use super::{b, get, log_of, pad_log22, Tab};

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
// Part constants (`UpsGen.pcCell`, `Gen.lean:255`)
// ---------------------------------------------------------------------------

/// `UpsGen.kin` (`Gen.lean:223`): `Σ ind (kind = n)`.
fn kin(p: &UpsPartI, ns: &[u64]) -> u64 {
    ns.iter().map(|&n| ind(p.kind == n)).sum()
}

/// `UpsGen.XcpB` (`Gen.lean:224`): `kind == 10 && (ci == 8 || ci == 10)`.
fn x_cp_b(i: &UpsInst, p: &UpsPartI) -> bool {
    p.kind == 10 && (i.ci == 8 || i.ci == 10)
}

/// `UpsGen.xcpV` (`Gen.lean:225`).
fn x_cp_v(i: &UpsInst, p: &UpsPartI) -> u64 {
    ind(x_cp_b(i, p))
}

/// `UpsGen.useAV` (`Gen.lean:226`).
fn use_a_v(i: &UpsInst, p: &UpsPartI) -> u64 {
    kin(p, &[0, 1, 3, 4, 5, 7, 11]) + x_cp_v(i, p)
}

/// `UpsGen.spRecv` (`Gen.lean:122`).
fn sp_recv(i: &UpsInst) -> u64 {
    cin(i, &[5, 6, 7, 9])
}

/// `UpsGen.bNV` (`Gen.lean:227`).
fn b_n_v(i: &UpsInst, p: &UpsPartI) -> u64 {
    kin(p, &[0, 1, 9, 11]) + kin(p, &[10]) * sp_recv(i)
}

/// `UpsGen.bLV` (`Gen.lean:228`).
fn b_l_v(p: &UpsPartI) -> u64 {
    kin(p, &[3])
}

/// `UpsGen.cOV` (`Gen.lean:229`).
fn c_o_v(p: &UpsPartI) -> u64 {
    kin(p, &[0, 1, 11])
}

/// `UpsGen.cSV` (`Gen.lean:230`).
fn c_s_v(p: &UpsPartI) -> u64 {
    kin(p, &[3])
}

/// `UpsGen.CcV` (`Gen.lean:231`).
fn cc_v(i: &UpsInst, p: &UpsPartI) -> u64 {
    (kin(p, &[7]) + x_cp_v(i, p)) * (50 + 2 * p.phk)
}

/// `UpsGen.eLV` (`Gen.lean:232`).
fn e_l_v(p: &UpsPartI) -> u64 {
    kin(p, &[2, 4, 5, 8, 10])
}

/// `UpsGen.eSV` (`Gen.lean:233`).
fn e_s_v(i: &UpsInst, p: &UpsPartI) -> u64 {
    kin(p, &[6]) + kin(p, &[10]) * cin(i, &[4])
}

/// `UpsGen.KcV` (`Gen.lean:234`).
fn kc_v(i: &UpsInst, p: &UpsPartI) -> u64 {
    kin(p, &[2]) * (100 + 2 * p.qhk)
        + 50 * kin(p, &[4])
        + 102 * kin(p, &[5])
        + kin(p, &[6]) * (100 + 2 * p.qhk)
        + kin(p, &[7]) * (50 + 2 * p.qhk)
        + 102 * kin(p, &[8])
        + kin(p, &[9]) * (50 + 2 * p.qhk)
        + kin(p, &[10])
            * (202 * cin(i, &[4]) + 100 * cin(i, &[5, 7, 8]) + 152 * cin(i, &[6, 9, 10]))
}

/// `UpsGen.vcpV` (`Gen.lean:239`).
fn vcp_v(i: &UpsInst, p: &UpsPartI) -> u64 {
    kin(p, &[0, 5, 6]) + kin(p, &[10]) * cin(i, &[4])
}

/// `UpsGen.ba0V` (`Gen.lean:240`).
fn ba0_v(i: &UpsInst, p: &UpsPartI) -> u64 {
    ind(p.kind == 5 && i.ts == 1)
}

/// `UpsGen.ba1V` (`Gen.lean:241`).
fn ba1_v(i: &UpsInst, p: &UpsPartI) -> u64 {
    128 * ind(p.kind == 5 && i.ts != 1)
}

/// `UpsGen.Spy1B` (`Gen.lean:242`).
fn spy1_b(i: &UpsInst, p: &UpsPartI) -> bool {
    p.kind == 10 && (i.ci == 4 || (i.ts == 1 && (i.ci == 6 || i.ci == 9 || i.ci == 10)))
}

/// `UpsGen.Spy2B` (`Gen.lean:243`).
fn spy2_b(i: &UpsInst, p: &UpsPartI) -> bool {
    p.kind == 10 && i.ts != 1 && (i.ci == 6 || i.ci == 9 || i.ci == 10)
}

/// `UpsGen.spY1V` (`Gen.lean:244`).
fn sp_y1_v(i: &UpsInst, p: &UpsPartI) -> u64 {
    ind(spy1_b(i, p))
}

/// `UpsGen.spY2V` (`Gen.lean:245`).
fn sp_y2_v(i: &UpsInst, p: &UpsPartI) -> u64 {
    ind(spy2_b(i, p))
}

/// `UpsGen.S15B` (`Gen.lean:247`): target slot 15 (last window).
fn s15_b(i: &UpsInst, p: &UpsPartI) -> bool {
    (p.kind == 0 && p.sd == 1) || (p.kind == 5 && i.ts != 1)
}

/// `UpsGen.upV` (`Gen.lean:249`).
fn up_v(p: &UpsPartI) -> u64 {
    kin(p, &[0, 1, 11])
}

/// `UpsGen.nokeyV` (`Gen.lean:250`).
fn nokey_v(p: &UpsPartI) -> u64 {
    ind(p.ty <= 1 && p.qhk == 1)
}

/// `UpsGen.isPC` (`Gen.lean:253`).
pub fn is_pc(col: usize) -> bool {
    (49..100).contains(&col) || (179..184).contains(&col)
}

/// `UpsGen.pcCell` (`Gen.lean:255`): the part-constant columns.
pub fn pc_cell(i: &UpsInst, p: &UpsPartI, k: usize, col: usize) -> u64 {
    if col == 49 {
        (k + 1) as u64
    } else if col < 61 {
        ind(p.kind == (col - 50) as u64)
    } else if col < 65 {
        ind((k + 1) as u64 == (col - 60) as u64)
    } else if col < 68 {
        ind(p.sd == (col - 65) as u64)
    } else {
        match col {
            68 => p.s_n,
            69 => p.pb.len() as u64,
            70 => ind(p.ty == 0),
            71 => ind(p.ty == 1),
            72 => ind(p.ty == 2),
            73 => ind(p.ty == 3),
            74 => p.qhk,
            75 => p.qodd,
            76 => nokey_v(p),
            77 => p.nochild,
            78 => p.q.len() as u64,
            79 => ind((k + 1) as u64 == i.n_q() as u64),
            80 => p.jm,
            81 => p.clen,
            82 => kc_v(i, p),
            83 => e_l_v(p),
            84 => e_s_v(i, p),
            85 => use_a_v(i, p),
            86 => b_n_v(i, p),
            87 => b_l_v(p),
            88 => c_o_v(p),
            89 => c_s_v(p),
            90 => cc_v(i, p),
            91 => p.neg,
            92 => p.phk,
            93 => p.podd,
            94 => vcp_v(i, p),
            95 => x_cp_v(i, p),
            96 => ba0_v(i, p),
            97 => ba1_v(i, p),
            98 => sp_y1_v(i, p),
            99 => sp_y2_v(i, p),
            179 => ind(p.kind == 11),
            180 => up_v(p),
            181 => p.rc,
            182 => p.pdep,
            183 => p.c_n,
            _ => 0,
        }
    }
}

// ---------------------------------------------------------------------------
// Node-row predicates (`Gen.lean:302 …`)
// ---------------------------------------------------------------------------

/// `UpsGen.fieldAt` (`Gen.lean:305`): `(state, index, field length, windows before)`.
fn field_at(shape: &[(u64, u64)], p: usize) -> (u64, usize, u64, usize) {
    fn go(shape: &[(u64, u64)], p: usize, before: usize) -> (u64, usize, u64, usize) {
        match shape.split_first() {
            None => (9, 0, 0, before),
            Some(((s, l), rest)) => {
                if (p as u64) < *l {
                    (*s, p, *l, before)
                } else {
                    let extra = if *s == 7 { 1 } else { 0 };
                    go(rest, p - *l as usize, before + extra)
                }
            }
        }
    }
    go(shape, p, 0)
}

/// `UpsGen.nWin` (`Gen.lean:313`).
fn n_win(shape: &[(u64, u64)]) -> usize {
    shape.iter().filter(|f| f.0 == 7).count()
}

/// Field `p` of part `P` as `(st, ix, fl, wi)`.
fn fa(i: &UpsInst, k: usize, p: usize) -> (u64, usize, u64, usize) {
    field_at(&i.part(k).shape, p)
}

/// `Gen.lean:318`: `st == 7 && wi == 0`.
fn fw_b(st: u64, wi: usize) -> bool {
    st == 7 && wi == 0
}
/// `Gen.lean:319`.
fn lastw_b(p: &UpsPartI, st: u64, wi: usize) -> bool {
    st == 7 && wi + 1 == n_win(&p.shape)
}
/// `Gen.lean:320`.
fn tgt_b(i: &UpsInst, p: &UpsPartI, st: u64, wi: usize) -> bool {
    st == 7 && ((fw_b(st, wi) && !s15_b(i, p)) || (lastw_b(p, st, wi) && s15_b(i, p)))
}
/// `Gen.lean:321`.
fn wy_b(i: &UpsInst, p: &UpsPartI, st: u64, wi: usize) -> bool {
    st == 7 && p.kind == 10 && ((fw_b(st, wi) && spy1_b(i, p)) || (!fw_b(st, wi) && spy2_b(i, p)))
}
/// `Gen.lean:322`.
fn wfr_b(i: &UpsInst, p: &UpsPartI, st: u64, wi: usize) -> bool {
    st == 7
        && (((p.kind == 0 || p.kind == 5) && tgt_b(i, p, st, wi))
            || (p.kind == 1 || p.kind == 9 || p.kind == 11)
            || (p.kind == 10 && (wy_b(i, p, st, wi) || !x_cp_b(i, p))))
}
/// `Gen.lean:325`.
fn wn_b(i: &UpsInst, p: &UpsPartI, st: u64, wi: usize) -> bool {
    st == 7 && ((p.kind == 5 && tgt_b(i, p, st, wi)) || (p.kind == 10 && wy_b(i, p, st, wi)))
}
/// `Gen.lean:326`.
fn vcp_b(i: &UpsInst, p: &UpsPartI) -> bool {
    p.kind == 0 || p.kind == 5 || p.kind == 6 || (p.kind == 10 && i.ci == 4)
}
/// `Gen.lean:328`: the byte is copied from the source.
fn cp_b(i: &UpsInst, p: &UpsPartI, st: u64, wi: usize) -> bool {
    (st == 0 && matches!(p.kind, 0 | 1 | 2 | 3 | 5 | 11))
        || ((st == 1 || st == 2) && (p.kind == 1 || p.kind == 2 || p.kind == 11))
        || (st == 3 && (p.kind == 1 || p.kind == 2 || p.kind == 6 || p.kind == 7))
        || ((st == 4 || st == 5) && vcp_b(i, p))
        || (st == 6 && (p.kind == 0 || p.kind == 3 || p.kind == 4 || p.kind == 5))
        || (st == 7 && !wfr_b(i, p, st, wi))
}
/// `Gen.lean:336`: the row reads its target window's child id.
fn rdc_b(i: &UpsInst, p: &UpsPartI, st: u64, ix: usize, wi: usize) -> bool {
    st == 7 && ix == 0 && tgt_b(i, p, st, wi) && (p.kind == 0 || p.kind == 1 || p.kind == 11)
}
/// `Gen.lean:338`: header / old-value / old-memory reads.
fn extra_b(i: &UpsInst, p: &UpsPartI, st: u64, ix: usize, wi: usize) -> bool {
    (st == 0 && (p.kind == 4 || p.kind == 6 || p.kind == 7 || x_cp_b(i, p)))
        || (st == 1 && ix == 0 && (p.kind == 6 || p.kind == 7))
        || (st == 2 && (p.kind == 6 || p.kind == 7))
        || (st == 4 && p.kind == 3)
        || (st == 6 && ix == 0 && x_cp_b(i, p))
        || (st == 8 && p.kind != 8)
        || rdc_b(i, p, st, ix, wi)
}
/// `Gen.lean:342`.
fn aft_b(i: &UpsInst, p: &UpsPartI, st: u64, wi: usize) -> bool {
    (p.kind == 4 && (st == 6 || st == 7 || st == 8))
        || (p.kind == 5 && ((st == 7 && !fw_b(st, wi) && i.ts == 1) || st == 8))
}
/// `Gen.lean:344`.
fn win_fr_b(i: &UpsInst, p: &UpsPartI, st: u64, wi: usize) -> bool {
    (st == 5 && !cp_b(i, p, st, wi)) || (st == 7 && wfr_b(i, p, st, wi))
}
/// `Gen.lean:345`.
fn gd_b(i: &UpsInst, p: &UpsPartI, st: u64, ix: usize, wi: usize) -> bool {
    ix == 0 && win_fr_b(i, p, st, wi)
}

/// `Gen.lean:360`: the read position.
fn spos_v(i: &UpsInst, p: &UpsPartI, st: u64, ix: usize, wi: usize, px: usize) -> i64 {
    let aft = ind(aft_b(i, p, st, wi)) as i64;
    let plen = p.pb.len() as i64;
    if st == 8 {
        plen - 8 + ix as i64
    } else if [0, 1, 2, 3, 11].contains(&p.kind) {
        px as i64
    } else if p.kind == 4 {
        px as i64 - 36 * aft
    } else if p.kind == 5 {
        px as i64 - 32 * aft
    } else if p.kind == 6 || p.kind == 7 {
        if st == 0 {
            5
        } else if st == 1 {
            1
        } else {
            px as i64 + p.phk as i64 - p.qhk as i64
        }
    } else if p.kind == 10 {
        if st == 0 {
            5
        } else if st == 6 {
            1
        } else if st == 4 || st == 5 {
            plen - 45 + px as i64
        } else if st == 7 {
            plen - 40 + ix as i64
        } else {
            0
        }
    } else {
        0
    }
}

/// `UpsGen.rbV` (`Gen.lean:373`): the source byte at `spos`.
fn rb_v(i: &UpsInst, p: &UpsPartI, st: u64, ix: usize, wi: usize, px: usize) -> u64 {
    // `(sposV …).toNat`: a negative position reads index 0 (as in Lean)
    get(&p.pb, spos_v(i, p, st, ix, wi, px).max(0) as usize)
}

/// `Gen.lean:379`: the digest lookup's id.
fn di_v(i: &UpsInst, p: &UpsPartI, st: u64, ix: usize, wi: usize, k: usize) -> u64 {
    if gd_b(i, p, st, ix, wi) {
        if st == 5 {
            ups_id_v(i, 0)
        } else if wn_b(i, p, st, wi) {
            ups_id_v(i, k as u64)
        } else {
            ups_id_v(i, p.jm)
        }
    } else {
        0
    }
}

/// `Gen.lean:383`: the digest lookup's length.
fn dl_v(i: &UpsInst, p: &UpsPartI, st: u64, ix: usize, wi: usize) -> u64 {
    if gd_b(i, p, st, ix, wi) {
        if st == 5 {
            i.l() as u64
        } else if wn_b(i, p, st, wi) {
            50
        } else {
            p.clen
        }
    } else {
        0
    }
}

// ---------------------------------------------------------------------------
// `memory_usage` (`Gen.lean:390`)
// ---------------------------------------------------------------------------

/// `UpsGen.limb` (`Gen.lean:404`): limb `i` of an exact value.  `i128` mirrors
/// Lean's unbounded `Int` (the chain's intermediates exceed `i64`); `emod` is
/// the non-negative `rem_euclid`.
fn limb(r: i128, i: usize) -> i128 {
    if i < 7 {
        r.div_euclid(256i128.pow(i as u32)).rem_euclid(256)
    } else {
        r.div_euclid(256i128.pow(7))
    }
}

/// `Σ_{l < n} f l · 256^l` (`Gen.lean:415`).
fn pfx(f: &dyn Fn(usize) -> i128, n: usize) -> i128 {
    let mut acc = 0i128;
    for l in 0..n {
        acc += f(l) * 256i128.pow(l as u32);
    }
    acc
}

/// The per-part `memory_usage` arithmetic (`Gen.lean:395 …`).
struct Mem<'a> {
    i: &'a UpsInst,
    p: &'a UpsPartI,
}

impl Mem<'_> {
    fn mem_byte(&self, q: &UpsPartI, i: usize) -> i128 {
        // `Gen.lean:398` `memRb`: `((pb.length : Int) - 8 + i).toNat`.
        let idx = (q.pb.len() as i64 - 8 + i as i64).max(0) as usize;
        get(&q.pb, idx) as i128
    }
    fn child(&self) -> &UpsPartI {
        self.i.part(self.p.jm.saturating_sub(1) as usize)
    }
    fn slb(&self, i: usize) -> i128 {
        if i < 4 {
            get(&self.p.pb, self.p.soff as usize + i) as i128
        } else {
            0
        }
    }
    fn a(&self, i: usize) -> i128 {
        use_a_v(self.i, self.p) as i128 * self.rb(i)
    }
    fn b(&self, i: usize) -> i128 {
        b_n_v(self.i, self.p) as i128 * limb(self.p.m_b as i128, i)
            + b_l_v(self.p) as i128 * l_b(self.i, i) as i128
    }
    fn c(&self, i: usize) -> i128 {
        c_o_v(self.p) as i128 * self.mem_byte(self.child(), i)
            + c_s_v(self.p) as i128 * self.slb(i)
            + ind(i == 0) as i128 * cc_v(self.i, self.p) as i128
    }
    fn x1(&self, i: usize) -> i128 {
        self.a(i) + self.b(i) - self.c(i)
    }
    fn ein(&self, i: usize) -> i128 {
        ind(i == 0) as i128 * kc_v(self.i, self.p) as i128
            + e_l_v(self.p) as i128 * l_b(self.i, i) as i128
            + e_s_v(self.i, self.p) as i128 * self.slb(i)
    }
    fn rb(&self, i: usize) -> i128 {
        get(
            &self.p.pb,
            ((self.p.pb.len() as i128 - 8 + i as i128).max(0)) as usize,
        ) as i128
    }
    fn sig(&self) -> i128 {
        1 - 2 * self.p.neg as i128
    }
    fn tv(&self) -> i128 {
        self.sig() * pfx(&|l| self.x1(l), 8)
    }
    fn t(&self, i: usize) -> i128 {
        self.tv().div_euclid(256i128.pow(i as u32)).rem_euclid(256)
    }
    fn rv(&self) -> i128 {
        pfx(&|l| self.ein(l), 8) + (1 - self.p.neg as i128) * self.tv()
    }
    fn co(&self, i: usize) -> i128 {
        (self.sig() * pfx(&|l| self.x1(l), i + 1)
            - self.tv().rem_euclid(256i128.pow((i + 1) as u32)))
        .div_euclid(256i128.pow((i + 1) as u32))
    }
    fn co2(&self, i: usize) -> i128 {
        let f = |l: usize| self.ein(l) + (1 - self.p.neg as i128) * self.t(l);
        (pfx(&f, i + 1) - self.rv().rem_euclid(256i128.pow((i + 1) as u32)))
            .div_euclid(256i128.pow((i + 1) as u32))
    }
    fn cb(&self, i: usize) -> i128 {
        self.co(i) + if i < 7 { 65536 } else { 0 }
    }
    /// `UpsGen.memReg` (`Gen.lean:430`).
    fn mem_reg(&self, i: usize, m: usize) -> i128 {
        if m < 8 {
            self.t(i).div_euclid(2i128.pow(m as u32)).rem_euclid(2)
        } else if m < 11 {
            self.cb(i)
                .div_euclid(2i128.pow((m - 8) as u32))
                .rem_euclid(2)
        } else if m < 14 {
            self.co2(i)
                .div_euclid(2i128.pow((m - 11) as u32))
                .rem_euclid(2)
        } else if m == 14 {
            if i == 0 {
                0
            } else {
                self.co(i - 1)
            }
        } else if m == 15 {
            if i == 0 {
                0
            } else {
                self.co2(i - 1)
            }
        } else if m == 16 {
            self.x1(i)
        } else if m == 17 {
            self.ein(i)
        } else if m < 32 {
            self.cb(i)
                .div_euclid(2i128.pow((m - 15) as u32))
                .rem_euclid(2)
        } else {
            0
        }
    }
}

// ---------------------------------------------------------------------------
// `qRow` (`Gen.lean:450`)
// ---------------------------------------------------------------------------

/// `u32Bytes P.qhk` (`Spec/U32Bytes.lean:9`).
fn u32_bytes(n: u64) -> [u64; 4] {
    [
        n % 256,
        (n / 256) % 256,
        (n / 65536) % 256,
        (n / 16777216) % 256,
    ]
}

/// `le256` of a digit list (`Near/Extract/Segments.lean:202`, wrapped to `u64`).
fn le256(xs: &[u64]) -> u64 {
    let mut a: u64 = 0;
    for &x in xs.iter().rev() {
        a = a.wrapping_mul(256).wrapping_add(x);
    }
    a
}

/// `UpsGen.qRow` (`Gen.lean:450`): the cells of row `px` of part `k` (source
/// `P`) in field `st` at index `ix` of length `fl`, after `wi` windows, use
/// count `u`.
#[allow(clippy::too_many_arguments)]
fn q_row(
    i: &UpsInst,
    p: &UpsPartI,
    k: usize,
    px: usize,
    st: u64,
    ix: usize,
    fl: u64,
    wi: usize,
    u: u64,
    col: usize,
) -> i64 {
    let rd = ind(cp_b(i, p, st, wi) || extra_b(i, p, st, ix, wi)) as i64;
    match col {
        0 | 3 => 1,
        8 => ind(px == 0) as i64,
        9 => ind(px + 1 == p.q.len()) as i64,
        100 => px as i64,
        101 => get(&p.q, px) as i64,
        102 => rd,
        103 => rb_v(i, p, st, ix, wi, px) as i64,
        104 => spos_v(i, p, st, ix, wi, px),
        105 => {
            if cp_b(i, p, st, wi) || extra_b(i, p, st, ix, wi) {
                u as i64
            } else {
                0
            }
        }
        115 => ind(ix == 0) as i64,
        116 => ind(ix as u64 + 1 == fl) as i64,
        117 => ix as i64,
        118 => ind(fw_b(st, wi)) as i64,
        119 => ind(lastw_b(p, st, wi)) as i64,
        120 => ind(wfr_b(i, p, st, wi)) as i64,
        121 => ind(tgt_b(i, p, st, wi)) as i64,
        122 => ind(wy_b(i, p, st, wi)) as i64,
        123 => ind(wn_b(i, p, st, wi)) as i64,
        124 => ind(gd_b(i, p, st, ix, wi)) as i64,
        125 => di_v(i, p, st, ix, wi, k) as i64,
        126 => dl_v(i, p, st, ix, wi) as i64,
        127 => ind(cp_b(i, p, st, wi)) as i64,
        128 => ind(aft_b(i, p, st, wi)) as i64,
        168 => ind(st == 8 && (k + 1) as u64 != i.n_q() as u64 && p.kind != 8) as i64,
        169 => ind(st == 8
            && ([0, 1, 9, 11].contains(&p.kind) || (p.kind == 10 && [5, 6, 7, 9].contains(&i.ci))))
            as i64,
        170 => {
            if st == 8 {
                limb(Mem { i, p }.rv(), ix) as i64
            } else {
                0
            }
        }
        171 => {
            if st == 8 {
                limb(p.m_b as i128, ix) as i64
            } else {
                0
            }
        }
        172 => {
            if st == 8 {
                Mem { i, p }.mem_byte(Mem { i, p }.child(), ix) as i64
            } else {
                0
            }
        }
        184 => get(&p.pcid, spos_v(i, p, st, ix, wi, px).max(0) as usize) as i64,
        185 => ind(rdc_b(i, p, st, ix, wi)) as i64,
        _ => {
            if (106..115).contains(&col) {
                ind(st == (col - 106) as u64) as i64
            } else if (129..161).contains(&col) {
                let win_fr = ind(win_fr_b(i, p, st, wi));
                if win_fr == 1 {
                    let j = col - 129;
                    if j < 32usize.saturating_sub(ix) {
                        get(&p.q, px + j) as i64
                    } else {
                        0
                    }
                } else if st == 1 {
                    if col == 137 {
                        let t = u32_bytes(p.qhk);
                        le256(&t[..(ix + 1).min(4)]) as i64
                    } else if col == 138 {
                        256i64.pow(ix as u32)
                    } else if col - 129 < 4 {
                        (get(&p.q, px) as i64)
                            .div_euclid(16)
                            .div_euclid(2i64.pow((col - 129) as u32))
                            % 2
                    } else if col - 129 < 8 {
                        (get(&p.q, px) as i64)
                            .rem_euclid(16)
                            .div_euclid(2i64.pow((col - 133) as u32))
                            % 2
                    } else {
                        0
                    }
                } else if st == 0 || st == 2 {
                    let rb = rb_v(i, p, st, ix, wi, px) as i64;
                    if col - 129 < 4 {
                        rb.div_euclid(16).div_euclid(2i64.pow((col - 129) as u32)) % 2
                    } else if col - 129 < 8 {
                        rb.rem_euclid(16).div_euclid(2i64.pow((col - 133) as u32)) % 2
                    } else {
                        0
                    }
                } else if st == 8 {
                    Mem { i, p }.mem_reg(ix, col - 129) as i64
                } else {
                    0
                }
            } else if (161..164).contains(&col) {
                if st == 4 || st == 8 {
                    l_b(i, col - 161 + ix) as i64
                } else {
                    l_b(i, col - 161) as i64
                }
            } else if (164..168).contains(&col) {
                if st == 4 {
                    Mem { i, p }.slb((col - 164 + ix) % 4) as i64
                } else if st == 8 {
                    Mem { i, p }.slb(col - 164 + ix) as i64
                } else {
                    Mem { i, p }.slb(col - 164) as i64
                }
            } else if (187..200).contains(&col) {
                if st == 8 {
                    (Mem { i, p }
                        .co2(ix)
                        .div_euclid(2i128.pow((col - 184) as u32))
                        .rem_euclid(2)) as i64
                } else {
                    0
                }
            } else {
                0
            }
        }
    }
}

/// `UpsGen.qRowCell` (`Gen.lean:511`).
#[allow(clippy::too_many_arguments)]
fn q_row_cell(i: &UpsInst, k: usize, px: usize, u: u64, col: usize) -> i64 {
    let p = i.part(k);
    let (st, ix, fl, wi) = fa(i, k, px);
    q_row(i, p, k, px, st, ix, fl, wi, u, col)
}

/// `UpsGen.qCell` (`Gen.lean:516`).
fn q_cell(i: &UpsInst, k: usize, px: usize, u: u64, col: usize) -> i64 {
    if is_pc(col) {
        pc_cell(i, i.part(k), k, col) as i64
    } else {
        q_row_cell(i, k, px, u, col)
    }
}

// ---------------------------------------------------------------------------
// `UPB` use counts (`UpsGen.rkey`, `uU`, `Gen.lean:539`)
// ---------------------------------------------------------------------------

/// `UpsGen.rkey` (`Gen.lean:540`): `(sN, spos)` for a read row, else `None`.
fn rkey(insts: &[UpsInst], r: (usize, Rk)) -> Option<(u64, i64)> {
    match r.1 {
        Rk::Q(k, p) => {
            let i = &insts[r.0];
            let part = i.part(k);
            let (st, ix, _fl, wi) = fa(i, k, p);
            if cp_b(i, part, st, wi) || extra_b(i, part, st, ix, wi) {
                Some((part.s_n, spos_v(i, part, st, ix, wi, p)))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// `UpsGen.uU` (`Gen.lean:549`): earlier reads of the same `(sN, spos)`.
fn uu(recs: &[(usize, Rk)], insts: &[UpsInst], q: usize) -> u64 {
    let key = rkey(insts, recs[q]);
    recs[..q].iter().filter(|&&r| rkey(insts, r) == key).count() as u64
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
                    Rk::Q(k, p) => q_cell(inst, k, p, uu(&recs, insts, q), col),
                };
                set_i(&mut t, q, col, x);
            }
        }
    }
    t
}

/// `upsA7` width (`Tables/UnfoldA7.lean`): `upsV3` + `s` (200) + `nD` (201).
pub const UPS_A7_WIDTH: usize = 202;

/// The honest `upsA7` trace `upsA7Trace insts t` (`Render/UnfoldA7Aligned.lean`):
/// [`ups_aligned`] plus `upsCols` (`Render/UnfoldA7Ext.lean`) — `s` the prefix
/// sum (in `F`) of `vb + qb` (columns 2, 3) over the rows before, `nD` =
/// `dd0·N0 + dd1·N1 + dd2·N2` (columns 28·11 + 29·12 + 30·13) on every row.
pub fn ups_a7(insts: &[UpsInst]) -> Tab {
    use super::{fp_add, fp_mul};
    let mut t = super::widen(&ups_aligned(insts), UPS_A7_WIDTH);
    let w = t.width;
    let mut s = 0u64;
    for r in 0..t.height() {
        let c = |x: usize| t.cells[r * w + x] as u64;
        let nd = fp_add(
            fp_add(fp_mul(c(28), c(11)), fp_mul(c(29), c(12))),
            fp_mul(c(30), c(13)),
        );
        let inc = fp_add(c(2), c(3));
        t.set(r, 200, s);
        t.set(r, 201, nd);
        s = fp_add(s, inc);
    }
    t
}

/// Parse `json` as a `List UpsInst` and render the `upsA7` trace.
pub fn render(json: &str) -> Result<Tab, String> {
    let insts: Vec<UpsInst> = serde_json::from_str(json).map_err(|e| e.to_string())?;
    Ok(ups_a7(&insts))
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

    #[test]
    fn part_constants_match_pc_cell() {
        let i = inst();
        let t = ups_aligned(std::slice::from_ref(&i));
        // Q rows follow the 4 walk + L value rows.
        let base = 4 + i.l();
        let mut row = base;
        for k in 0..i.n_q() {
            for p in 0..i.part(k).q.len() {
                for col in 0..UPS_WIDTH {
                    if !is_pc(col) || is_seg(col) {
                        continue;
                    }
                    let want = (pc_cell(&i, i.part(k), k, col) % crate::field::P as u64) as u32;
                    assert_eq!(t.cells[row * UPS_WIDTH + col], want, "Q({k},{p}) col {col}");
                }
                row += 1;
            }
        }
        // `j` column is `k + 1` on each part row; `qlen`; `rootP` on the last part.
        assert_eq!(t.cells[base * UPS_WIDTH + 49] as u64, 1);
        assert_eq!(t.cells[base * UPS_WIDTH + 78] as u64, 3);
        assert_eq!(
            t.cells[(row - 1) * UPS_WIDTH + 79] as u64,
            1,
            "rootP on last part row"
        );
    }

    #[test]
    fn render_json_round_trip() {
        let i = inst();
        let json = serde_json::to_string(std::slice::from_ref(&i)).unwrap();
        let t = render(&json).unwrap();
        assert_eq!(t.width, UPS_A7_WIDTH);
        assert_eq!(t, ups_a7(std::slice::from_ref(&i)));
    }

    #[test]
    fn a7_columns() {
        let i = inst();
        let base = ups_aligned(std::slice::from_ref(&i));
        let t = ups_a7(std::slice::from_ref(&i));
        assert_eq!((t.log, t.width), (base.log, UPS_A7_WIDTH));
        let at = |r: usize, c: usize| t.cells[r * UPS_A7_WIDTH + c] as u64;
        for r in 0..t.height() {
            for c in 0..UPS_WIDTH {
                assert_eq!(at(r, c) as u32, base.cells[r * UPS_WIDTH + c]);
            }
        }
        // `s` on the last row is Σ vb + qb = L + Σ |q| (`upsA7Total`)
        let total = i.l() + i.parts.iter().map(|p| p.q.len()).sum::<usize>();
        assert_eq!(at(0, 200), 0);
        assert_eq!(at(t.height() - 1, 200), total as u64);
        // `nD` on the segment's first row is `N[D]`
        assert_eq!(at(0, 201), i.n[i.d as usize]);
    }

    #[test]
    fn a7_constraints() {
        // the appended constraints (`NEARAIRV3_JSON`) on sampled (not honest)
        // instances: `s` rows 0, 1, last; `nD` on a segment's first row
        let mut r = crate::v3::sample::Rng::new(2);
        for n in [0, 1, 3] {
            let is = crate::v3::sample::ups(&mut r, n);
            let t = ups_a7(&is);
            let h = t.height();
            let mut cells = vec![(0, 200), (1, 200), (h - 1, 200)];
            if n > 0 {
                cells.push((0, 201));
            }
            crate::v3::a7_test::honest_and_tampered(7, UPS_WIDTH, &t, &cells);
        }
    }
}
