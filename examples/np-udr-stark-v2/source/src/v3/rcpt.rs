//! Honest `rcptV3` trace generator for `nearAirV3` table 16 (`RcptV3.tableQ`,
//! `NearV3/Rcpt/Tables/RcptR.lean`: width 263, 882 constraints), the Rust twin of
//! the installed honest render `rcptTraceAlignedQ pub x` (`Render/HonestRcptQ.lean`):
//!
//! ```text
//! rcptTraceQ      = patchTrace (counterPatch N 0 (physicalBoundaryRank N 0)) 0
//! N               = rcptTraceNative pub x = booleanReceiptTrace own ctx lists 22 …
//!                   (Render/PaddedRcptR.lean)
//! ```
//!
//! * `booleanReceiptTrace` = `emittedReceiptTrace` (emission patch) over
//!   `plannedTrace` (`Assembly/RcptSkeleton*`): per applied source list a 12-row
//!   header (`sCL`), then one segment per receipt.  Receipt cells come from
//!   `receiptCell` (bookkeeping, `rconsts` via `completeReceiptConstants`) and the
//!   frame chain `streamAux`/`tokenAux` ∘ `completeReceiptAux`
//!   (`Assembly/RcptDepositGlobalCommute.lean`: digest metadata, characters,
//!   predecessor / named scores, system, routing, key, gas borrow / effective /
//!   delay / flag / token / product, deposit age, deposit); header cells from
//!   `headerCell` ∘ `headerStreamAux` ∘ `completeReceiptHeaders`.
//! * The arithmetic repairs of `tableR` (2026-10-11): the refund surplus is
//!   `gasSurplusPrice` (gated by `gq = ge·(1 − sys)`, `0` for system receipts) and
//!   the deposit age `r − tprev` is a 13-bit value in `xb53..65` on the first `DEP`
//!   row.
//! * `counterPatch … physicalBoundaryRank` (`Render/HonestBalanceBnd.lean`): `uB` on
//!   **every** row (headers and padding included) is the number of earlier rows with
//!   `gBd = 1` and the same boundary key `(65·q + iB, loB, hiB, hnB)`.
//! * `patchTrace` (`Assembly/RoutingQTrace.lean`): on the first receiver row
//!   (`sV = fs = 1`) the seven scratch bits `xb12..18` hold `q` (`qBoundR`).
//! * The height is always `2^22` (`rcptTraceAlignedQ_log`).
//!
//! Cells no Lean frame determines (the `RcptInput` parameters `constants`,
//! `digests`, `fallback`, `headerFallback`) are those of the accepted render
//! (`Assembly/RenderV3RcptAccepted.lean`): `0`, except `uAK` on every receipt row,
//! the access-key use rank (`NativeAccessKeyRanks.rankAux`) = the view's `aku`.
//!
//! **Input.**  [`RcptE`] is the Lean view `RcptE` (`RcptV3Proof.rcptOf`) plus the
//! receipt's native routing interval `iv` (`nativeRoutingInterval k`): the routing
//! frame writes `loB`/`hiB`/`hnB` on every receiver row, while the view's `rlk`
//! only lists the rows with `gBd = 1`.  Without `iv`, `rlk` is read as the legacy
//! dense list (index = position).  [`RcptIn`] adds the prepared values the rows read
//! directly (`own`, `height`, `bgp`).  The burnt amounts, refund amounts and the
//! token chain are recomputed natively (`nativeBurn`, `gasSurplusPrice`), so the
//! view's `burnt`/`ramt`/`aft` are not read.
//!
//! **Testing.**  Table 16 reads prepared-statement public values in its local
//! constraints (`PH_OWN`, `PH_HEIGHT`, `PH_GP`, `PH_N`, `PH_BLEN`, `PH_BURNT`), so
//! every check uses the true public vector [`honest_pubs`] (`npudr v3check … rcpt`
//! goes through [`check_render`]).  Checks run at the compact height
//! `2^logOf(rows + 1)` rather than `2^22`: every row past the planned rows is zero
//! padding except `uB` (read by no constraint), so the checked row kinds and
//! transitions are the same.  The full `2^22 × 263` table is 4.4 GB of `u32`
//! ([`rcpt_aligned`]); the Lean differential (`conformance/RenderV3Rcpt.lean`,
//! `run-v2.d/rcpt.sh`) compares the first rows ([`render_prefix`]).

use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use serde::Deserialize;

use crate::field::F;

use super::{b, get, log_of, Tab};

pub const RCPT_WIDTH: usize = 263;

// ---------------------------------------------------------------------------
// Column layout (`NearV3/Rcpt/Tables/Rcpt/Layout.lean`)
// ---------------------------------------------------------------------------

#[allow(dead_code)]
mod col {
    pub const ACT: usize = 0;
    pub const RF: usize = 1;
    pub const RL: usize = 2;
    pub const LAST_R: usize = 3;
    pub const S_CL: usize = 4;
    pub const S_PL: usize = 5;
    pub const S_P: usize = 6;
    pub const S_VL: usize = 7;
    pub const S_V: usize = 8;
    pub const S_RID: usize = 9;
    pub const S_T0: usize = 10;
    pub const S_SL: usize = 11;
    pub const S_S: usize = 12;
    pub const S_KT: usize = 13;
    pub const S_PK: usize = 14;
    pub const S_GP: usize = 15;
    pub const S_TL: usize = 16;
    pub const S_DEP: usize = 17;
    pub const S_XP0: usize = 18;
    pub const S_XRI: usize = 19;
    pub const S_XG: usize = 20;
    pub const S_XST: usize = 21;
    pub const S_XL0: usize = 22;
    pub const S_XLH: usize = 23;
    pub const S_XRH: usize = 24;
    pub const S_XRF: usize = 25;
    pub const S_XRZ: usize = 26;
    pub const IDX: usize = 27;
    pub const FS: usize = 28;
    pub const FE: usize = 29;
    pub const B: usize = 30;
    pub const T_A: usize = 43;
    pub const SYM_A: usize = 44;
    pub const LAST_A: usize = 45;
    pub const G_KA: usize = 46;
    pub const KZ: usize = 47;
    pub const R: usize = 48;
    pub const O: usize = 49;
    pub const O2: usize = 50;
    pub const LP: usize = 51;
    pub const LV: usize = 52;
    pub const LS: usize = 53;
    pub const KT: usize = 54;
    pub const HR: usize = 55;
    pub const KSLOT: usize = 56;
    pub const TPREV: usize = 57;
    pub const CJ: usize = 58;
    pub const GE: usize = 59;
    pub const BIG: usize = 60;
    pub const O_END: usize = 61;
    pub const O2_END: usize = 62;
    pub const fn reg(i: usize) -> usize {
        63 + i
    }
    pub const fn tok(i: usize) -> usize {
        95 + i
    }
    pub const H2: usize = 111;
    pub const H3: usize = 112;
    pub const H5: usize = 113;
    pub const H6: usize = 114;
    pub const H7: usize = 115;
    pub const fn lb(i: usize) -> usize {
        116 + i
    }
    pub const Z: usize = 120;
    pub const LINV: usize = 121;
    pub const L210: usize = 122;
    pub const HX6: usize = 123;
    pub const ACC: usize = 124;
    pub const VC0: usize = 125;
    pub const VC1: usize = 126;
    pub const H01: usize = 127;
    pub const P1: usize = 128;
    pub const P2: usize = 129;
    pub const P3: usize = 130;
    pub const I1: usize = 131;
    pub const I2: usize = 132;
    pub const I3: usize = 133;
    pub const ISYS: usize = 134;
    pub const R1: usize = 135;
    /// v1's `lo8`, renamed `sys` in v3.
    pub const SYS: usize = 136;
    /// v1's `lo4`, renamed `ee` in v3.
    pub const EE: usize = 137;
    pub const fn xb(i: usize) -> usize {
        138 + i
    }
    pub const C1: usize = 204;
    pub const C2: usize = 205;
    pub const C3: usize = 206;
    pub const C4: usize = 207;
    pub const fn dl(i: usize) -> usize {
        208 + i
    }
    pub const BURNT: usize = 216;
    pub const RAMT: usize = 217;
    pub const SUM_D: usize = 218;
    pub const INV_A: usize = 219;
    pub const BEF: usize = 220;
    pub const LK: usize = 221;
    pub const ST: usize = 222;
    pub const DSUM: usize = 223;
    pub const INV_B: usize = 224;
    pub const D_I: usize = 225;
    pub const D_L: usize = 226;
    pub const G_DG: usize = 227;
    // v3 columns
    pub const J: usize = 228;
    pub const NJ: usize = 229;
    pub const LE: usize = 230;
    pub const GQ: usize = 231;
    pub const PC: usize = 232;
    pub const G_V: usize = 233;
    pub const G_S: usize = 234;
    pub const SX: usize = 235;
    pub const INV_D: usize = 236;
    pub const SCNT: usize = 237;
    pub const DM: usize = 238;
    pub const DD: usize = 239;
    pub const INV_L: usize = 240;
    pub const T_B: usize = 241;
    pub const SYM_B: usize = 242;
    pub const G_KB: usize = 243;
    pub const FK_F: usize = 244;
    pub const K_F: usize = 245;
    pub const G_F: usize = 246;
    pub const G_AK: usize = 247;
    pub const UAK: usize = 248;
    pub const Q: usize = 249;
    pub const EQ_L: usize = 250;
    pub const EQ_H: usize = 251;
    pub const G_BD: usize = 252;
    pub const LO_B: usize = 253;
    pub const HI_B: usize = 254;
    pub const HN_B: usize = 255;
    pub const U_B: usize = 256;
    pub const I_B: usize = 257;
    pub const V_B: usize = 258;
    pub const E_L: usize = 259;
    pub const E_H: usize = 260;
    pub const I_L: usize = 261;
    pub const I_H: usize = 262;
}

use col::*;

// ---------------------------------------------------------------------------
// Constants (`Near/Ids.lean`, `NearV3/Rcpt/Ids.lean`, `NearSpec.Params`)
// ---------------------------------------------------------------------------

const PM: u64 = crate::field::P as u64;

const K_RC: u64 = 1;
const K_RF: u64 = 2;
const K_PEO: u64 = 3;
const K_LEAF: u64 = 4;
const K_RID: u64 = 5;
const SYM_END: u64 = 16;

/// `Params.G` and `Params.storageAmountPerByte` (`NearSpec`).
const GAS_G: u128 = 223182562500;
const STORAGE_PER_BYTE: u128 = 10_000_000_000_000_000_000;

const G_LE: [u64; 8] = [196, 164, 183, 246, 51, 0, 0, 0];
const S_LE: [u64; 8] = [0, 0, 232, 137, 4, 35, 199, 138];

/// `regStates`: states whose `b` byte is the register head (`Rcpt/Arith.lean`).
const REG_STATES: [usize; 15] = [
    S_PL, S_VL, S_SL, S_T0, S_KT, S_TL, S_XP0, S_XG, S_XST, S_XL0, S_XRH, S_XRF, S_XRZ, S_XRI,
    S_XLH,
];

const SYSTEM: [u64; 6] = [115, 121, 115, 116, 101, 109];

fn msg_id(kind: u64, idx: u64) -> u64 {
    kind + 16 * idx
}

// ---------------------------------------------------------------------------
// Small numeric helpers (`RcptGen`, `RcptP`)
// ---------------------------------------------------------------------------

fn bit_of(x: u128, j: usize) -> u64 {
    if j >= 128 {
        0
    } else {
        ((x >> j) & 1) as u64
    }
}

/// Field inverse `x⁻¹` (`0 ↦ 0`).
fn inv_p(x: u128) -> u64 {
    let f = F::from_u64((x % PM as u128) as u64);
    f.try_inverse().unwrap_or(F::ZERO).as_canonical_u32() as u64
}

/// `(Fp.ofNat a − Fp.ofNat b)⁻¹` (`0 ↦ 0`).
fn inv_pf(a: i128, b: i128) -> u64 {
    let d = F::from_u64((a.rem_euclid(PM as i128)) as u64)
        - F::from_u64((b.rem_euclid(PM as i128)) as u64);
    d.try_inverse().unwrap_or(F::ZERO).as_canonical_u32() as u64
}

/// `leBytes w x`: byte `i` of `x` (`u128`, so bytes `16..` are 0).
fn le_bytes(w: usize, x: u128) -> Vec<u64> {
    (0..w)
        .map(|i| ((x >> (8 * i.min(15))) & 255) as u64)
        .collect()
}

/// `leN'` of a byte list (`< 2^128`).
fn le_n(v: &[u64]) -> u128 {
    v.iter().enumerate().fold(0u128, |a, (i, &b)| {
        if i < 16 {
            a | (((b & 255) as u128) << (8 * i))
        } else {
            a
        }
    })
}

fn set_bits(rw: &mut [u64; RCPT_WIDTH], off: usize, len: usize, x: u128) {
    for j in 0..len {
        rw[xb(off + j)] = bit_of(x, j);
    }
}

/// `conv g v i = Σ_{j ≤ i} g_j · v (i − j)`.
fn conv(g: &[u64], v: &[u64], i: usize) -> u64 {
    (0..g.len())
        .filter(|&j| j <= i)
        .map(|j| g[j] * get(v, i - j))
        .sum()
}

/// `chain x`: carry into position `i`.
fn chain(x: &[u64]) -> Vec<u64> {
    let mut out = vec![0u64; x.len() + 1];
    for i in 0..x.len() {
        out[i + 1] = (x[i] + out[i]) / 256;
    }
    out
}

/// `bchain a b b0`: borrow into position `i`.
fn bchain(a: &[u64], b: &[u64], b0: u64) -> Vec<u64> {
    let mut out = vec![0u64; a.len() + 1];
    out[0] = b0;
    for i in 0..a.len() {
        out[i + 1] = u64::from(get(a, i) < get(b, i) + out[i]);
    }
    out
}

fn sqd(a: i128, b: i128) -> u128 {
    let d = a - b;
    (d * d) as u128
}

fn is_hex_c(ch: u64) -> bool {
    (48..=57).contains(&ch) || (97..=102).contains(&ch)
}

fn sys_b(j: usize) -> u64 {
    get(&SYSTEM, j)
}

/// `RcptGen.charCell`: the character scratch columns of byte `ch`.
fn char_cell(ch: u64, c: usize) -> u64 {
    let hi = ch / 16;
    let lo = ch % 16;
    if c == H2 {
        b(hi == 2)
    } else if c == H3 {
        b(hi == 3)
    } else if c == H5 {
        b(hi == 5)
    } else if c == H6 {
        b(hi == 6)
    } else if c == H7 {
        b(hi == 7)
    } else if c == lb(0) {
        bit_of(lo as u128, 0)
    } else if c == lb(1) {
        bit_of(lo as u128, 1)
    } else if c == lb(2) {
        bit_of(lo as u128, 2)
    } else if c == lb(3) {
        bit_of(lo as u128, 3)
    } else if c == Z {
        b(lo == 0)
    } else if c == LINV {
        if lo == 0 {
            0
        } else {
            inv_p(lo as u128)
        }
    } else if c == L210 {
        b(lo % 8 == 7)
    } else if c == HX6 {
        b(hi == 6 && (1..=6).contains(&lo))
    } else {
        0
    }
}

// ---------------------------------------------------------------------------
// JSON mirrors (`RcptE`, `ListV3`, `RcptView.lean`)
// ---------------------------------------------------------------------------

/// One routing lookup `(pos, lo, hi, hn, u)` (`RLk`).
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct Rlk {
    pub pos: u64,
    pub lo: u64,
    pub hi: u64,
    pub hn: u64,
    pub u: u64,
}

/// A receipt's native routing interval `(lower, upper)` (`nativeRoutingInterval k`,
/// `Option Bytes × Option Bytes`; `None` = unbounded).
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct Iv {
    #[serde(default)]
    pub lo: Option<Vec<u64>>,
    #[serde(default)]
    pub hi: Option<Vec<u64>>,
}

/// `ZkFormal.NearV3.RcptE`: v1's `RcptV` plus the system / signer-receiver /
/// access-key / routing data, plus the native routing interval `iv`.
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct RcptE {
    #[serde(default)]
    pub p: Vec<u64>,
    #[serde(default)]
    pub v: Vec<u64>,
    #[serde(default)]
    pub s: Vec<u64>,
    #[serde(default)]
    pub rid: Vec<u64>,
    #[serde(default)]
    pub kt: u64,
    #[serde(default)]
    pub pk: Vec<u64>,
    #[serde(default)]
    pub gp: Vec<u64>,
    #[serde(default)]
    pub dep: Vec<u64>,
    #[serde(default)]
    pub hr: bool,
    #[serde(default)]
    pub ge: bool,
    #[serde(default)]
    pub kslot: u64,
    #[serde(default)]
    pub tprev: u64,
    #[serde(default)]
    pub bef: Vec<u64>,
    #[serde(default)]
    pub lk: Vec<u64>,
    #[serde(default)]
    pub st: Vec<u64>,
    #[serde(default)]
    pub aft: Vec<u64>,
    #[serde(default)]
    pub burnt: Vec<u64>,
    #[serde(default)]
    pub ramt: Vec<u64>,
    #[serde(default)]
    pub rfid: Vec<u64>,
    #[serde(default)]
    pub peoh: Vec<u64>,
    // v3
    #[serde(default)]
    pub sys: bool,
    #[serde(default)]
    pub ee: bool,
    #[serde(default)]
    pub gv: Vec<bool>,
    #[serde(default)]
    pub gs: Vec<bool>,
    #[serde(default)]
    pub sx: Vec<u64>,
    #[serde(default)]
    pub akf: u64,
    #[serde(default)]
    pub akk: u64,
    #[serde(default)]
    pub aku: u64,
    #[serde(default)]
    pub q: u64,
    #[serde(default)]
    pub rlk: Vec<Rlk>,
    /// The native routing interval (not part of the Lean view, see the module doc).
    #[serde(default)]
    pub iv: Option<Iv>,
}

/// `ListV3`: the header's two `n_j` bytes and the list's receipts.
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct ListV3 {
    #[serde(default)]
    pub n0: u64,
    #[serde(default)]
    pub n1: u64,
    #[serde(default)]
    pub rs: Vec<RcptE>,
}

/// The whole `rcptV3` input: the applied source lists plus the prepared-statement
/// values the row constructor reads directly.
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct RcptIn {
    pub lists: Vec<ListV3>,
    /// `u64` own shard id (`PH_OWN`).
    #[serde(default)]
    pub own: u64,
    /// `u64` height of `B2` (`PH_HEIGHT`).
    #[serde(default)]
    pub height: u64,
    /// `u128` prepared block gas price (`PH_GP`, `ctx.gasPrice`).
    #[serde(default)]
    pub bgp: u128,
}

// ---------------------------------------------------------------------------
// Per-receipt row context
// ---------------------------------------------------------------------------

/// Everything a receipt segment needs: the view data plus its plan
/// (`ReceiptPlan`: indices, offsets, last flags) and token prefix.
#[derive(Clone, Debug, Default)]
struct Rd {
    p: Vec<u64>,
    v: Vec<u64>,
    s: Vec<u64>,
    rid: Vec<u64>,
    kt: u64,
    pk: Vec<u64>,
    gp: Vec<u64>,
    dep: Vec<u64>,
    ge: bool,
    hr: bool,
    sys: bool,
    kslot: u64,
    tprev: u64,
    bef: Vec<u64>,
    lk: Vec<u64>,
    st: Vec<u64>,
    rfid: Vec<u64>,
    peoh: Vec<u64>,
    akf: u64,
    akk: u64,
    aku: u64,
    q: u64,
    /// routing interval `(lower, upper)`
    lo: Option<Vec<u64>>,
    hi: Option<Vec<u64>>,
    // plan
    r: u64,
    j: u64,
    nj: u64,
    cj: u64,
    o: u64,
    o2: u64,
    le: bool,
    last_r: bool,
    /// `prefixBurn` before this receipt
    before: u128,
}

impl Rd {
    fn lp(&self) -> usize {
        self.p.len()
    }
    fn lv(&self) -> usize {
        self.v.len()
    }
    fn ls(&self) -> usize {
        self.s.len()
    }
    /// `systemEqualLength` (`dm`).
    fn dm(&self) -> bool {
        self.ls() == self.lv()
    }
    /// `systemMismatch` (`dd`).
    fn dd(&self) -> bool {
        self.sys && !self.system_equal() && self.dm()
    }
    /// `gq = ge·(1 − sys)` (`gasEffectiveConstants`).
    fn gq(&self) -> bool {
        self.ge && !self.sys
    }
    fn rc_len(&self) -> u64 {
        123 + self.lp() as u64 + self.lv() as u64 + self.ls() as u64 + 32 * self.kt
    }
    fn refund_len(&self) -> u64 {
        if self.hr {
            129 + 2 * self.ls() as u64 + 32 * self.kt
        } else {
            0
        }
    }
    fn o_end(&self) -> u64 {
        self.o + self.rc_len()
    }
    fn o2_end(&self) -> u64 {
        self.o2 + self.refund_len()
    }
    /// `systemEqual`: predecessor `"system"` and signer = receiver.
    fn system_equal(&self) -> bool {
        self.sys && self.s == self.v
    }
    /// `firstMismatch` of signer / receiver.
    fn first_mismatch(&self) -> usize {
        self.s
            .iter()
            .zip(self.v.iter())
            .position(|(a, c)| a != c)
            .unwrap_or(self.s.len().min(self.v.len()))
    }
    /// `systemLookup r i`.
    fn system_lookup(&self, i: usize) -> bool {
        self.system_equal() || (self.dd() && i == self.first_mismatch())
    }
    /// `systemLookupCount r i`.
    fn system_lookup_count(&self, i: usize) -> u64 {
        if self.system_equal() {
            i as u64 + 1
        } else if self.dd() && self.first_mismatch() <= i {
            1
        } else {
            0
        }
    }
    /// `nativeFieldByte`.
    fn field_byte(&self, state: usize, i: usize) -> u64 {
        if state == S_P {
            get(&self.p, i)
        } else if state == S_V {
            get(&self.v, i)
        } else if state == S_RID {
            get(&self.rid, i)
        } else if state == S_S {
            get(&self.s, i)
        } else if state == S_PK {
            get(&self.pk, i)
        } else if state == S_GP {
            get(&self.gp, i)
        } else if state == S_DEP {
            get(&self.dep, i)
        } else {
            0
        }
    }
    fn gp_n(&self) -> u128 {
        le_n(&self.gp)
    }
    /// `gasBorrow ctx r i`.
    fn gas_borrow(&self, bgp: &[u64], i: usize) -> u64 {
        get(&bchain(&self.gp, bgp, 0), i)
    }
    /// `gasDifference ctx r i` (`bdig`).
    fn gas_diff(&self, bgp: &[u64], i: usize) -> u64 {
        let bc = bchain(&self.gp, bgp, 0);
        get(&self.gp, i) + 256 * get(&bc, i + 1) - get(bgp, i) - get(&bc, i)
    }
    /// `gasBurnPrice`: `min(gp, bgp)`, `0` for system receipts.
    fn burn_price(&self, bgp: u128) -> u128 {
        if self.sys {
            0
        } else {
            self.gp_n().min(bgp)
        }
    }
    /// `gasSurplusPrice`: `gp − min(gp, bgp)`, `0` for system receipts.
    fn surplus_price(&self, bgp: u128) -> u128 {
        if self.sys {
            0
        } else {
            self.gp_n() - self.gp_n().min(bgp)
        }
    }
    /// `nativeBurn`: `G · gasBurnPrice`.
    fn burn(&self, bgp: u128) -> u128 {
        GAS_G * self.burn_price(bgp)
    }
    /// `nativeDepositData.big`: `10^19 · storage ≤ bef + dep + locked`.
    fn big(&self) -> bool {
        STORAGE_PER_BYTE.wrapping_mul(le_n(&self.st))
            <= le_n(&self.bef)
                .wrapping_add(le_n(&self.dep))
                .wrapping_add(le_n(&self.lk))
    }
}

// ---------------------------------------------------------------------------
// Field lengths, fields, register loads
// ---------------------------------------------------------------------------

/// `RcptSkeleton.fields`.
fn fields(refund: bool) -> Vec<usize> {
    let mut f = vec![
        S_PL, S_P, S_VL, S_V, S_RID, S_T0, S_SL, S_S, S_KT, S_PK, S_GP, S_TL, S_DEP, S_XP0,
    ];
    if refund {
        f.push(S_XRI);
    }
    f.extend([S_XG, S_XST, S_XL0, S_XLH]);
    if refund {
        f.extend([S_XRH, S_XRF, S_XRZ]);
    }
    f
}

/// `RcptSkeleton.fieldLen`.
fn field_len(d: &Rd, s: usize) -> usize {
    if s == S_CL {
        12
    } else if s == S_PL {
        4
    } else if s == S_P {
        d.lp()
    } else if s == S_VL {
        4
    } else if s == S_V {
        d.lv()
    } else if s == S_RID {
        32
    } else if s == S_T0 {
        1
    } else if s == S_SL {
        4
    } else if s == S_S {
        d.ls()
    } else if s == S_KT {
        1
    } else if s == S_PK {
        (32 + 32 * d.kt) as usize
    } else if s == S_GP {
        16
    } else if s == S_TL {
        13
    } else if s == S_DEP {
        16
    } else if s == S_XP0 {
        4
    } else if s == S_XRI {
        32
    } else if s == S_XG {
        8
    } else if s == S_XST {
        5
    } else if s == S_XL0 {
        4
    } else if s == S_XLH {
        32
    } else if s == S_XRH {
        16
    } else if s == S_XRF {
        10
    } else if s == S_XRZ {
        16
    } else {
        0
    }
}

/// `RcptSkeleton.registerLoad`: the register byte stream loaded at state `s`.
fn register_load(d: &Rd, s: usize, height: u64, bgp: &[u64]) -> Vec<u64> {
    let mut v: Vec<u64> = match s {
        S_PL => vec![d.lp() as u64, 0, 0, 0],
        S_VL => vec![d.lv() as u64, 0, 0, 0],
        S_SL => vec![d.ls() as u64, 0, 0, 0],
        S_T0 => vec![0],
        S_KT => vec![d.kt],
        S_TL => vec![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3],
        S_XP0 => vec![b(d.hr), 0, 0, 0],
        S_XG => G_LE.to_vec(),
        S_XST => vec![2, 0, 0, 0, 0],
        S_XL0 => vec![2, 0, 0, 0],
        S_XRH => {
            let mut h = le_bytes(8, height as u128);
            h.extend([0; 8]);
            h
        }
        S_XRF => vec![6, 0, 0, 0, 115, 121, 115, 116, 101, 109],
        S_XRZ => vec![0; 16],
        S_P => SYSTEM.to_vec(),
        S_GP => bgp.to_vec(),
        S_XRI => d.rfid.clone(),
        S_XLH => d.peoh.clone(),
        _ => Vec::new(),
    };
    v.resize(32, 0);
    v
}

// ---------------------------------------------------------------------------
// Routing frame (`RoutingFrame.frameOf` / `frameCell`, `RcptRoutingFrame.routingAux`)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, Default)]
struct RouteFrame {
    value: u64,
    lower: u64,
    upper: u64,
    equal_lower: bool,
    equal_upper: bool,
    missing_upper: bool,
    pos: usize,
}

/// `samePrefix a b n`: `a_i = b_i` for `i < n` (out of range reads `0`).
fn same_prefix(a: &[u64], b: &[u64], n: usize) -> bool {
    (0..n).all(|i| get(a, i) == get(b, i))
}

/// `frameOf receiver (interval p) pos`.
fn route_frame(d: &Rd, pos: usize) -> RouteFrame {
    let empty: Vec<u64> = Vec::new();
    let lo = d.lo.as_ref().unwrap_or(&empty);
    let hi = d.hi.as_ref().unwrap_or(&empty);
    RouteFrame {
        value: get(&d.v, pos),
        lower: get(lo, pos),
        upper: get(hi, pos),
        equal_lower: same_prefix(&d.v, lo, pos),
        equal_upper: d.hi.is_some() && same_prefix(&d.v, hi, pos),
        missing_upper: d.hi.is_none(),
        pos,
    }
}

/// `RoutingFrame.frameCell` on the routing scratch columns.
fn route_cell(f: &RouteFrame, c: usize) -> u64 {
    if c == I_L {
        inv_pf(f.value as i128, f.lower as i128)
    } else if c == I_H {
        inv_pf(f.upper as i128, f.value as i128)
    } else if c == I_B {
        f.pos as u64
    } else if c == V_B {
        f.value
    } else if c == LO_B {
        f.lower
    } else if c == HI_B {
        f.upper
    } else if c == HN_B {
        b(f.missing_upper)
    } else if c == EQ_L {
        b(f.equal_lower)
    } else if c == EQ_H {
        b(f.equal_upper)
    } else if c == G_BD {
        b(f.equal_lower || f.equal_upper)
    } else if c == E_L {
        b(f.value == f.lower)
    } else if c == E_H {
        b(f.upper == f.value)
    } else if (xb(20)..xb(29)).contains(&c) {
        bit_of(f.value as u128 + 255 - f.lower as u128, c - xb(20))
    } else if (xb(29)..xb(38)).contains(&c) {
        bit_of(f.upper as u128 + 255 - f.value as u128, c - xb(29))
    } else {
        0
    }
}

/// The routing scratch column set (`routingScratch`).
fn routing_scratch(c: usize) -> bool {
    matches!(
        c,
        EQ_L | EQ_H | E_L | E_H | V_B | I_B | LO_B | HI_B | HN_B | I_L | I_H | G_BD
    ) || (xb(20)..xb(38)).contains(&c)
}

/// The interval of a receipt: `iv` if given, else the legacy dense `rlk`
/// (`rlk[i]` is position `i`; `hn = 1` on the first lookup means no upper bound).
fn interval_of(e: &RcptE) -> (Option<Vec<u64>>, Option<Vec<u64>>) {
    if let Some(iv) = &e.iv {
        return (iv.lo.clone(), iv.hi.clone());
    }
    let lo: Vec<u64> = e.rlk.iter().map(|r| r.lo).collect();
    let miss = e.rlk.first().map(|r| r.hn == 1).unwrap_or(true);
    let hi: Vec<u64> = e.rlk.iter().map(|r| r.hi).collect();
    let trim = |mut v: Vec<u64>| {
        while v.last() == Some(&0) {
            v.pop();
        }
        v
    };
    (Some(trim(lo)), if miss { None } else { Some(trim(hi)) })
}

// ---------------------------------------------------------------------------
// ---------------------------------------------------------------------------
// Key symbols (`RcptKeyFrame`)
// ---------------------------------------------------------------------------

fn key_zero(s: usize, i: usize) -> bool {
    s == S_VL && i < 2
}
fn key_access_a(s: usize, i: usize) -> bool {
    s == S_T0
        || (s == S_SL && i == 0)
        || s == S_S
        || s == S_KT
        || s == S_PK
        || (s == S_GP && i == 0)
}
fn key_access_b(s: usize, i: usize) -> bool {
    s == S_T0 || (s == S_SL && i == 0) || s == S_S || s == S_KT || s == S_PK
}
fn key_gate_a(d: &Rd, s: usize, i: usize) -> bool {
    s == S_V || key_zero(s, i) || (s == S_RID && i == 0) || (d.system_equal() && key_access_a(s, i))
}
fn key_gate_b(d: &Rd, s: usize, i: usize) -> bool {
    s == S_V || (d.system_equal() && key_access_b(s, i))
}
fn key_last(d: &Rd, s: usize, i: usize) -> bool {
    (s == S_RID && i == 0) || (d.system_equal() && s == S_GP && i == 0)
}
fn key_byte(d: &Rd, s: usize, i: usize) -> u64 {
    if s == S_V {
        get(&d.v, i)
    } else if s == S_S {
        get(&d.s, i)
    } else if s == S_PK {
        get(&d.pk, i)
    } else {
        0
    }
}
fn key_pos_a(d: &Rd, s: usize, i: usize) -> u64 {
    if s == S_V || s == S_S {
        2 + 2 * i as u64
    } else if s == S_VL {
        i as u64
    } else if s == S_RID {
        2 + 2 * d.lv() as u64
    } else if s == S_SL {
        2 + 2 * d.ls() as u64
    } else if s == S_KT {
        4 + 2 * d.ls() as u64
    } else if s == S_PK {
        6 + 2 * d.ls() as u64 + 2 * i as u64
    } else if s == S_GP {
        70 + 2 * d.ls() as u64 + 64 * d.kt
    } else {
        0
    }
}
fn key_pos_b(d: &Rd, s: usize, i: usize) -> u64 {
    if s == S_V || s == S_S {
        3 + 2 * i as u64
    } else if s == S_T0 {
        1
    } else if s == S_SL {
        3 + 2 * d.ls() as u64
    } else if s == S_KT {
        5 + 2 * d.ls() as u64
    } else if s == S_PK {
        7 + 2 * d.ls() as u64 + 2 * i as u64
    } else {
        0
    }
}
fn key_sym_a(d: &Rd, s: usize, i: usize) -> u64 {
    if s == S_V || s == S_S || s == S_PK {
        key_byte(d, s, i) / 16
    } else if s == S_RID || s == S_GP {
        SYM_END
    } else {
        0
    }
}
fn key_sym_b(d: &Rd, s: usize, i: usize) -> u64 {
    if s == S_V || s == S_S || s == S_PK {
        key_byte(d, s, i) % 16
    } else if s == S_T0 || s == S_SL {
        2
    } else if s == S_KT {
        d.kt
    } else {
        0
    }
}

// ---------------------------------------------------------------------------
// Emissions (`NearV3/Rcpt/Tables/Rcpt/Fields.lean`)
// ---------------------------------------------------------------------------

/// A linear expression `k + Σ coef·col`.
#[derive(Clone, Debug)]
struct Lin {
    k: u64,
    t: Vec<(u64, usize)>,
}

impl Lin {
    fn eval(&self, rw: &[u64; RCPT_WIDTH]) -> u64 {
        self.t
            .iter()
            .fold(self.k % PM, |a, &(m, c)| (a + m % PM * (rw[c] % PM)) % PM)
    }
}

fn kk(v: u64) -> Lin {
    Lin { k: v, t: vec![] }
}
fn cc(x: usize) -> Lin {
    Lin {
        k: 0,
        t: vec![(1, x)],
    }
}
fn lin(k: u64, t: &[(u64, usize)]) -> Lin {
    Lin { k, t: t.to_vec() }
}

/// `(Id, pos, value, gate)`
type Em = [Lin; 4];

/// `emits` of `NearV3/Rcpt/Tables/Rcpt/Fields.lean`.
fn emits() -> Vec<(usize, Vec<Em>)> {
    let peo = || lin(K_PEO, &[(16, R)]);
    let leaf = || lin(K_LEAF, &[(16, R)]);
    let ridm = || lin(K_RID, &[(16, R)]);
    let rc = || lin(K_RC, &[(16, J)]);
    let rf = || kk(K_RF);
    let ix = || cc(IDX);
    let be = || cc(B);
    let one = || kk(1);
    let hr = || cc(HR);
    let at = |k: u64, t: &[(u64, usize)]| {
        let mut t = t.to_vec();
        t.push((1, IDX));
        Lin { k, t }
    };
    let var: [(u64, usize); 4] = [(1, LP), (1, LV), (1, LS), (32, KT)];
    let with = |a: &[(u64, usize)], b: &[(u64, usize)]| -> Vec<(u64, usize)> {
        a.iter().chain(b).copied().collect()
    };
    vec![
        (S_CL, vec![[rc(), ix(), cc(reg(0)), one()]]),
        (S_PL, vec![[rc(), at(0, &[(1, O)]), be(), one()]]),
        (S_P, vec![[rc(), at(4, &[(1, O)]), be(), one()]]),
        (
            S_VL,
            vec![
                [rc(), at(4, &[(1, O), (1, LP)]), be(), one()],
                [peo(), at(28, &[(32, HR)]), be(), one()],
            ],
        ),
        (
            S_V,
            vec![
                [rc(), at(8, &[(1, O), (1, LP)]), be(), one()],
                [peo(), at(32, &[(32, HR)]), be(), one()],
            ],
        ),
        (
            S_RID,
            vec![
                [rc(), at(8, &[(1, O), (1, LP), (1, LV)]), be(), one()],
                [leaf(), at(4, &[]), be(), one()],
                [ridm(), ix(), be(), hr()],
            ],
        ),
        (
            S_T0,
            vec![
                [rc(), lin(40, &[(1, O), (1, LP), (1, LV)]), be(), one()],
                [rf(), lin(46, &[(1, O2), (1, LS)]), be(), hr()],
            ],
        ),
        (
            S_SL,
            vec![
                [rc(), at(41, &[(1, O), (1, LP), (1, LV)]), be(), one()],
                [rf(), at(10, &[(1, O2)]), be(), hr()],
                [rf(), at(47, &[(1, O2), (1, LS)]), be(), hr()],
            ],
        ),
        (
            S_S,
            vec![
                [rc(), at(45, &[(1, O), (1, LP), (1, LV)]), be(), one()],
                [rf(), at(14, &[(1, O2)]), be(), hr()],
                [rf(), at(51, &[(1, O2), (1, LS)]), be(), hr()],
            ],
        ),
        (
            S_KT,
            vec![
                [
                    rc(),
                    lin(45, &[(1, O), (1, LP), (1, LV), (1, LS)]),
                    be(),
                    one(),
                ],
                [rf(), lin(51, &[(1, O2), (2, LS)]), be(), hr()],
            ],
        ),
        (
            S_PK,
            vec![
                [
                    rc(),
                    at(46, &[(1, O), (1, LP), (1, LV), (1, LS)]),
                    be(),
                    one(),
                ],
                [rf(), at(52, &[(1, O2), (2, LS)]), be(), hr()],
            ],
        ),
        (
            S_GP,
            vec![
                [rc(), at(78, &with(&[(1, O)], &var)), be(), one()],
                [peo(), at(12, &[(32, HR)]), cc(BURNT), one()],
                [rf(), at(113, &[(1, O2), (2, LS), (32, KT)]), cc(RAMT), hr()],
            ],
        ),
        (
            S_TL,
            vec![
                [rc(), at(94, &with(&[(1, O)], &var)), be(), one()],
                [rf(), at(100, &[(1, O2), (2, LS), (32, KT)]), be(), hr()],
            ],
        ),
        (
            S_DEP,
            vec![[rc(), at(107, &with(&[(1, O)], &var)), be(), one()]],
        ),
        (S_XP0, vec![[peo(), ix(), be(), one()]]),
        (
            S_XRI,
            vec![
                [peo(), at(4, &[]), be(), one()],
                [rf(), at(14, &[(1, O2), (1, LS)]), be(), one()],
            ],
        ),
        (S_XG, vec![[peo(), at(4, &[(32, HR)]), be(), one()]]),
        (
            S_XST,
            vec![[peo(), at(32, &[(32, HR), (1, LV)]), be(), one()]],
        ),
        (S_XL0, vec![[leaf(), ix(), be(), one()]]),
        (S_XLH, vec![[leaf(), at(36, &[]), be(), one()]]),
        (S_XRH, vec![[ridm(), at(32, &[]), be(), one()]]),
        (S_XRF, vec![[rf(), at(0, &[(1, O2)]), be(), one()]]),
        (
            S_XRZ,
            vec![[rf(), at(84, &[(1, O2), (2, LS), (32, KT)]), be(), one()]],
        ),
    ]
}

fn fill_emits(ems: &[(usize, Vec<Em>)], rw: &mut [u64; RCPT_WIDTH]) {
    for (s, es) in ems {
        if rw[*s] == 1 {
            for slot in 0..3 {
                if let Some(em) = es.get(slot) {
                    let vals = [
                        em[0].eval(rw),
                        em[1].eval(rw),
                        em[2].eval(rw),
                        em[3].eval(rw),
                    ];
                    rw[e_id(slot)] = vals[0];
                    rw[e_pos(slot)] = vals[1];
                    rw[e_v(slot)] = vals[2];
                    rw[e_g(slot)] = vals[3];
                } else {
                    rw[e_id(slot)] = 0;
                    rw[e_pos(slot)] = 0;
                    rw[e_v(slot)] = 0;
                    rw[e_g(slot)] = 0;
                }
            }
        }
    }
}

fn e_id(e: usize) -> usize {
    31 + 4 * e
}
fn e_pos(e: usize) -> usize {
    32 + 4 * e
}
fn e_v(e: usize) -> usize {
    33 + 4 * e
}
fn e_g(e: usize) -> usize {
    34 + 4 * e
}

// ---------------------------------------------------------------------------
// Rows
// ---------------------------------------------------------------------------

type Row = [u64; RCPT_WIDTH];

/// Receipt segment rows: `receiptCell` over `tokenReceiptAux pub digests tokens`
/// ∘ `completeReceiptAux` ∘ `depositFinalAux`, constants from
/// `completeReceiptConstants` ∘ `depositConstants` ∘ `depositAgeConstants`.
fn seg_rows(d: &Rd, height: u64, bgp: u128, bgp_b: &[u64]) -> Vec<Row> {
    let g5 = &G_LE[..5];
    let burn = d.burn(bgp);
    let tok_old = le_bytes(16, d.before);
    let tok_new = le_bytes(16, d.before + burn);
    // gas arithmetic (whole-receipt streams)
    let pcv: Vec<u64> = le_bytes(16, d.burn_price(bgp));
    let sv: Vec<u64> = le_bytes(16, d.surplus_price(bgp));
    let bcv = chain(&(0..16).map(|k| conv(g5, &pcv, k)).collect::<Vec<_>>());
    let scv = chain(&(0..16).map(|k| conv(g5, &sv, k)).collect::<Vec<_>>());
    let burnt_b = le_bytes(16, burn);
    let ramt_b = le_bytes(16, GAS_G * d.surplus_price(bgp));
    let tcv = chain(
        &(0..16)
            .map(|k| get(&tok_old, k) + get(&burnt_b, k))
            .collect::<Vec<_>>(),
    );
    let diff_sum: u64 = (0..16).map(|k| d.gas_diff(bgp_b, k)).sum();
    let inv_a = if d.hr { inv_p(diff_sum as u128) } else { 0 };
    // character scores (`characterData`, whole-field values)
    let p_acc: u128 = (0..d.lp())
        .map(|j| sqd(get(&d.p, j) as i128, sys_b(j) as i128))
        .sum();
    let p_score = (p_acc + sqd(d.lp() as i128, 6)) % PM as u128;
    let v0 = get(&d.v, 0);
    let v1 = get(&d.v, 1);
    let h01 = b(is_hex_c(v0)) + b(is_hex_c(v1));
    let v_acc: u64 = (0..d.lv()).map(|j| b(is_hex_c(get(&d.v, j)))).sum();
    let lvi = d.lv() as i128;
    let va = v_acc as i128;
    let pv1 = (sqd(lvi, 64) + sqd(va, lvi)) % PM as u128;
    let pv2 =
        (sqd(lvi, 42) + sqd(v0 as i128, 48) + sqd(v1 as i128, 120) + sqd(va, h01 as i128 + 40))
            % PM as u128;
    let pv3 =
        (sqd(lvi, 42) + sqd(v0 as i128, 48) + sqd(v1 as i128, 115) + sqd(va, h01 as i128 + 40))
            % PM as u128;
    let big = d.big();
    let access = if d.akf == 0 { Some(d.akk) } else { None };
    let mut rows = Vec::new();
    for &s in &fields(d.hr) {
        let len = field_len(d, s);
        let ld = register_load(d, s, height, bgp_b);
        for i in 0..len {
            let mut rw = [0u64; RCPT_WIDTH];
            let last = i + 1 == len;
            // control (`controlCell`) and bookkeeping (`receiptCell`)
            rw[ACT] = 1;
            rw[IDX] = i as u64;
            rw[FS] = b(i == 0);
            rw[FE] = b(last);
            rw[s] = 1;
            let is_rl = last && (s == S_XRZ || (s == S_XLH && !d.hr));
            rw[RF] = b(s == S_PL && i == 0);
            rw[RL] = b(is_rl);
            rw[LE] = b(is_rl && d.le);
            rw[LAST_R] = b(is_rl && d.le && d.last_r);
            rw[J] = d.j;
            rw[NJ] = d.nj;
            rw[R] = d.r;
            rw[CJ] = d.cj;
            rw[O] = d.o;
            rw[O_END] = d.o_end();
            rw[O2] = d.o2;
            rw[O2_END] = d.o2_end();
            rw[LP] = d.lp() as u64;
            rw[LV] = d.lv() as u64;
            rw[LS] = d.ls() as u64;
            rw[KT] = d.kt;
            rw[HR] = b(d.hr);
            // `rconsts`
            rw[KSLOT] = d.kslot;
            rw[TPREV] = d.tprev;
            rw[GE] = b(d.ge);
            rw[BIG] = b(big);
            rw[SYS] = b(d.sys);
            rw[EE] = b(d.system_equal());
            rw[GQ] = b(d.gq());
            rw[DM] = b(d.dm());
            rw[DD] = b(d.dd());
            rw[Q] = d.q;
            // register stream and byte (`streamAux`)
            for j in 0..32 {
                rw[reg(j)] = get(&ld, i + j);
            }
            rw[B] = if REG_STATES.contains(&s) {
                get(&ld, i)
            } else {
                d.field_byte(s, i)
            };
            // tokens (`tokenAux`)
            for j in 0..16 {
                rw[tok(j)] = if s < S_GP {
                    get(&tok_old, j)
                } else if s == S_GP {
                    if i + j < 16 {
                        get(&tok_old, i + j)
                    } else {
                        get(&tok_new, i + j - 16)
                    }
                } else {
                    get(&tok_new, j)
                };
            }
            // digest metadata (`digestMetadata`)
            rw[G_DG] = b(i == 0 && (s == S_XRI || s == S_XLH));
            if s == S_XRI {
                rw[D_I] = msg_id(K_RID, d.r);
                rw[D_L] = 48;
            } else {
                rw[D_I] = msg_id(K_PEO, d.r);
                rw[D_L] = 37 + 32 * b(d.hr) + d.lv() as u64;
            }
            // characters (`characterAux`, `characterLengthAux`)
            if s == S_P || s == S_V || s == S_S {
                let bv = d.field_byte(s, i);
                for c in 111..=123 {
                    rw[c] = char_cell(bv, c);
                }
                set_bits(&mut rw, 0, 6, (len as u128).saturating_sub(2));
                set_bits(&mut rw, 6, 6, 64u128.saturating_sub(len as u128));
            }
            // predecessor score (`predecessorAux`)
            if s == S_P {
                let acc: u128 = (0..=i)
                    .map(|j| sqd(get(&d.p, j) as i128, sys_b(j) as i128))
                    .sum();
                rw[ACC] = (acc % PM as u128) as u64;
                rw[P1] = p_score as u64;
                rw[ISYS] = inv_p(p_score);
            }
            // named receiver score (`namedAux`)
            if s == S_V {
                rw[ACC] = (0..=i).map(|j| b(is_hex_c(get(&d.v, j)))).sum();
                rw[VC0] = v0;
                rw[VC1] = v1;
                rw[H01] = h01;
                rw[P1] = pv1 as u64;
                rw[P2] = pv2 as u64;
                rw[P3] = pv3 as u64;
                rw[I1] = inv_p(pv1);
                rw[I2] = inv_p(pv2);
                rw[I3] = inv_p(pv3);
            }
            // system (`systemAux`, every row)
            rw[G_V] = b(s == S_V && d.system_lookup(i));
            rw[G_S] = b(s == S_S && d.system_lookup(i));
            rw[SX] = get(&d.v, i);
            rw[INV_D] = inv_pf(get(&d.s, i) as i128, get(&d.v, i) as i128);
            rw[SCNT] = d.system_lookup_count(i);
            rw[INV_L] = inv_pf(d.ls() as i128, d.lv() as i128);
            // routing (`routingAux`: `idx` on `sV`, `Lv` on the first `RID` row)
            if s == S_V || (s == S_RID && i == 0) {
                let pos = if s == S_V { i } else { d.lv() };
                let f = route_frame(d, pos);
                for c in 0..RCPT_WIDTH {
                    if routing_scratch(c) {
                        rw[c] = route_cell(&f, c);
                    }
                }
            }
            // key symbols and access key (`keyAux`)
            rw[T_A] = key_pos_a(d, s, i);
            rw[T_B] = key_pos_b(d, s, i);
            rw[SYM_A] = key_sym_a(d, s, i);
            rw[SYM_B] = key_sym_b(d, s, i);
            rw[LAST_A] = b(key_last(d, s, i));
            rw[G_KA] = b(key_gate_a(d, s, i));
            rw[G_KB] = b(key_gate_b(d, s, i));
            rw[KZ] = b(key_zero(s, i));
            rw[G_F] = b((s == S_PL && i == 0) || (d.system_equal() && s == S_T0));
            rw[FK_F] = b(s == S_T0 && access.is_none());
            rw[K_F] = if s == S_T0 {
                access.unwrap_or(0)
            } else {
                d.kslot
            };
            rw[G_AK] = b(d.system_equal() && s == S_T0 && access.is_some());
            if s == S_PK {
                let kb = key_byte(d, s, i);
                for j in 0..4 {
                    rw[xb(j)] = bit_of((kb / 16) as u128, j);
                    rw[xb(4 + j)] = bit_of((kb % 16) as u128, j);
                }
            }
            rw[UAK] = d.aku;
            // gas (`gasBorrowAux` … `gasProductAux`, `tokenAux` bits)
            if s == S_GP {
                rw[C1] = d.gas_borrow(bgp_b, i);
                set_bits(&mut rw, 0, 8, d.gas_diff(bgp_b, i) as u128);
                rw[xb(8)] = d.gas_borrow(bgp_b, i + 1);
                rw[PC] = get(&pcv, i);
                for j in 0..4 {
                    rw[dl(j)] = if j < i { get(&pcv, i - 1 - j) } else { 0 };
                    rw[dl(4 + j)] = if j < i { get(&sv, i - 1 - j) } else { 0 };
                }
                rw[SUM_D] = (0..=i).map(|k| d.gas_diff(bgp_b, k)).sum();
                rw[INV_A] = inv_a;
                rw[BURNT] = get(&burnt_b, i);
                rw[C4] = get(&tcv, i);
                rw[xb(39)] = get(&tcv, i + 1);
                set_bits(&mut rw, 31, 8, get(&tok_new, i) as u128);
                rw[RAMT] = get(&ramt_b, i);
                rw[C2] = get(&bcv, i);
                rw[C3] = get(&scv, i);
                set_bits(&mut rw, 9, 11, get(&bcv, i + 1) as u128);
                set_bits(&mut rw, 20, 11, get(&scv, i + 1) as u128);
            }
            // deposit (`depositAgeAux` ∘ `depositAux`)
            rw[R1] = b(s == S_DEP && i == 1);
            if s == S_DEP {
                dep_row(&mut rw, d, big, i);
            }
            rows.push(rw);
        }
    }
    rows
}

/// Deposit arithmetic (`depositAux`, `depositScratch`, `depositAgeAux`; `Seg.*`
/// of `nativeDepositData`).
fn dep_row(rw: &mut Row, d: &Rd, big: bool, i: usize) {
    let bef = le_n(&d.bef);
    let dep = le_n(&d.dep);
    let lk = le_n(&d.lk);
    let stor = le_n(&d.st);
    let bef_b = le_bytes(16, bef);
    let dep_b = le_bytes(16, dep);
    let lk_b = le_bytes(16, lk);
    let st_b = le_bytes(8, stor);
    let aft_b = le_bytes(16, bef.wrapping_add(dep));
    let tot_b = le_bytes(16, bef.wrapping_add(dep).wrapping_add(lk));
    let q_b = le_bytes(16, STORAGE_PER_BYTE.wrapping_mul(stor));
    let y1: Vec<u64> = (0..16).map(|k| get(&bef_b, k) + get(&dep_b, k)).collect();
    let y2: Vec<u64> = (0..16).map(|k| get(&aft_b, k) + get(&lk_b, k)).collect();
    let y3: Vec<u64> = (0..16).map(|k| conv(&S_LE, &st_b, k)).collect();
    let (c1, c2, c3) = (chain(&y1), chain(&y2), chain(&y3));
    let dbr = bchain(&tot_b, &q_b, 0);
    let run_a = |i: usize| -> u64 { (0..=i).map(|k| 255 - get(&aft_b, k)).sum() };
    rw[ST] = get(&st_b, i);
    rw[BEF] = get(&bef_b, i);
    rw[LK] = get(&lk_b, i);
    rw[C1] = get(&c1, i);
    rw[C2] = get(&c2, i);
    rw[C3] = get(&c3, i);
    rw[C4] = get(&dbr, i);
    rw[DSUM] = run_a(i);
    rw[INV_B] = inv_p(run_a(15) as u128);
    for j in 0..7 {
        rw[dl(j)] = if j < i { get(&st_b, i - 1 - j) } else { 0 };
    }
    set_bits(rw, 0, 8, get(&aft_b, i) as u128);
    rw[xb(8)] = get(&c1, i + 1);
    set_bits(rw, 9, 8, get(&tot_b, i) as u128);
    rw[xb(17)] = get(&c2, i + 1);
    set_bits(rw, 18, 8, get(&q_b, i) as u128);
    set_bits(rw, 26, 12, get(&c3, i + 1) as u128);
    // `ddv = bdig totB qB 0`
    let ddv = get(&tot_b, i) + 256 * get(&dbr, i + 1) - get(&q_b, i) - get(&dbr, i);
    set_bits(rw, 38, 8, ddv as u128);
    rw[xb(46)] = get(&dbr, i + 1);
    if i == 1 && !big {
        set_bits(rw, 47, 10, 770u128.saturating_sub(stor));
    }
    // deposit age (13 bits, `depositAgeAux`)
    if i == 0 {
        set_bits(rw, 53, 13, (d.r as u128).saturating_sub(d.tprev as u128));
    }
}

/// List-header rows (`headerCell` ∘ `headerStreamAux` ∘ `tokenHeaderAux`, 12 rows).
fn header_rows(
    own: u64,
    list_index: u64,
    receipt_index: u64,
    n: usize,
    body_offset: u64,
    before: u128,
    last_list: bool,
) -> Vec<Row> {
    let mut stream = le_bytes(8, own as u128);
    stream.extend(le_bytes(4, n as u128));
    let tok_old = le_bytes(16, before);
    let mut rows = Vec::with_capacity(12);
    for i in 0..12 {
        let mut rw = [0u64; RCPT_WIDTH];
        rw[ACT] = 1;
        rw[S_CL] = 1;
        rw[IDX] = i as u64;
        rw[FS] = b(i == 0);
        rw[FE] = b(i + 1 == 12);
        let le = i + 1 == 12 && n == 0;
        rw[LE] = b(le);
        rw[LAST_R] = b(le && last_list);
        rw[J] = list_index;
        rw[NJ] = n as u64;
        rw[R] = receipt_index;
        rw[O_END] = 12;
        rw[O2] = body_offset;
        rw[O2_END] = body_offset;
        for j in 0..32 {
            rw[reg(j)] = get(&stream, i + j);
        }
        rw[B] = get(&stream, i);
        for j in 0..16 {
            rw[tok(j)] = get(&tok_old, j);
        }
        rows.push(rw);
    }
    rows
}

// ---------------------------------------------------------------------------
// Renderer
// ---------------------------------------------------------------------------

/// `log` of the installed honest render (`rcptTraceAlignedQ_log`).
pub const RCPT_LOG: usize = 22;

/// The planned rows of the final trace plus the `uB` value of every padding row.
struct Rows {
    rows: Vec<Row>,
    pad_ub: u64,
}

/// `physicalBoundaryKey`: `(65·q + iB, loB, hiB, hnB)` (field values).
fn boundary_key(rw: &Row) -> [u64; 4] {
    [
        (65 * (rw[Q] % PM) + rw[I_B] % PM) % PM,
        rw[LO_B] % PM,
        rw[HI_B] % PM,
        rw[HN_B] % PM,
    ]
}

/// All planned rows: native rows (`plannedRows`), emission patch, BND counter
/// ranks (`counterPatch … physicalBoundaryRank`) and the `q` bits (`patchTrace`).
fn build(input: &RcptIn) -> Rows {
    let bgp_b = le_bytes(16, input.bgp);
    let bgp = input.bgp;
    let last_list_idx = input.lists.len().saturating_sub(1);
    let mut rows: Vec<Row> = Vec::new();
    // `planLists 0 0 8`: global `r`, global body offset from 8, burn prefix.
    let mut global_r: u64 = 0;
    let mut body_off: u64 = 8;
    let mut burnt: u128 = 0;
    for (j, list) in input.lists.iter().enumerate() {
        rows.extend(header_rows(
            input.own,
            j as u64,
            global_r,
            list.rs.len(),
            body_off,
            burnt,
            j == last_list_idx,
        ));
        // `planReceipts j nj r 1 12 o2`
        let mut o: u64 = 12;
        for (cj, e) in list.rs.iter().enumerate() {
            let (lo, hi) = interval_of(e);
            let d = Rd {
                p: e.p.clone(),
                v: e.v.clone(),
                s: e.s.clone(),
                rid: e.rid.clone(),
                kt: e.kt,
                pk: e.pk.clone(),
                gp: e.gp.clone(),
                dep: e.dep.clone(),
                ge: e.ge,
                hr: e.hr,
                sys: e.sys,
                kslot: e.kslot,
                tprev: e.tprev,
                bef: e.bef.clone(),
                lk: e.lk.clone(),
                st: e.st.clone(),
                rfid: e.rfid.clone(),
                peoh: e.peoh.clone(),
                akf: e.akf,
                akk: e.akk,
                aku: e.aku,
                q: e.q,
                lo,
                hi,
                r: global_r,
                j: j as u64,
                nj: list.rs.len() as u64,
                cj: cj as u64 + 1,
                o,
                o2: body_off,
                le: cj + 1 == list.rs.len(),
                last_r: cj + 1 == list.rs.len() && j == last_list_idx,
                before: burnt,
            };
            rows.extend(seg_rows(&d, input.height, bgp, &bgp_b));
            o += d.rc_len();
            body_off += d.refund_len();
            burnt += d.burn(bgp);
            global_r += 1;
        }
    }
    let ems = emits();
    for rw in rows.iter_mut() {
        fill_emits(&ems, rw);
    }
    // `counterPatch … physicalBoundaryRank`: rank among earlier selected rows.
    let mut used: std::collections::HashMap<[u64; 4], u64> = std::collections::HashMap::new();
    for rw in rows.iter_mut() {
        let key = boundary_key(rw);
        let sel = rw[G_BD] == 1;
        rw[U_B] = used.get(&key).copied().unwrap_or(0);
        if sel {
            *used.entry(key).or_insert(0) += 1;
        }
    }
    let pad_ub = used.get(&[0, 0, 0, 0]).copied().unwrap_or(0);
    // `patchTrace`: the first receiver row carries the bits of `q`.
    for rw in rows.iter_mut() {
        if rw[S_V] == 1 && rw[FS] == 1 {
            let qv = rw[Q];
            set_bits(rw, 12, 7, qv as u128);
        }
    }
    Rows { rows, pad_ub }
}

/// The number of planned rows (`(plannedRows lists).length`).
pub fn planned_rows(input: &RcptIn) -> usize {
    build(input).rows.len()
}

/// The honest trace at height `2^log` (planned rows, then padding with
/// `uB = pad_ub`).  Panics if the planned rows do not fit.
pub fn rcpt_at_log(input: &RcptIn, log: usize) -> Tab {
    let rs = build(input);
    let mut t = Tab::zero(log, RCPT_WIDTH);
    let h = t.height();
    assert!(
        rs.rows.len() <= h,
        "rcpt: {} rows exceed 2^{log}",
        rs.rows.len()
    );
    for (q, rw) in rs.rows.iter().enumerate() {
        for (c, x) in rw.iter().enumerate() {
            t.set(q, c, *x);
        }
    }
    if rs.pad_ub != 0 {
        for q in rs.rows.len()..h {
            t.set(q, U_B, rs.pad_ub);
        }
    }
    t
}

/// The installed honest trace (`rcptTraceAlignedQ`, height `2^22`).
pub fn rcpt_aligned(input: &RcptIn) -> Tab {
    rcpt_at_log(input, RCPT_LOG)
}

/// Parse `json` as the `RcptIn` input and render the aligned trace.
pub fn render(json: &str) -> Result<Tab, String> {
    let input: RcptIn = serde_json::from_str(json).map_err(|e| e.to_string())?;
    Ok(rcpt_aligned(&input))
}

/// The first `n` rows of the aligned trace in the `np-lean-render-v3-rcpt` prefix
/// format: u32 LE `log = 22, width, n`, then `n · width` cells (row-major).
pub fn render_prefix(json: &str, n: usize) -> Result<Vec<u8>, String> {
    let input: RcptIn = serde_json::from_str(json).map_err(|e| e.to_string())?;
    let rs = build(&input);
    let mut out = Vec::with_capacity(12 + 4 * n * RCPT_WIDTH);
    for x in [RCPT_LOG, RCPT_WIDTH, n] {
        out.extend_from_slice(&(x as u32).to_le_bytes());
    }
    for q in 0..n.min(1 << RCPT_LOG) {
        for c in 0..RCPT_WIDTH {
            let x = match rs.rows.get(q) {
                Some(rw) => rw[c],
                None if c == U_B => rs.pad_ub,
                None => 0,
            };
            out.extend_from_slice(&((x % PM) as u32).to_le_bytes());
        }
    }
    Ok(out)
}

/// The public vector the honest rows read (`RcptOk.gasPub`, `finalPub`,
/// `owner`): `PH_N` (receipt count), `PH_OWN`, `PH_HEIGHT`, `PH_GP`, `PH_BURNT`
/// (`Σ nativeBurn`) and `PH_BLEN` (`8 + Σ refundLength`); everything else `0`.
pub fn honest_pubs(input: &RcptIn, num_pub: usize) -> Vec<F> {
    let mut p = vec![F::ZERO; num_pub.max(PH_BLEN + 4)];
    let mut put = |at: usize, bs: Vec<u64>| {
        for (i, x) in bs.into_iter().enumerate() {
            p[at + i] = F::from_u64(x);
        }
    };
    let rs: Vec<&RcptE> = input.lists.iter().flat_map(|l| l.rs.iter()).collect();
    let mut burnt = 0u128;
    let mut blen = 8u128;
    for e in &rs {
        let price = if e.sys { 0 } else { le_n(&e.gp).min(input.bgp) };
        burnt += GAS_G * price;
        if e.hr {
            blen += 129 + 2 * e.s.len() as u128 + 32 * e.kt as u128;
        }
    }
    put(PH_N, le_bytes(4, rs.len() as u128));
    put(PH_OWN, le_bytes(8, input.own as u128));
    put(PH_HEIGHT, le_bytes(8, input.height as u128));
    put(PH_GP, le_bytes(16, input.bgp));
    put(PH_BURNT, le_bytes(16, burnt));
    put(PH_BLEN, le_bytes(4, blen));
    p
}

/// `npudr v3check … rcpt`: the honest trace at the compact height
/// `2^logOf(rows + 1)` (see the module doc) and its public vector.
pub fn check_render(json: &str, num_pub: usize) -> Result<(Tab, Vec<F>), String> {
    let input: RcptIn = serde_json::from_str(json).map_err(|e| e.to_string())?;
    let log = log_of(planned_rows(&input) + 1);
    Ok((rcpt_at_log(&input, log), honest_pubs(&input, num_pub)))
}

/// The SHA-side traffic of the honest `rcpt` rows (for the collectors,
/// `src/v3/collect.rs`), in row order:
///
/// * `bytes`: every `BYTES` send `(id, pos, value)` with a nonzero gate — the three
///   emission slots `(eId e, ePos e, eV e)` gated by `eG e` (`RcptV3.interactions`):
///   `RC(j)` (`K_RC + 16·j`, list bytes, consumed by `srcpV3`), `PEO(r)`, `LEAF(r)`,
///   `RID(r)` (`K_PEO`/`K_LEAF`/`K_RID + 16·r`, hashed by the SHA table) and the
///   refund body `(K_RF, pos, byte)` (public bus); the gate is `1` or `hr`, so each
///   message has multiplicity one;
/// * `digests`: every `DIGEST` receive `(dI, dL, reg0..31)` (gate `gDg`, the first
///   `XRI` / `XLH` row): `RID(r)` (length 48, the refund id) and `PEO(r)` (length
///   `37 + 32·hr + Lv`, `H(PEO(r))`).
#[derive(Clone, Debug, Default)]
pub struct ShaTraffic {
    pub bytes: Vec<[u64; 3]>,
    pub digests: Vec<(u64, u64, Vec<u64>)>,
}

/// [`ShaTraffic`] of `input` (built from the planned rows; padding sends nothing).
pub fn sha_traffic(input: &RcptIn) -> ShaTraffic {
    let rs = build(input);
    let mut t = ShaTraffic::default();
    for rw in &rs.rows {
        for e in 0..3 {
            if rw[e_g(e)] % PM != 0 {
                t.bytes
                    .push([rw[e_id(e)] % PM, rw[e_pos(e)] % PM, rw[e_v(e)] % PM]);
            }
        }
        if rw[G_DG] == 1 {
            t.digests.push((
                rw[D_I] % PM,
                rw[D_L] % PM,
                (0..32).map(|i| rw[reg(i)]).collect(),
            ));
        }
    }
    t
}

const PH_N: usize = 30;
const PH_OWN: usize = 34;
const PH_HEIGHT: usize = 50;
const PH_GP: usize = 58;
const PH_BURNT: usize = 178;
const PH_BLEN: usize = 194;

#[cfg(test)]
mod tests {
    use super::*;

    fn bytes_of(s: &str) -> Vec<u64> {
        s.bytes().map(|x| x as u64).collect()
    }

    /// One list, one ordinary named receipt in the interval `["alice", ∞)`.
    fn sample_input() -> RcptIn {
        let e = RcptE {
            p: bytes_of("alice"),
            v: bytes_of("alice"),
            s: bytes_of("alice"),
            rid: vec![7u64; 32],
            kt: 0,
            pk: vec![1u64; 32],
            gp: vec![0u64; 16],
            dep: vec![0u64; 16],
            hr: false,
            ge: true,
            kslot: 1,
            tprev: 0,
            bef: vec![0u64; 16],
            lk: vec![0u64; 16],
            st: vec![0u64; 16],
            rfid: vec![0u64; 32],
            peoh: vec![3u64; 32],
            iv: Some(Iv {
                lo: Some(bytes_of("alice")),
                hi: None,
            }),
            ..RcptE::default()
        };
        RcptIn {
            lists: vec![ListV3 {
                n0: 1,
                n1: 0,
                rs: vec![e],
            }],
            own: 0,
            height: 0,
            bgp: 0,
        }
    }

    fn one(e: RcptE, bgp: u128) -> RcptIn {
        RcptIn {
            lists: vec![ListV3 {
                n0: 1,
                n1: 0,
                rs: vec![e],
            }],
            own: 5,
            height: 77,
            bgp,
        }
    }

    fn air_table() -> crate::air::Table {
        let air_json = std::env::var("RCPT_AIR_JSON").unwrap_or_else(|_| {
            concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../conformance/out-v2/nearAirV3.json"
            )
            .to_string()
        });
        let txt = std::fs::read_to_string(&air_json).expect("nearAirV3.json");
        let air = crate::air::Air::from_json(&txt).expect("parse air");
        let idx = crate::v3::TABLES
            .iter()
            .find(|(n, _)| *n == "rcpt")
            .map(|p| p.1)
            .unwrap();
        let t = air.tables[idx].clone();
        assert_eq!(
            t.constraints.len(),
            900,
            "{air_json}: table 16 is not tableQ (882 + 18 exported)"
        );
        t
    }

    fn failing(input: &RcptIn) -> Vec<(usize, usize)> {
        let t = air_table();
        let json = serde_json::to_string(input).unwrap();
        let (tab, pubs) = check_render(&json, 202).unwrap();
        assert_eq!(tab.width, t.width);
        crate::check::failing_constraints(&t, &tab.to_matrix(), &pubs, 40)
    }

    fn check_against_air(input: &RcptIn) {
        let bad = failing(input);
        assert!(bad.is_empty(), "failing (constraint, row): {bad:?}");
    }

    #[test]
    fn header_and_first_segment() {
        let input = sample_input();
        let t = rcpt_at_log(&input, 10);
        assert_eq!(t.width, RCPT_WIDTH);
        let w = RCPT_WIDTH;
        assert_eq!(t.cells[S_CL], 1);
        assert_eq!(t.cells[ACT], 1);
        assert_eq!(t.cells[NJ], 1);
        assert_eq!(t.cells[e_id(0)] as u64, K_RC);
        let q = 12;
        assert_eq!(t.cells[q * w + S_PL], 1);
        assert_eq!(t.cells[q * w + RF], 1);
        assert_eq!(t.cells[q * w + LP], 5);
        assert_eq!(t.cells[q * w + O], 12);
        // first receiver row: `q = 0` bits, `uB` rank 0
        let v0 = (0..t.height())
            .find(|&r| t.cells[r * w + S_V] == 1)
            .unwrap();
        assert_eq!(t.cells[v0 * w + FS], 1);
        assert_eq!(t.cells[v0 * w + U_B], 0);
    }

    #[test]
    fn empty_list_is_twelve_rows() {
        let mut input = sample_input();
        input.lists[0].rs.clear();
        input.lists[0].n0 = 0;
        assert_eq!(planned_rows(&input), 12);
        let t = rcpt_at_log(&input, 4);
        assert_eq!(t.cells[11 * RCPT_WIDTH + LE], 1);
        assert_eq!(t.cells[11 * RCPT_WIDTH + LAST_R], 1);
        assert_eq!(t.cells[12 * RCPT_WIDTH + ACT], 0);
    }

    #[test]
    fn prefix_matches_table() {
        let input = sample_input();
        let json = serde_json::to_string(&input).unwrap();
        let n = planned_rows(&input) + 8;
        let pre = render_prefix(&json, n).unwrap();
        let t = rcpt_at_log(&input, log_of(n));
        assert_eq!(pre.len(), 12 + 4 * n * RCPT_WIDTH);
        for (k, ch) in pre[12..].chunks(4).enumerate() {
            assert_eq!(u32::from_le_bytes(ch.try_into().unwrap()), t.cells[k]);
        }
    }

    #[test]
    fn all_constraints_hold_on_one_receipt() {
        check_against_air(&sample_input());
    }

    #[test]
    fn all_constraints_hold_on_empty_list() {
        let mut input = sample_input();
        input.lists[0].rs.clear();
        input.lists[0].n0 = 0;
        check_against_air(&input);
    }

    #[test]
    fn all_constraints_hold_on_sampled_inputs() {
        use crate::v3::sample::Rng;
        for seed in 1..=30 {
            let input = crate::v3::sample::rcpt(&mut Rng::new(seed), seed as usize);
            check_against_air(&input);
        }
    }

    #[test]
    fn all_constraints_hold_on_refund_receipt() {
        let mut e = sample_input().lists[0].rs.remove(0);
        e.hr = true;
        e.gp = le_bytes(16, 100);
        e.dep = le_bytes(16, 100);
        e.rfid = vec![9u64; 32];
        e.iv = Some(Iv {
            lo: Some(bytes_of("al")),
            hi: Some(bytes_of("b")),
        });
        check_against_air(&one(e, 50));
    }

    /// The gas repair: a system receipt with gas price `u128::MAX` against block
    /// price `0` (`old_gas_surplus_top_zero`) is accepted by `tableR`.
    #[test]
    fn system_receipt_with_max_gas_price() {
        let mut e = sample_input().lists[0].rs.remove(0);
        e.sys = true;
        e.p = bytes_of("system");
        e.gp = vec![255u64; 16];
        check_against_air(&one(e, 0));
    }

    /// The deposit-age repair: a receipt at index `≥ 512` reading the initial
    /// account (`tprev = 0`) is accepted (13-bit age).
    #[test]
    fn deposit_age_beyond_nine_bits() {
        let mut input = sample_input();
        let e = input.lists[0].rs[0].clone();
        input.lists[0].rs = vec![e; 600];
        input.lists[0].n0 = 600 % 256;
        input.lists[0].n1 = 600 / 256;
        check_against_air(&input);
    }

    /// Two receipts with the same interval: the second receiver's lookups are
    /// ranked after the first's (`physicalBoundaryRank`).
    #[test]
    fn boundary_ranks_count_earlier_uses() {
        let mut input = sample_input();
        let e = input.lists[0].rs[0].clone();
        input.lists[0].rs = vec![e.clone(), e];
        input.lists[0].n0 = 2;
        check_against_air(&input);
        let t = rcpt_at_log(&input, 10);
        let w = RCPT_WIDTH;
        let firsts: Vec<usize> = (0..t.height())
            .filter(|&r| t.cells[r * w + S_V] == 1 && t.cells[r * w + FS] == 1)
            .collect();
        assert_eq!(firsts.len(), 2);
        assert_eq!(t.cells[firsts[0] * w + U_B], 0);
        assert_eq!(t.cells[firsts[1] * w + U_B], 1);
    }

    /// `qBoundR`: `q = 128` cannot be written in the seven scratch bits.
    #[test]
    fn q_128_violates() {
        let mut input = sample_input();
        input.lists[0].rs[0].q = 127;
        check_against_air(&input);
        input.lists[0].rs[0].q = 128;
        assert!(!failing(&input).is_empty());
    }

    /// A deposit age `≥ 2^13` does not fit the 13 age bits.
    #[test]
    fn deposit_age_8192_violates() {
        let mut input = sample_input();
        input.lists[0].rs[0].tprev = (PM - 8192) as u64; // r − tprev ≡ 8192 (mod P)
        let bad = failing(&input);
        assert!(!bad.is_empty());
    }

    /// The refund surplus is gated by `gq`: a non-refund flag on a surplus fails.
    #[test]
    fn missing_refund_flag_violates() {
        let mut e = sample_input().lists[0].rs.remove(0);
        e.gp = le_bytes(16, 100);
        assert!(!failing(&one(e, 50)).is_empty());
    }
}
