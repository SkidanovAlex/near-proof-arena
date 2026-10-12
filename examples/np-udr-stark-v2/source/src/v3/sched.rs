//! Honest scheduler trace generators for `nearAirV3` tables 11–15, the Rust
//! twins of the honest renders the D0a completeness proof uses
//! (`ZkFormal/NearV3/Render/CompleteV3.lean`, `sched_renders_on`):
//!
//! | table | idx | width | Lean render (all at the shared clock `2^22`) |
//! |---|---|---|---|
//! | `codec` | 11 | 91 | `codecCell (bs.map blkOf)` = `natCell ((allDescs Bs).map Desc.row) codecPad` (`Render/CodecRender.lean`, `CodecGen.lean`; rows = `Gen.codecRows` per block) |
//! | `scandist` | 12 | 119 | `ProcScanDistPhases.trace bs`: every run's `Gen.Scan.rows`, then every block's `(distribution b).rows`, zero padding |
//! | `proc` | 13 | 64 | `procTraceV3 rs` (`Render/PaddedProc.lean`): every run's `procVs`, the last run's `tailV` (or `padPV`), then `padPV` |
//! | `mem` | 14 | 18 | `MemConcatCells.trace rs`: every run's `Gen.Mem.rows`, zero padding |
//! | `cmp` | 15 | 33 | `cmpTraceAligned (requests bs)`: per block `run.cmps ++ codec cmps ++ dist cmps`, padding `b = 1` |
//!
//! The certificate renders tables 12–15 (and 11) over **all** scheduler
//! instances (`bs`, one block per instance `τ = 0, 1, …`), at the fixed height
//! `2^22` (`Candidates/SchedHeight`, `22 ≡ 1 mod 3`), independent of the row
//! count.  The JSON input is a list of blocks (`SchedIn`: a `Run` plus the
//! public/native data the codec and distribute rows read); a single `SchedIn`
//! object or a bare `Run` (or a list of bare `Run`s) is read as that list.
//!
//! Executable Lean twin: `conformance/RenderV3Sched.lean`
//! (`np-lean-render-v3-sched`), which also samples honest blocks with the
//! native scheduler (`ActualRun.run`).
use serde::Deserialize;

use p3_field::Field;
use p3_field::PrimeCharacteristicRing;
use p3_field::PrimeField32;

use crate::field::{F, P};

use super::{Tab, b, get};

// ---------------------------------------------------------------------------
// field helpers (`ZkFormal.NearV3.Sched.Gen.Common`)
// ---------------------------------------------------------------------------

/// `fneg x = (P − x % P) % P`.
fn fneg(x: u64) -> u64 {
    (P as u64 - x % P as u64) % P as u64
}

/// `fsub a b = (a % P + P − b % P) % P`.
fn fsub(a: u64, b: u64) -> u64 {
    (a % P as u64 + P as u64 - b % P as u64) % P as u64
}

/// `finv x`: the inverse of `x mod P` (`0 ↦ 0`).
fn finv(x: u64) -> u64 {
    F::from_u64(x % P as u64)
        .try_inverse()
        .unwrap_or(F::ZERO)
        .as_canonical_u32() as u64
}

/// `bit x b = x / 2^b % 2`.
fn bit(x: u64, k: u64) -> u64 {
    (x >> k) & 1
}

/// `getBit bm i` (`bm` is a list of bytes): bit `i % 8` of byte `i / 8`.
fn get_bit(bm: &[u64], i: u64) -> bool {
    (get(bm, (i / 8) as usize) >> (i % 8)) & 1 == 1
}

/// `b2n`.
fn n2(x: bool) -> u64 {
    b(x)
}

/// `List.getD i false` for a `List Bool`.
fn get_bool(xs: &[bool], i: u64) -> bool {
    xs.get(i as usize).copied().unwrap_or(false)
}

// ---------------------------------------------------------------------------
// JSON mirrors of the Lean `Gen.Run` structures (`Sched/Gen/Run.lean`)
// ---------------------------------------------------------------------------

/// A converted request (`Gen.CReq`).
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct CReq {
    pub cid: u64,
    pub s: u64,
    pub r: u64,
    pub link: u64,
    /// the 5-byte bitmap
    pub bm: Vec<u64>,
    /// set bit positions (`setBits`)
    pub bits: Vec<u64>,
    /// increases over `base` (`incsOf`)
    pub incs: Vec<u64>,
    /// `a2[link]` (allowance at conversion time)
    pub key: u64,
}

/// One processing step = one `sprV3` entry row (`Gen.Entry`).
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct Entry {
    pub x: u64,
    pub ts: u64,
    pub ein: u64,
    pub eout: u64,
    pub inc: u64,
    pub rem: u64,
    pub s: u64,
    pub r: u64,
    pub link: u64,
    #[serde(rename = "sbIn")]
    pub sb_in: u64,
    #[serde(rename = "sbOut")]
    pub sb_out: u64,
    #[serde(rename = "rbIn")]
    pub rb_in: u64,
    #[serde(rename = "rbOut")]
    pub rb_out: u64,
    #[serde(rename = "alIn")]
    pub al_in: u64,
    #[serde(rename = "alOut")]
    pub al_out: u64,
    #[serde(rename = "cS")]
    pub c_s: bool,
    #[serde(rename = "cR")]
    pub c_r: bool,
    #[serde(rename = "cL")]
    pub c_l: bool,
    pub ok: bool,
    pub push: bool,
    pub zn: u64,
}

/// One round (`Gen.RoundD`).
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct RoundD {
    #[serde(rename = "K")]
    pub k: u64,
    pub z: u64,
    #[serde(rename = "T")]
    pub t: u64,
    #[serde(rename = "Lr")]
    pub lr: u64,
    pub kst: u64,
    pub kend: u64,
    #[serde(rename = "Kq")]
    pub kq: u64,
    pub zq: u64,
    pub entries: Vec<Entry>,
}

/// A memory op row (`Gen.MOp`); `op = 1` READ, `op = 2` GRANT.
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct MOp {
    pub t: u64,
    pub op: u64,
    pub vin: u64,
    pub v: u64,
    pub wp: u64,
    pub w: u64,
    pub inc: u64,
    pub ok: bool,
    pub c: bool,
    pub sf: bool,
}

/// A memory segment (`Gen.Seg`); `vin0`/`v0`/`w0` are the INIT values.
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct Seg {
    pub addr: u64,
    #[serde(rename = "isL")]
    pub is_l: bool,
    pub al: bool,
    pub vin0: u64,
    pub v0: u64,
    pub w0: u64,
    pub ops: Vec<MOp>,
}

/// The ChaCha RNG state (`NearSpecV3.Rng`).
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct Rng {
    pub key: Vec<u64>,
    pub ctr: u64,
    pub buf: Vec<u64>,
}

/// The final process state (`NearV3.Sched.PState`).
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct PState {
    pub sb: Vec<u64>,
    pub rb: Vec<u64>,
    pub al: Vec<u64>,
    pub g: Vec<u64>,
    #[serde(default)]
    pub rng: Rng,
}

/// `Gen.Run` (`Sched/Gen/Run.lean:122`) — everything the honest scheduler
/// traces need, for one instance `τ`.
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct Run {
    pub tau: u64,
    pub n: u64,
    pub base: u64,
    #[serde(rename = "D")]
    pub d: u64,
    pub seed: Vec<u64>,
    pub key: Vec<u64>,
    pub a2: Vec<u64>,
    pub conv: Vec<CReq>,
    /// `used[cid][j]`: increase `j` of request `cid` is processed.
    #[serde(default)]
    pub used: Vec<Vec<bool>>,
    pub rounds: Vec<RoundD>,
    pub segs: Vec<Seg>,
    /// comparator messages `(x, y, b)` sent by the memory and process tables.
    #[serde(default)]
    pub cmps: Vec<(u64, u64, u64)>,
    /// RNG words drawn in total.
    #[serde(default)]
    pub kfin: u64,
    /// final process state (`processEv`).
    #[serde(default)]
    pub fin: PState,
}

/// The bandwidth-scheduler `Params` (`NearSpecV3.Params`).
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct Params {
    pub base: u64,
    #[serde(rename = "maxShardBandwidth")]
    pub max_shard_bandwidth: u64,
    #[serde(rename = "maxSingleGrant")]
    pub max_single_grant: u64,
    #[serde(rename = "maxReceiptSize")]
    pub max_receipt_size: u64,
    #[serde(rename = "maxAllowance")]
    pub max_allowance: u64,
}

/// The renderer input: a `Run` plus the public `InstPub` data the `scandist`
/// and `codec` generators read.  A bare `Run` JSON is accepted too (all extra
/// fields default).
#[derive(Clone, Debug, Default, Deserialize, serde::Serialize)]
pub struct SchedIn {
    pub run: Run,
    #[serde(default)]
    pub ids: Vec<u64>,
    #[serde(default)]
    pub allowed: Vec<bool>,
    #[serde(default)]
    pub params: Params,
    /// whether a canonical previous state is present
    #[serde(default)]
    pub present: bool,
    /// `vidV` of the `0x0f` read
    #[serde(default)]
    pub vid: u64,
    /// grid grants per link (`gbA`)
    #[serde(default)]
    pub gb: Vec<u64>,
    /// forwarding demands of instance 0 (`fwd`)
    #[serde(default)]
    pub fwd: Vec<(u64, u64)>,
    /// `sha256(all_shards)` bytes (`I.ash`)
    #[serde(default)]
    pub ash: Vec<u64>,
    /// canonical previous allowances `a0[k]` (`a0Canon n prev`, length `n²`)
    #[serde(default)]
    pub a0: Vec<u64>,
    /// previous sanity-hash bytes (`I.prev.sanityHash`), used when `present`
    #[serde(default)]
    pub prev_hash: Vec<u64>,
}

/// Parse `json` as the block list: a list of `SchedIn`, a list of bare `Run`s,
/// one `SchedIn`, or one bare `Run`.
pub fn parse_all(json: &str) -> Result<Vec<SchedIn>, String> {
    let v: serde_json::Value = serde_json::from_str(json).map_err(|e| e.to_string())?;
    let one = |v: serde_json::Value| -> Result<SchedIn, String> {
        if v.get("run").is_some() {
            serde_json::from_value::<SchedIn>(v).map_err(|e| e.to_string())
        } else {
            let run: Run = serde_json::from_value(v).map_err(|e| e.to_string())?;
            Ok(SchedIn {
                run,
                ..Default::default()
            })
        }
    };
    match v {
        serde_json::Value::Array(xs) => xs.into_iter().map(one).collect(),
        v => Ok(vec![one(v)?]),
    }
}

/// `log₂` of the scheduler tables' shared height (`SchedHeight.trace`).
pub const SCHED_LOG: usize = 22;

/// The table at the shared clock `2^22`: `rows`, then `pad(q)` (`None` = zero).
fn sched_tab(rows: &[Vec<u64>], width: usize, pad: impl Fn(usize) -> Option<Vec<u64>>) -> Tab {
    let mut t = Tab::zero(SCHED_LOG, width);
    let h = t.height();
    for (q, row) in rows.iter().enumerate().take(h) {
        for (c, &x) in row.iter().enumerate().take(width) {
            t.set(q, c, x);
        }
    }
    for q in rows.len().min(h)..h {
        if let Some(row) = pad(q) {
            for (c, &x) in row.iter().enumerate().take(width) {
                t.set(q, c, x);
            }
        }
    }
    t
}

// ---------------------------------------------------------------------------
// cmp — table 15, `Gen.Cmp` (`Sched/Gen/Cmp.lean`)
// ---------------------------------------------------------------------------

/// `Sched.Cmp.width` (= `nearAirV3` table 15).
pub const CMP_WIDTH: usize = 33;
const C_COL_ACT: usize = 0;
const C_COL_X: usize = 1;
const C_COL_Y: usize = 2;
const C_COL_B: usize = 3;
const C_NBITS: usize = 29;

/// `Gen.Cmp.row x y b`: `d = b·(x − y) + (1 − b)·(y − x − 1)` in 29 bits.
fn cmp_row(x: u64, y: u64, b: u64) -> Vec<u64> {
    let d = if b == 1 {
        x.saturating_sub(y)
    } else {
        y.saturating_sub(x).saturating_sub(1)
    };
    let mut a = vec![0u64; CMP_WIDTH];
    a[C_COL_ACT] = 1;
    a[C_COL_X] = x;
    a[C_COL_Y] = y;
    a[C_COL_B] = b;
    for i in 0..C_NBITS {
        a[4 + i] = bit(d, i as u64);
    }
    a
}

/// `cmpTraceAligned cmps` (`Render/PaddedSched.lean`): one row per comparison
/// (`Gen.Cmp.rows`), then `Gen.Cmp.padRow` (`b = 1`) up to `2^22`.
pub fn cmp_aligned(cmps: &[(u64, u64, u64)]) -> Tab {
    let rows: Vec<Vec<u64>> = cmps.iter().map(|&(x, y, b)| cmp_row(x, y, b)).collect();
    let mut pad = vec![0u64; CMP_WIDTH];
    pad[C_COL_B] = 1;
    sched_tab(&rows, CMP_WIDTH, |_| Some(pad.clone()))
}

/// `ProcNativeOldComparisonCapacity.requests bs`: per block, the run's memory
/// and process comparisons, the codec comparisons, then the distribute
/// comparisons.
pub fn cmp_requests(bs: &[SchedIn]) -> Vec<(u64, u64, u64)> {
    let mut out = Vec::new();
    for inp in bs {
        out.extend_from_slice(&inp.run.cmps);
        out.extend(codec_block(inp).1);
        if let Some(d) = dist_rows(inp) {
            out.extend(d.cmps);
        }
    }
    out
}

/// `npudr v3render cmp`.
pub fn cmp(json: &str) -> Result<Tab, String> {
    Ok(cmp_aligned(&cmp_requests(&parse_all(json)?)))
}

// ---------------------------------------------------------------------------
// mem — table 14, `Gen.Mem` (`Sched/Gen/Mem.lean`, `Tables/Mem.lean`)
// ---------------------------------------------------------------------------

/// `Sched.Mem.width` (= `nearAirV3` table 14).
pub const MEM_WIDTH: usize = 18;
const M_ACT: usize = 0;
const M_FST: usize = 1;
const M_LST: usize = 2;
const M_IS_RD: usize = 3;
const M_IS_GR: usize = 4;
const M_ADDR: usize = 5;
const M_T: usize = 6;
const M_TP: usize = 7;
const M_VIN: usize = 8;
const M_V: usize = 9;
const M_WP: usize = 10;
const M_W: usize = 11;
const M_AL: usize = 12;
const M_IS_L: usize = 13;
const M_INC: usize = 14;
const M_OK: usize = 15;
const M_CC: usize = 16;
const M_SF: usize = 17;

/// `OP_READ` / `OP_GRANT` (`Sched/Ids.lean`).
const OP_READ: u64 = 1;
const OP_GRANT: u64 = 2;

/// `Gen.Mem.segRows g`: the INIT row (`fst`), then the ops in time order.
fn mem_seg_rows(g: &Seg) -> Vec<Vec<u64>> {
    let mut base = vec![0u64; MEM_WIDTH];
    base[M_ACT] = 1;
    base[M_ADDR] = g.addr;
    base[M_AL] = n2(g.al);
    base[M_IS_L] = n2(g.is_l);
    let mut init = base.clone();
    init[M_FST] = 1;
    init[M_LST] = n2(g.ops.is_empty());
    init[M_VIN] = g.vin0;
    init[M_V] = g.v0;
    init[M_WP] = g.w0;
    init[M_W] = g.w0;
    init[M_INC] = g.w0;
    init[M_CC] = n2(g.is_l);
    let mut out = vec![init];
    let n_ops = g.ops.len();
    let mut t_prev = 0u64;
    for (i0, o) in g.ops.iter().enumerate() {
        let i = i0 + 1;
        let mut row = base.clone();
        row[M_LST] = n2(i == n_ops);
        row[M_IS_RD] = n2(o.op == OP_READ);
        row[M_IS_GR] = n2(o.op == OP_GRANT);
        row[M_T] = o.t;
        row[M_TP] = t_prev;
        row[M_VIN] = o.vin;
        row[M_V] = o.v;
        row[M_WP] = o.wp;
        row[M_W] = o.w;
        row[M_INC] = o.inc;
        row[M_OK] = n2(o.ok);
        row[M_CC] = n2(o.c);
        row[M_SF] = n2(o.sf);
        out.push(row);
        t_prev = o.t;
    }
    out
}

/// `Gen.Mem.rows R`: every segment's rows.
pub fn mem_rows(r: &Run) -> Vec<Vec<u64>> {
    let mut rows: Vec<Vec<u64>> = Vec::new();
    for g in &r.segs {
        rows.extend(mem_seg_rows(g));
    }
    rows
}

/// `MemConcatCells.trace rs`: every run's `Gen.Mem.rows`, zero padding, `2^22` rows.
pub fn mem_aligned(rs: &[&Run]) -> Tab {
    let rows: Vec<Vec<u64>> = rs.iter().flat_map(|r| mem_rows(r)).collect();
    sched_tab(&rows, MEM_WIDTH, |_| None)
}

/// `npudr v3render mem`.
pub fn mem(json: &str) -> Result<Tab, String> {
    let bs = parse_all(json)?;
    Ok(mem_aligned(&bs.iter().map(|b| &b.run).collect::<Vec<_>>()))
}

// ---------------------------------------------------------------------------
// proc — table 13, `Gen.Proc` (`Sched/Gen/Proc.lean`, `Tables/Proc.lean`)
// ---------------------------------------------------------------------------

/// `Sched.Proc.width` (= `nearAirV3` table 13).
pub const PROC_WIDTH: usize = 64;
const P_ACT: usize = 0;
const P_KK: usize = 1;
const P_KH: usize = 2;
const P_KE: usize = 3;
const P_TAU: usize = 4;
const P_COL_L: usize = 5; // + i, i < 16
const P_KC: usize = 21;
const P_KL: usize = 22;
const P_IKC: usize = 23;
const P_KQ: usize = 24;
const P_TQ: usize = 25;
const P_KQQ: usize = 26;
const P_ZQ: usize = 27;
const P_K: usize = 28;
const P_Z: usize = 29;
const P_ZK: usize = 30;
const P_IK: usize = 31;
const P_KEND: usize = 32;
const P_LR: usize = 33;
const P_T: usize = 34;
const P_X: usize = 35;
const P_TS: usize = 36;
const P_EIN: usize = 37;
const P_EOUT: usize = 38;
const P_INC: usize = 39;
const P_REM: usize = 40;
const P_IREM: usize = 41;
const P_LASTF: usize = 42;
const P_S: usize = 43;
const P_R: usize = 44;
const P_LINK: usize = 45;
const P_SBIN: usize = 46;
const P_SBOUT: usize = 47;
const P_RBIN: usize = 48;
const P_RBOUT: usize = 49;
const P_ALIN: usize = 50;
const P_ALOUT: usize = 51;
const P_CS: usize = 52;
const P_CR: usize = 53;
const P_CL: usize = 54;
const P_OK: usize = 55;
const P_IA: usize = 56;
const P_ZA: usize = 57;
const P_ZN: usize = 58;
const P_PM: usize = 59;
const P_LE: usize = 60;
const P_CG: usize = 61;
const P_CX: usize = 62;
const P_CY: usize = 63;

/// `Sched.T0` (`Sched/Ids.lean`).
const T0: u64 = 1_048_576;
/// `Sched.Proc.KSENT` (sentinel previous key after the key block).
const KSENT: u64 = 16_777_216;

/// `keyLimb seed k = seed[2k] + 256·seed[2k+1]`.
fn key_limb(seed: &[u64], k: u64) -> u64 {
    get(seed, (2 * k) as usize) + 256 * get(seed, (2 * k + 1) as usize)
}

/// `withKey R off`: set `colL i = limb (i + off) % 16`.
fn with_key(seed: &[u64], off: u64, a: &mut [u64]) {
    for i in 0..16u64 {
        a[P_COL_L + i as usize] = key_limb(seed, (i + off) % 16);
    }
}

/// `ikcPad = finv (fneg 15)`.
fn ikc_pad() -> u64 {
    finv(fneg(15))
}

/// `Gen.Proc.keyRow R k`.
fn proc_key_row(r: &Run, k: u64) -> Vec<u64> {
    let mut a = vec![0u64; PROC_WIDTH];
    with_key(&r.seed, k, &mut a);
    a[P_ACT] = 1;
    a[P_KK] = 1;
    a[P_TAU] = r.tau;
    a[P_KC] = k;
    a[P_KL] = n2(k == 15);
    a[P_IKC] = if k == 15 { 0 } else { finv(fsub(k, 15)) };
    a[P_SBIN] = get(&r.seed, (2 * k) as usize);
    a[P_SBOUT] = get(&r.seed, (2 * k + 1) as usize);
    a[P_KQ] = 0;
    a[P_TQ] = T0;
    a[P_KQQ] = KSENT;
    a[P_ZQ] = 0;
    a
}

/// `Gen.Proc.roundBase R rd`.
fn proc_round_base(r: &Run, rd: &RoundD) -> Vec<u64> {
    let mut a = vec![0u64; PROC_WIDTH];
    with_key(&r.seed, 0, &mut a);
    a[P_ACT] = 1;
    a[P_TAU] = r.tau;
    a[P_IKC] = ikc_pad();
    a[P_K] = rd.k;
    a[P_Z] = rd.z;
    a[P_ZK] = n2(rd.k == 0);
    a[P_IK] = finv(rd.k);
    a[P_KEND] = rd.kend;
    a[P_LR] = rd.lr;
    a[P_T] = rd.t;
    a
}

/// `Gen.Proc.roundRows R rd`: the header, then the entries.
fn proc_round_rows(r: &Run, rd: &RoundD) -> Vec<Vec<u64>> {
    let base = proc_round_base(r, rd);
    let mut header = base.clone();
    header[P_KH] = 1;
    header[P_KQ] = rd.kst;
    header[P_TQ] = rd.t;
    header[P_KQQ] = rd.kq;
    header[P_ZQ] = rd.zq;
    header[P_CG] = n2(rd.k != 0);
    header[P_CX] = rd.kq;
    header[P_CY] = rd.k + 1;
    let mut out = vec![header];
    let n = rd.entries.len();
    for (i, e) in rd.entries.iter().enumerate() {
        let last = i + 1 == n;
        let last_f = e.rem == 0;
        let mut row = base.clone();
        row[P_KE] = 1;
        row[P_KQ] = rd.kend;
        row[P_TQ] = rd.t + rd.lr;
        row[P_KQQ] = rd.k;
        row[P_ZQ] = rd.z;
        row[P_X] = e.x;
        row[P_TS] = e.ts;
        row[P_EIN] = e.ein;
        row[P_EOUT] = e.eout;
        row[P_INC] = e.inc;
        row[P_REM] = e.rem;
        row[P_IREM] = finv(e.rem);
        row[P_LASTF] = n2(last_f);
        row[P_S] = e.s;
        row[P_R] = e.r;
        row[P_LINK] = e.link;
        row[P_SBIN] = e.sb_in;
        row[P_SBOUT] = e.sb_out;
        row[P_RBIN] = e.rb_in;
        row[P_RBOUT] = e.rb_out;
        row[P_ALIN] = e.al_in;
        row[P_ALOUT] = e.al_out;
        row[P_CS] = n2(e.c_s);
        row[P_CR] = n2(e.c_r);
        row[P_CL] = n2(e.c_l);
        row[P_OK] = n2(e.ok);
        row[P_IA] = finv(e.al_out);
        row[P_ZA] = n2(e.al_out == 0);
        row[P_ZN] = e.zn;
        row[P_PM] = n2(e.ok && !last_f);
        row[P_LE] = n2(last);
        row[P_CG] = 1;
        row[P_CX] = if last { rd.t } else { rd.entries[i + 1].ts };
        row[P_CY] = e.ts + 1;
        out.push(row);
    }
    out
}

/// `Gen.Proc.tailRow R`: the first padding row (key register and instance
/// carries of the last round).
fn proc_tail_row(r: &Run) -> Vec<u64> {
    let (kq0, tq0, kqq0, zq0) = match r.rounds.last() {
        Some(rd) => (rd.kend, rd.t + rd.lr, rd.k, rd.z),
        None => (0, T0, KSENT, 0),
    };
    let mut a = vec![0u64; PROC_WIDTH];
    with_key(&r.seed, 0, &mut a);
    a[P_TAU] = r.tau;
    a[P_IKC] = ikc_pad();
    a[P_KQ] = kq0;
    a[P_TQ] = tq0;
    a[P_KQQ] = kqq0;
    a[P_ZQ] = zq0;
    a
}

/// `procVs R` (= `Gen.Proc.rows R`): the 16 key rows, then each round's rows.
pub fn proc_rows(r: &Run) -> Vec<Vec<u64>> {
    let mut rows: Vec<Vec<u64>> = Vec::new();
    for k in 0..16u64 {
        rows.push(proc_key_row(r, k));
    }
    for rd in &r.rounds {
        rows.extend(proc_round_rows(r, rd));
    }
    rows
}

/// `procTraceV3 rs` (`Render/PaddedProc.lean`, `ProcConcatGeometry.atRow`):
/// every run's `procVs`, then `tail rs` (the last run's `tailV`, or `padPV`
/// when there is no run), then `padPV` (`ikc = ikcPad`) up to `2^22`.
pub fn proc_aligned(rs: &[&Run]) -> Tab {
    let rows: Vec<Vec<u64>> = rs.iter().flat_map(|r| proc_rows(r)).collect();
    let n_rows = rows.len();
    let mut pad = vec![0u64; PROC_WIDTH];
    pad[P_IKC] = ikc_pad();
    let tail = match rs.last() {
        Some(r) => proc_tail_row(r),
        None => pad.clone(),
    };
    sched_tab(&rows, PROC_WIDTH, |q| {
        Some(if q == n_rows {
            tail.clone()
        } else {
            pad.clone()
        })
    })
}

/// `npudr v3render proc`.
pub fn proc(json: &str) -> Result<Tab, String> {
    let bs = parse_all(json)?;
    Ok(proc_aligned(&bs.iter().map(|b| &b.run).collect::<Vec<_>>()))
}

// ---------------------------------------------------------------------------
// scandist — table 12, `Gen.sdRows` = `Scan.rows ++ Dist.rows`
// (`Sched/Gen/Scan.lean`, `Sched/Gen/Dist.lean`, `Tables/{Scan,Dist}.lean`)
// ---------------------------------------------------------------------------

/// `Sched.ScanDist.width` (= `Dist.width`, `nearAirV3` table 12).
pub const SCANDIST_WIDTH: usize = 119;

// physical column layout (`Tables/Dist.lean`)
const D_ACT: usize = 0;
const D_KSH: usize = 1;
const D_KGH: usize = 2;
const D_KC: usize = 3;
const D_TAU: usize = 4;
const D_NN: usize = 5;
const D_KP: usize = 6;
const D_KS: usize = 7;
const D_SIDE: usize = 8;
const D_SHD: usize = 9;
const D_LNK: usize = 10;
const D_BY0: usize = 11;
const D_BY1: usize = 12;
const D_BY2: usize = 13;
const D_LLO: usize = 14;
const D_LHI: usize = 15;
const D_ALC: usize = 16;
const D_A: usize = 17;
const D_B: usize = 18;
const D_S: usize = 19;
const D_R: usize = 20;
const D_N1: usize = 21; // = adr
const D_L1: usize = 22; // = bv
const D_N2: usize = 23;
const D_L2: usize = 24;
const D_Q1: usize = 25;
const D_R1: usize = 26;
const D_BT1: usize = 27; // + i, 6
const D_Q2: usize = 33;
const D_R2: usize = 34;
const D_BT2: usize = 35; // + i, 6
const D_ICNT: usize = 41; // = ig2
const D_ZC: usize = 42; // = e2
const D_KP2: usize = 43; // = gb
const D_DA: usize = 44;
const D_DB: usize = 45;
const D_AL: usize = 46;
const D_IG1: usize = 47;
const D_E1: usize = 48;
const D_CX: usize = 49;
const D_CY: usize = 50;
const D_CB: usize = 51;
const D_CG: usize = 52;
const D_DLSG: usize = 53;
const D_DLRG: usize = 54;
const D_SL: usize = 55;
const D_EI: usize = 56;
const D_QB1: usize = 57; // + i, 23
const D_QB2: usize = 80; // + i, 23
const D_RB1: usize = 103; // + i, 6
const D_RB2: usize = 109; // + i, 6
// scan-only columns
const D_FQ: usize = 115;
const D_RE: usize = 116;
const D_US0: usize = 117;
const D_US1: usize = 118;

// `Tables/Scan.lean` named aliases into the physical layout
const S_Q: usize = D_SIDE; // `q i = fw i` = 8 + i
const S_CLO: usize = 13; // `fw 5`
const S_CHI: usize = 14; // `fw 6`
const S_S: usize = 15; // `fw 7`
const S_R: usize = 16; // `fw 8`
const S_BASE: usize = D_A;
const S_CID: usize = D_B;
const S_KEY: usize = D_S;
const S_DD: usize = D_R;
const S_LINK: usize = D_N1;
const S_Y: usize = D_N2;
const S_IY: usize = D_L2;
const S_Q0: usize = D_Q1;
const S_Q1: usize = D_Q2;
const S_B0: usize = D_BT1;
const S_B1: usize = D_BT1 + 1;
const S_U0: usize = D_BT1 + 2;
const S_U1: usize = D_BT1 + 3;
const S_E4: usize = D_BT1 + 4;
const S_ZK0: usize = D_BT1 + 5;
const S_RE: usize = D_RE;
const S_CUR: usize = D_DA;
const S_CM: usize = D_DB;
const S_IKEY: usize = D_IG1;
const S_J: usize = D_CX;
const S_M: usize = D_CY;

/// `byteOf x i = x / 256^i % 256`.
fn byte_of(x: u64, i: u32) -> u64 {
    x / 256u64.pow(i) % 256
}

/// `Gen.Scan.paramRow R`: the scan parameter row.
fn scan_param_row(r: &Run) -> Vec<u64> {
    let mut a = vec![0u64; SCANDIST_WIDTH];
    a[D_ACT] = 1;
    a[D_KP] = 1;
    a[D_TAU] = r.tau;
    a[D_NN] = r.n;
    a[S_BASE] = r.base;
    a[S_DD] = r.d;
    a[S_Q] = byte_of(r.base, 0);
    a[S_Q + 1] = byte_of(r.base, 1);
    a[S_Q + 2] = byte_of(r.base, 2);
    a[S_Q + 3] = byte_of(r.d, 0);
    a[S_Q + 4] = byte_of(r.d, 1);
    a[S_CLO] = byte_of(r.d, 2);
    a[S_CHI] = r.n;
    a
}

/// `Gen.Scan.reqRows R c`: 20 rows per converted request.
fn scan_req_rows(r: &Run, c: &CReq) -> Vec<Vec<u64>> {
    let used = r.used.get(c.cid as usize).cloned().unwrap_or_default();
    let mm = c.bits.len() as u64;
    let val_of = |pos: u64| r.base + r.d * (pos + 1) / 40;
    let mut out = Vec::with_capacity(20);
    let mut jj = 0u64;
    let mut cur = r.base;
    for rho in 0..20u64 {
        let yy = rho / 4;
        let uu = rho % 4;
        let pos = 8 * yy + 2 * uu;
        let bb0 = n2(get_bit(&c.bm, pos));
        let bb1 = n2(get_bit(&c.bm, pos + 1));
        let v0 = val_of(pos);
        let v1 = val_of(pos + 1);
        let cm = if bb0 == 1 { v0 } else { cur };
        let mut a = vec![0u64; SCANDIST_WIDTH];
        a[D_ACT] = 1;
        a[D_KS] = 1;
        a[D_FQ] = n2(rho == 0);
        a[D_TAU] = r.tau;
        a[D_NN] = r.n;
        a[S_BASE] = r.base;
        a[S_DD] = r.d;
        a[S_CID] = c.cid;
        a[S_CLO] = c.cid % 256;
        a[S_CHI] = c.cid / 256;
        a[S_S] = c.s;
        a[S_R] = c.r;
        a[S_LINK] = c.link;
        a[S_Q] = get(&c.bm, yy as usize) / 4u64.pow(uu as u32);
        for i in 1..5u64 {
            a[S_Q + i as usize] = get(&c.bm, (yy + i) as usize);
        }
        a[S_B0] = bb0;
        a[S_B1] = bb1;
        a[S_U0] = bit(uu, 0);
        a[S_U1] = bit(uu, 1);
        a[S_Y] = yy;
        a[S_IY] = if yy == 4 { 0 } else { finv(fsub(yy, 4)) };
        a[S_E4] = n2(yy == 4);
        a[S_RE] = n2(yy == 4 && uu == 3);
        a[S_Q0] = r.d * (pos + 1) / 40;
        a[S_Q1] = r.d * (pos + 2) / 40;
        a[D_R1] = r.d * (pos + 1) % 40;
        a[D_R2] = r.d * (pos + 2) % 40;
        for i in 0..6u64 {
            a[D_RB1 + i as usize] = bit(r.d * (pos + 1) % 40, i);
            a[D_RB2 + i as usize] = bit(r.d * (pos + 2) % 40, i);
        }
        for i in 0..23u64 {
            a[D_QB1 + i as usize] = bit(r.d * (pos + 1) / 40, i);
            a[D_QB2 + i as usize] = bit(r.d * (pos + 2) / 40, i);
        }
        a[S_CUR] = cur;
        a[S_CM] = cm;
        a[S_J] = jj;
        a[S_M] = mm;
        a[S_KEY] = c.key;
        a[S_IKEY] = finv(c.key);
        a[S_ZK0] = n2(c.key == 0);
        a[D_US0] = n2(bb0 == 1 && get_bool(&used, jj));
        a[D_US1] = n2(bb1 == 1 && get_bool(&used, jj + bb0));
        out.push(a);
        jj += bb0 + bb1;
        cur = if bb1 == 1 { v1 } else { cm };
    }
    out
}

/// `Gen.Scan.rows R`: the param row (if any request), then 20 rows per request.
fn scan_rows(r: &Run) -> Vec<Vec<u64>> {
    if r.conv.is_empty() {
        return Vec::new();
    }
    let mut out = vec![scan_param_row(r)];
    for c in &r.conv {
        out.extend(scan_req_rows(r, c));
    }
    out
}

/// `indexOf ids s`: the first index, or `None`.
fn index_of(ids: &[u64], s: u64) -> Option<usize> {
    ids.iter().position(|&x| x == s)
}

/// `tgt ids k`: the link index of record `k` (`Spec/CanonDup.lean`; Lean's
/// `x / 0 = x % 0`-style totality: `k / 0 = 0`, `k % 0 = k`).
fn tgt(ids: &[u64], k: u64) -> u64 {
    let n = ids.len() as u64;
    let (q, m) = if n == 0 { (0, k) } else { (k / n, k % n) };
    let a = index_of(ids, get(ids, q as usize)).unwrap_or(0) as u64;
    let b_ = index_of(ids, get(ids, m as usize)).unwrap_or(0) as u64;
    a * n + b_
}

/// The source map of a layout for links `l < upto`: `src[l] = srcOf ids l`
/// (the last record `k < |ids|²` with `tgt ids k = l`) and `is_src[k]` = some
/// link `l < upto` has `srcOf ids l = some k` (`srcFields`' `use`, the codec's
/// `useC`).
struct SrcMap {
    src: Vec<Option<u64>>,
    is_src: Vec<bool>,
}

impl SrcMap {
    fn new(ids: &[u64], upto: u64) -> SrcMap {
        let nn = (ids.len() * ids.len()) as u64;
        let mut src = vec![None; upto as usize];
        for k in 0..nn {
            let l = tgt(ids, k);
            if l < upto {
                src[l as usize] = Some(k);
            }
        }
        let mut is_src = vec![false; nn.max(upto) as usize];
        for &k in src.iter().flatten() {
            is_src[k as usize] = true;
        }
        SrcMap { src, is_src }
    }
    fn src(&self, l: u64) -> Option<u64> {
        self.src.get(l as usize).copied().flatten()
    }
    fn used(&self, k: u64) -> bool {
        self.is_src.get(k as usize).copied().unwrap_or(false)
    }
}

/// `Gen.srcFields ids l = b2 src ++ [hasSrc, use]` (`use`: `l` is the source
/// of some link).
fn src_fields(m: &SrcMap, l: u64) -> [u64; 4] {
    let src = m.src(l);
    let s = src.unwrap_or(0);
    [s % 256, s / 256 % 256, n2(src.is_some()), n2(m.used(l))]
}

/// `Gen.cntS n allowed s` (allowed links of sender `s`).
fn cnt_s(n: u64, allowed: &[bool], s: u64) -> u64 {
    (0..n).filter(|&r| get_bool(allowed, s * n + r)).count() as u64
}

/// `Gen.cntR n allowed r`.
fn cnt_r(n: u64, allowed: &[bool], r: u64) -> u64 {
    (0..n).filter(|&s| get_bool(allowed, s * n + r)).count() as u64
}

/// `Gen.budget0 P side x = maxShardBandwidth − base·cnt` (`n = |P.ids|`).
fn budget0(p: &Params, side: u64, x: u64, n: u64, allowed: &[bool]) -> u64 {
    let c = if side == 0 {
        cnt_s(n, allowed, x)
    } else {
        cnt_r(n, allowed, x)
    };
    p.max_shard_bandwidth.saturating_sub(p.base * c)
}

/// `Gen.avgOf links left`.
fn avg_of(links: u64, left: u64) -> u64 {
    if links == 0 { 0 } else { left / links }
}

/// `Gen.Dist.bitsOf col x`: the six bits of `x` at `col … col+5`.
fn set_bits_of(a: &mut [u64], col: usize, x: u64) {
    for i in 0..6u64 {
        a[col + i as usize] = bit(x, i);
    }
}

/// `Gen.Dist.bitsN col len x`.
fn set_bits_n(a: &mut [u64], col: usize, len: u64, x: u64) {
    for i in 0..len {
        a[col + i as usize] = bit(x, i);
    }
}

/// `Gen.DistOut`: the distribute rows, the grid grant per link, the
/// comparator messages.
pub struct DistOut {
    pub rows: Vec<Vec<u64>>,
    pub gb: Vec<u64>,
    pub cmps: Vec<(u64, u64, u64)>,
}

/// `Gen.distRows I R`: the shard rows (senders then receivers, sorted), then
/// the grid (a header and `n` cells per sender position).  `None` where the
/// Lean generator throws (`sort order`, `distribute break`);
/// `ProcNativeOldComparisonCapacity.distribution` then uses the empty output.
fn dist_rows(inp: &SchedIn) -> Option<DistOut> {
    let r = &inp.run;
    let n = r.n;
    let tv = r.tau;
    let allowed = &inp.allowed;
    let n_ids = inp.ids.len() as u64;
    let sm = SrcMap::new(&inp.ids, n_ids * n_ids);
    let sb = &r.fin.sb;
    let rb = &r.fin.rb;
    let count = |sd: u64, x: u64| {
        if sd == 0 {
            cnt_s(n, allowed, x)
        } else {
            cnt_r(n, allowed, x)
        }
    };
    let leftv = |sd: u64, x: u64| {
        if sd == 0 {
            get(sb, x as usize)
        } else {
            get(rb, x as usize)
        }
    };
    let cmp_of = |x: u64, y: u64| (x, y, n2(y <= x));
    // stable sort by `avg` (`sortByKey`)
    let sord: Vec<u64> = sort_by_key(|s| avg_of(count(0, s), leftv(0, s)), n);
    let rord: Vec<u64> = sort_by_key(|x| avg_of(count(1, x), leftv(1, x)), n);

    let mut rows: Vec<Vec<u64>> = Vec::new();
    let mut cmps: Vec<(u64, u64, u64)> = Vec::new();
    // shard rows
    for sd in 0..2u64 {
        let ord = if sd == 0 { &sord } else { &rord };
        let mut kpv = 0u64;
        for i in 0..n {
            let x = ord[i as usize];
            let c = count(sd, x);
            let left = leftv(sd, x);
            let b0 = budget0(&inp.params, sd, x, n_ids, allowed);
            let q = avg_of(c, left);
            let rem = if c == 0 { 0 } else { left % c };
            let key = q * 64 + x;
            if kpv > key {
                return None; // `check (kpv ≤ key) "sort order"`
            }
            cmps.push(cmp_of(key, kpv));
            let e1v = if i + 1 == n { 1 } else { 0 };
            let mut a = vec![0u64; SCANDIST_WIDTH];
            a[D_ACT] = 1;
            a[D_KSH] = 1;
            a[D_TAU] = tv;
            a[D_NN] = n;
            a[D_SIDE] = sd;
            a[D_A] = i;
            a[D_R] = x;
            a[D_N2] = c;
            a[D_L2] = left;
            a[D_BY0] = byte_of(b0, 0);
            a[D_BY1] = byte_of(b0, 1);
            a[D_BY2] = byte_of(b0, 2);
            a[D_Q2] = q;
            a[D_R2] = rem;
            a[D_ICNT] = finv(c);
            a[D_ZC] = n2(c == 0);
            a[D_KP2] = kpv;
            a[D_DA] = if sd == 0 { i } else { 0 };
            a[D_DB] = if sd == 0 { 255 } else { i };
            a[D_CX] = key;
            a[D_CY] = kpv;
            a[D_CB] = 1;
            a[D_CG] = 1;
            a[D_DLSG] = 1;
            a[D_SL] = left;
            a[D_E1] = e1v;
            a[D_SHD] = x;
            a[D_LNK] = c;
            a[D_LLO] = n;
            a[D_N1] = 4096 * (sd + 1) + x;
            a[D_L1] = b0;
            a[D_IG1] = finv(fsub(i, n.saturating_sub(1)));
            if c != 0 {
                set_bits_of(&mut a, D_BT2, c - 1 - rem);
            }
            set_bits_n(&mut a, D_QB2, 23, q);
            set_bits_n(&mut a, D_RB2, 6, rem);
            rows.push(a);
            kpv = key + 1;
        }
    }
    // grid
    let mut gb_arr = vec![0u64; (n * n) as usize];
    let mut ri: Vec<(u64, u64)> = (0..n).map(|x| (count(1, x), leftv(1, x))).collect();
    for i in 0..n {
        let sv = sord[i as usize];
        let mut se = (count(0, sv), leftv(0, sv));
        let mut header = vec![0u64; SCANDIST_WIDTH];
        header[D_ACT] = 1;
        header[D_KGH] = 1;
        header[D_TAU] = tv;
        header[D_NN] = n;
        header[D_A] = i;
        header[D_B] = 255;
        header[D_R] = sv;
        header[D_N2] = se.0;
        header[D_L2] = se.1;
        header[D_DLRG] = 1;
        rows.push(header);
        for j in 0..n {
            let rr = rord[j as usize];
            let l = sv * n + rr;
            let re = ri[rr as usize];
            let alv = get_bool(allowed, l);
            if alv && (se.0 == 0 || re.0 == 0) {
                return None; // `check (se.1 ≥ 1 && re.1 ≥ 1) "distribute break"`
            }
            let (q1v, r1v, q2v, r2v, gbv) = if alv {
                let q1v = se.1 / se.0;
                let q2v = re.1 / re.0;
                (q1v, se.1 % se.0, q2v, re.1 % re.0, q1v.min(q2v))
            } else {
                (0, 0, 0, 0, 0)
            };
            if alv {
                cmps.push(cmp_of(q1v, q2v));
            }
            let cbv = n2(alv && q2v <= q1v);
            let n2v = re.0 - n2(alv);
            let l2v = re.1.saturating_sub(gbv);
            let e1v = if j + 1 == n { 1 } else { 0 };
            let e2v = if i + 1 == n { 1 } else { 0 };
            let sf = src_fields(&sm, l);
            let mut a = vec![0u64; SCANDIST_WIDTH];
            a[D_ACT] = 1;
            a[D_KC] = 1;
            a[D_TAU] = tv;
            a[D_NN] = n;
            a[D_A] = i;
            a[D_B] = j;
            a[D_S] = sv;
            a[D_R] = rr;
            a[D_N1] = se.0;
            a[D_L1] = se.1;
            a[D_N2] = re.0;
            a[D_L2] = re.1;
            a[D_Q1] = q1v;
            a[D_R1] = r1v;
            a[D_Q2] = q2v;
            a[D_R2] = r2v;
            a[D_LLO] = l % 256;
            a[D_LHI] = l / 256;
            a[D_AL] = n2(alv);
            a[D_ALC] = n2(alv);
            a[D_SIDE] = sf[0];
            a[D_SHD] = sf[1];
            a[D_LNK] = sf[2];
            a[D_BY0] = sf[3];
            a[D_KP2] = gbv;
            a[D_CX] = q1v;
            a[D_CY] = q2v;
            a[D_CB] = cbv;
            a[D_CG] = n2(alv);
            a[D_DA] = i + 1;
            a[D_DB] = j;
            a[D_SL] = l2v;
            a[D_DLSG] = 1 - e2v;
            a[D_DLRG] = 1;
            a[D_E1] = e1v;
            a[D_IG1] = finv(fsub(j, n - 1));
            a[D_ZC] = e2v;
            a[D_ICNT] = finv(fsub(i, n - 1));
            a[D_EI] = e1v * e2v;
            if alv {
                set_bits_of(&mut a, D_BT1, se.0 - 1 - r1v);
                set_bits_of(&mut a, D_BT2, re.0 - 1 - r2v);
            }
            set_bits_n(&mut a, D_QB1, 23, q1v);
            set_bits_n(&mut a, D_QB2, 23, q2v);
            set_bits_n(&mut a, D_RB1, 6, r1v);
            set_bits_n(&mut a, D_RB2, 6, r2v);
            rows.push(a);
            if alv {
                gb_arr[l as usize] = gbv;
                se = (se.0 - 1, se.1 - gbv);
            }
            ri[rr as usize] = (n2v, l2v);
        }
    }
    Some(DistOut {
        rows,
        gb: gb_arr,
        cmps,
    })
}

/// `sortByKey key (List.range n)`: stable insertion sort.
fn sort_by_key(key: impl Fn(u64) -> u64, n: u64) -> Vec<u64> {
    fn insert(key: &impl Fn(u64) -> u64, x: u64, out: &mut Vec<u64>) {
        let kx = key(x);
        let at = out.iter().position(|&y| kx < key(y));
        match at {
            Some(i) => out.insert(i, x),
            None => out.push(x),
        }
    }
    let mut out: Vec<u64> = Vec::with_capacity(n as usize);
    for x in 0..n {
        insert(&key, x, &mut out);
    }
    out
}

/// `ProcScanDistPhases.rows bs`: every run's scan rows, then every block's
/// distribute rows (`distribution b`, empty when the generator throws).
pub fn scandist_rows(bs: &[SchedIn]) -> Vec<Vec<u64>> {
    let mut rows: Vec<Vec<u64>> = bs.iter().flat_map(|b| scan_rows(&b.run)).collect();
    for b in bs {
        if let Some(d) = dist_rows(b) {
            rows.extend(d.rows);
        }
    }
    rows
}

/// `ProcScanDistPhases.trace bs` (= `ssdCell bs`): the merged rows, zero
/// padding (`distPad`), `2^22` rows.
pub fn scandist_aligned(bs: &[SchedIn]) -> Tab {
    sched_tab(&scandist_rows(bs), SCANDIST_WIDTH, |_| None)
}

/// `npudr v3render scandist`.
pub fn scandist(json: &str) -> Result<Tab, String> {
    Ok(scandist_aligned(&parse_all(json)?))
}

// ---------------------------------------------------------------------------
// codec — table 11, `Gen.Codec.codecRows` (`Sched/Gen/Codec.lean`, `Tables/Codec.lean`)
// ---------------------------------------------------------------------------

/// `Sched.Codec.width` (= `nearAirV3` table 11).
pub const CODEC_WIDTH: usize = 91;
const CO_ACT: usize = 0;
const CO_KH: usize = 1;
const CO_KR: usize = 2;
const CO_KZ: usize = 3;
const CO_KA: usize = 4;
const CO_KF: usize = 5;
const CO_TAU: usize = 6;
const CO_POS: usize = 7;
const CO_PRES: usize = 8;
const CO_VID: usize = 9;
const CO_NN: usize = 10;
const CO_NN2: usize = 11;
const CO_BASE: usize = 12;
const CO_FAIR: usize = 13;
const CO_BPRE: usize = 14;
const CO_BPOST: usize = 15;
const CO_PBIT: usize = 16; // + i, 8
const CO_KIDX: usize = 24;
const CO_KLO: usize = 25;
const CO_KHI: usize = 26;
const CO_FS: usize = 27;
const CO_FR: usize = 28;
const CO_FA: usize = 29;
const CO_G: usize = 30;
const CO_IG7: usize = 31;
const CO_E7: usize = 32;
const CO_IG2: usize = 33;
const CO_E2: usize = 34;
const CO_LOWF: usize = 35;
const CO_WT: usize = 36;
const CO_AP: usize = 37;
const CO_BIG: usize = 38;
const CO_IB: usize = 39;
const CO_NZB: usize = 40;
const CO_APOST: usize = 41;
const CO_IKL: usize = 42;
const CO_EKL: usize = 43;
const CO_IHP: usize = 44;
const CO_EHP: usize = 45;
const CO_SJ: usize = 46;
const CO_ISJ: usize = 47;
const CO_ESJ: usize = 48;
const CO_BSHA: usize = 49;
const CO_FB: usize = 50; // + i, 3
const CO_AL: usize = 58;
const CO_A1: usize = 59;
const CO_CB: usize = 60;
const CO_AFIN: usize = 61;
const CO_GFIN: usize = 62;
const CO_GB: usize = 63;
const CO_ITZ: usize = 64;
const CO_ZT: usize = 65;
const CO_CX: usize = 66;
const CO_CY: usize = 67;
const CO_CBIT: usize = 68;
const CO_CG: usize = 69;
const CO_REND: usize = 70;
const CO_A2: usize = 71;
const CO_G2: usize = 72;
const CO_VBG: usize = 73;
const CO_FWG: usize = 74;
const CO_PM0: usize = 75;
const CO_PM1: usize = 76;
const CO_DGG: usize = 77;
const CO_BF: usize = 78;
const CO_PRBIT: usize = 79; // + i, 8
const CO_SRC_C: usize = 87;
const CO_APR: usize = 88;
const CO_HAS_C: usize = 89;
const CO_BIGR: usize = 90;

/// `Sched.Codec.MA` (`max_allowance`, PV 86).
const MA: u64 = 4_500_000;

/// The 32-byte register: the first 31 are overlaid record columns, the last is 53.
const CO_REG: [usize; 32] = [
    CO_KIDX, CO_KLO, CO_KHI, CO_G, CO_IG7, CO_IG2, CO_WT, CO_AP, CO_IB, CO_APOST, CO_IKL, CO_A1,
    CO_AFIN, CO_GFIN, CO_GB, CO_A2, CO_G2, CO_CX, CO_CY, 50, 51, 52, CO_LOWF, CO_NZB, CO_AL, CO_CB,
    CO_BF, CO_SRC_C, CO_APR, CO_HAS_C, CO_BIGR, 53,
];

/// `bytesLE x len`.
fn bytes_le(x: u64, len: usize) -> Vec<u64> {
    (0..len).map(|i| byte_of(x, i as u32)).collect()
}

/// `Gen.idByte ids k o` (`k / 0 = 0`, `k % 0 = k`).
fn id_byte(ids: &[u64], k: u64, o: u64) -> u64 {
    let n = ids.len() as u64;
    let (q, m) = if n == 0 { (0, k) } else { (k / n, k % n) };
    let id = if o < 8 {
        get(ids, q as usize)
    } else {
        get(ids, m as usize)
    };
    id / 256u64.pow((o % 8) as u32) % 256
}

/// The codec rows of one block (`Blk.descs (blkOf b)`, `Render/CodecGen.lean`,
/// = the rows of `Gen.codecRows I R present vidV gbA fwd`) and its comparator
/// messages (the `SCMP` sends: `(apR + fair, MA, cb)` on each allowance
/// field's `g = 2` row, `(gfin + gb, ft, 1)` on each record end of instance 0).
fn codec_rows(inp: &SchedIn, gb_a: &[u64]) -> (Vec<Vec<u64>>, Vec<(u64, u64, u64)>) {
    let r = &inp.run;
    let n = r.n;
    let nn = n * n;
    let tv = r.tau;
    let present = inp.present;
    // `maxShardBandwidth / n` with Lean's `x / 0 = 0`
    let fair_v = if n == 0 {
        0
    } else {
        inp.params.max_shard_bandwidth / n
    };
    let sm = SrcMap::new(&inp.ids, nn);
    let mut cmps: Vec<(u64, u64, u64)> = Vec::new();
    let base_v = inp.params.base;
    let a0 = &inp.a0;
    let hpre: Vec<u64> = if present {
        inp.prev_hash.clone()
    } else {
        vec![0; 32]
    };
    let mut sha_in = hpre.clone();
    sha_in.extend_from_slice(&inp.ash);
    let digest: Vec<u64> =
        crate::near::reexec::sha256(&sha_in.iter().map(|&x| x as u8).collect::<Vec<u8>>())
            .iter()
            .map(|&x| x as u64)
            .collect();

    let afin_f = |k: u64| -> u64 {
        match r.segs.get(k as usize) {
            Some(g) => g.ops.last().map(|o| o.v).unwrap_or(g.v0),
            None => 0,
        }
    };
    let gfin_f = |k: u64| -> u64 {
        match r.segs.get(k as usize) {
            Some(g) => g.ops.last().map(|o| o.w).unwrap_or(g.w0),
            None => 0,
        }
    };

    fn set_bits(a: &mut [u64], col: usize, x: u64) {
        for i in 0..8usize {
            a[col + i] = bit(x, i as u64);
        }
    }

    let inst: [(usize, u64); 10] = [
        (CO_ACT, 1),
        (CO_TAU, tv),
        (CO_PRES, n2(present)),
        (CO_VID, inp.vid),
        (CO_NN, n),
        (CO_NN2, nn),
        (CO_BASE, base_v),
        (CO_FAIR, fair_v),
        (CO_ITZ, finv(tv)),
        (CO_ZT, if tv == 0 { 1 } else { 0 }),
    ];

    let mut rows: Vec<Vec<u64>> = Vec::new();

    // header
    let hdr = [0u64, nn % 256, nn / 256 % 256, 0, 0];
    let params: Vec<u64> = {
        let mut p = hdr.to_vec();
        p.extend(bytes_le(base_v, 3));
        p.extend(bytes_le(fair_v, 3));
        p
    };
    for p in 0..5usize {
        let bp = hdr[p];
        let mut a = vec![0u64; CODEC_WIDTH];
        for &(c, v) in &inst {
            a[c] = v;
        }
        a[CO_KH] = 1;
        a[CO_KF] = if p == 0 { 1 } else { 0 };
        a[CO_POS] = p as u64;
        a[CO_BPOST] = bp;
        a[CO_BPRE] = if present { bp } else { 0 };
        a[CO_VBG] = n2(present);
        a[CO_IHP] = finv(fsub(p as u64, 4));
        a[CO_EHP] = if p == 4 { 1 } else { 0 };
        for i in 0..32usize {
            a[CO_REG[i]] = get(&params, p + i);
        }
        set_bits(&mut a, CO_PBIT, bp);
        set_bits(&mut a, CO_PRBIT, if present { bp } else { 0 });
        rows.push(a);
    }

    // records
    for kk in 0..nn {
        for f in 0..3u64 {
            let mut apv = 0u64;
            let mut apostv = 0u64;
            let mut bigv = 0u64;
            let mut cbv = 0u64;
            for gg in 0..8u64 {
                let p = 5 + 24 * kk + 8 * f + gg;
                let bpo = if f < 2 {
                    id_byte(&inp.ids, kk, 8 * f + gg)
                } else if gg < 3 {
                    afin_f(kk) / 256u64.pow(gg as u32) % 256
                } else {
                    0
                };
                let bpr = if !present {
                    0
                } else if f < 2 {
                    bpo
                } else {
                    get(a0, kk as usize) / 256u64.pow(gg as u32) % 256
                };
                let lowfv = if gg < 3 { 1 } else { 0 };
                let wtv = 256u64.pow(gg as u32);
                let nzbv = if bpr == 0 { 0 } else { 1 };
                let is_end = f == 2 && gg == 7;
                let src_o = sm.src(kk);
                let use_v = sm.used(kk);
                let a0s = match src_o {
                    Some(k2) => {
                        if present {
                            get(a0, k2 as usize)
                        } else {
                            0
                        }
                    }
                    None => 0,
                };
                let ap_rv = a0s % 16_777_216;
                let big_rv = if a0s >= 16_777_216 { 1 } else { 0 };
                let alv = n2(get_bool(&inp.allowed, kk));
                let gbv = get(gb_a, kk as usize);

                let mut a = vec![0u64; CODEC_WIDTH];
                for &(c, v) in &inst {
                    a[c] = v;
                }
                a[CO_KR] = 1;
                a[CO_POS] = p;
                a[CO_BPOST] = bpo;
                a[CO_BPRE] = bpr;
                a[CO_VBG] = n2(present);
                a[CO_KIDX] = kk;
                a[CO_KLO] = kk % 256;
                a[CO_KHI] = kk / 256;
                a[CO_FS] = if f == 0 { 1 } else { 0 };
                a[CO_FR] = if f == 1 { 1 } else { 0 };
                a[CO_FA] = if f == 2 { 1 } else { 0 };
                a[CO_G] = gg;
                a[CO_IG7] = finv(fsub(gg, 7));
                a[CO_E7] = if gg == 7 { 1 } else { 0 };
                a[CO_IKL] = finv(fsub(kk, nn - 1));
                a[CO_EKL] = if kk + 1 == nn { 1 } else { 0 };
                set_bits(&mut a, CO_PBIT, bpo);
                set_bits(&mut a, CO_PRBIT, bpr);
                a[54] = if f == 0 && gg == 0 { 1 } else { 0 }; // `rs`
                a[CO_AL] = alv;
                a[CO_GB] = gbv;
                a[CO_SRC_C] = src_o.unwrap_or(0);
                a[CO_HAS_C] = n2(src_o.is_some());
                a[57] = n2(use_v); // `useC`
                if f == 2 && gg >= 2 {
                    a[CO_APR] = ap_rv;
                    a[CO_BIGR] = big_rv;
                }
                if f == 2 {
                    a[CO_LOWF] = lowfv;
                    a[CO_WT] = wtv % P as u64;
                    a[CO_AP] = apv;
                    a[CO_BIG] = bigv;
                    a[CO_APOST] = apostv;
                    a[CO_NZB] = nzbv;
                    a[CO_IB] = finv(bpr);
                    a[CO_IG2] = finv(fsub(gg, 2));
                    a[CO_E2] = if gg == 2 { 1 } else { 0 };
                    if gg == 2 {
                        a[55] = n2(src_o.is_some()); // `a0g`
                        let x = ap_rv + fair_v;
                        cbv = if MA <= x { 1 } else { 0 };
                        cmps.push((x, MA, cbv));
                        a[CO_CX] = x;
                        a[CO_CY] = MA;
                        a[CO_CBIT] = cbv;
                        a[CO_CG] = 1;
                    }
                    if gg >= 2 {
                        a[CO_CB] = cbv;
                    }
                }
                if is_end {
                    let b_fv = if bigv == 1 || nzbv == 1 { 1 } else { 0 };
                    let a1v = if big_rv == 1 || cbv == 1 {
                        MA
                    } else {
                        ap_rv + fair_v
                    };
                    let a2v = a1v.saturating_sub(alv * base_v);
                    let gf = gfin_f(kk);
                    a[CO_REND] = 1;
                    a[CO_BF] = b_fv;
                    a[CO_A1] = a1v;
                    a[CO_A2] = a2v;
                    a[CO_G2] = alv * base_v;
                    a[CO_AFIN] = afin_f(kk);
                    a[CO_GFIN] = gf;
                    a[56] = n2(use_v); // `u0g`
                    if tv == 0 {
                        let ft = inp
                            .fwd
                            .iter()
                            .find(|&&(l, _)| l == kk)
                            .map(|&(_, t)| t)
                            .unwrap_or(0);
                        cmps.push((gf + gbv, ft, 1));
                        a[CO_FWG] = 1;
                        a[CO_CX] = gf + gbv;
                        a[CO_CY] = ft;
                        a[CO_CBIT] = 1;
                        a[CO_CG] = 1;
                        a[CO_PM0] = kk % 256;
                        a[CO_PM1] = kk / 256;
                        a[CO_FB] = ft % 256;
                        a[CO_FB + 1] = ft / 256 % 256;
                        a[CO_FB + 2] = ft / 65536 % 256;
                    }
                }
                rows.push(a);
                if f == 2 && gg < 3 {
                    apv += wtv * bpr;
                    apostv += wtv * bpo;
                }
                if f == 2 && gg >= 3 && bpr != 0 {
                    bigv = 1;
                }
            }
        }
    }

    // hash rows
    let base0 = 5 + 24 * nn;
    for j in 0..32usize {
        let bpr = get(&hpre, j);
        let mut a = vec![0u64; CODEC_WIDTH];
        for &(c, v) in &inst {
            a[c] = v;
        }
        a[CO_KZ] = 1;
        a[CO_DGG] = if j == 0 { 1 } else { 0 };
        a[CO_POS] = base0 + j as u64;
        a[CO_SJ] = j as u64;
        a[CO_BPOST] = get(&digest, j);
        a[CO_BPRE] = if present { bpr } else { 0 };
        a[CO_BSHA] = if present { bpr } else { 0 };
        a[CO_VBG] = n2(present);
        a[CO_ISJ] = finv(fsub(j as u64, 31));
        a[CO_ESJ] = if j == 31 { 1 } else { 0 };
        for i in 0..32usize {
            a[CO_REG[i]] = get(&digest, j + i);
        }
        set_bits(&mut a, CO_PBIT, get(&digest, j));
        set_bits(&mut a, CO_PRBIT, if present { bpr } else { 0 });
        rows.push(a);
    }
    for j in 0..32usize {
        let x = get(&inp.ash, j);
        let mut a = vec![0u64; CODEC_WIDTH];
        for &(c, v) in &inst {
            a[c] = v;
        }
        a[CO_KA] = 1;
        a[CO_POS] = base0 + 32 + j as u64;
        a[CO_SJ] = 32 + j as u64;
        a[CO_BSHA] = x;
        a[CO_PM0] = j as u64;
        a[CO_PM1] = x;
        a[CO_ISJ] = finv(fsub((32 + j) as u64, 63));
        a[CO_ESJ] = if j == 31 { 1 } else { 0 };
        rows.push(a);
    }

    (rows, cmps)
}

/// One block's codec rows and comparisons; `gbA` is the block's grants
/// (`b.grants`, field `gb`) when given (`n²` entries), else the distribute
/// grid's grants (`(distribution b).gb`, zero when it throws).
fn codec_block(inp: &SchedIn) -> (Vec<Vec<u64>>, Vec<(u64, u64, u64)>) {
    let nn = (inp.run.n * inp.run.n) as usize;
    let gb = if inp.gb.len() == nn {
        inp.gb.clone()
    } else {
        dist_rows(inp).map(|d| d.gb).unwrap_or_else(|| vec![0; nn])
    };
    codec_rows(inp, &gb)
}

/// `codecCell (bs.map blkOf)` (`Render/CodecRender.lean`): every block's
/// descriptor rows, zero padding (`codecPad`), `2^22` rows.
pub fn codec_aligned(bs: &[SchedIn]) -> Tab {
    let rows: Vec<Vec<u64>> = bs.iter().flat_map(|b| codec_block(b).0).collect();
    sched_tab(&rows, CODEC_WIDTH, |_| None)
}

/// `npudr v3render codec`.
pub fn codec(json: &str) -> Result<Tab, String> {
    Ok(codec_aligned(&parse_all(json)?))
}

// ---------------------------------------------------------------------------
// honest request-free blocks (`npudr v3sample codec|scandist|proc|mem|cmp`)
// ---------------------------------------------------------------------------

/// `Params.calculate Config.pv86 n` (`NearSpecV3.Scheduler`).
pub fn pv86_params(n: u64) -> Params {
    let base = (4_500_000u64 - 4_194_304) / n.saturating_sub(1).max(1);
    Params {
        base: base.min(100_000),
        max_shard_bandwidth: 4_500_000,
        max_single_grant: 4_194_304,
        max_receipt_size: 4_194_304,
        max_allowance: 4_500_000,
    }
}

/// `addrOf τ kind idx` (`Sched/Ids.lean`).
fn addr_of(tau: u64, kind: u64, idx: u64) -> u64 {
    tau * 16384 + kind * 4096 + idx
}

/// `leWords seed`.
fn le_words(seed: &[u64]) -> Vec<u64> {
    seed.chunks_exact(4)
        .map(|c| c[0] + 256 * c[1] + 65536 * c[2] + 16_777_216 * c[3])
        .collect()
}

/// One honest block of instance `tau` without raw requests: `ActualRun.run` on
/// an input whose requests are all empty is the closed-form link pass
/// (`linkPass`), no rounds, INIT-only memory segments, no comparisons, and the
/// final state is the link pass with `Rng.ofSeed seed`.  The prior state is
/// absent or canonical (`a0[l] < max_allowance`); the grants are the
/// distribute grid's; instance 0 carries random forwarding demands `≤ gfin + gb`.
fn sample_block(r: &mut super::sample::Rng, tau: u64) -> SchedIn {
    let n = 1 + r.below(4);
    let nn = n * n;
    let p = pv86_params(n);
    let id_base = r.below(1_000_000);
    let ids: Vec<u64> = (0..n).map(|i| id_base * 64 + 7 * i + 1).collect();
    let allowed: Vec<bool> = (0..nn).map(|_| r.below(4) != 0).collect();
    let present = r.coin();
    let a0: Vec<u64> = if present {
        (0..nn).map(|_| r.below(p.max_allowance)).collect()
    } else {
        Vec::new()
    };
    let prev_hash = if present { r.bytes(32) } else { Vec::new() };
    let seed = r.bytes(32);
    let ash = r.bytes(32);
    // `linkPass n p allowed (allowances ids prev)`
    let fair = p.max_shard_bandwidth / n;
    let al = |l: u64| allowed[l as usize];
    let a0l = |l: u64| if present { a0[l as usize] } else { 0 };
    let a2: Vec<u64> = (0..nn)
        .map(|l| {
            let a1 = (a0l(l) + fair).min(p.max_allowance);
            if al(l) { a1 - p.base } else { a1 }
        })
        .collect();
    let g2: Vec<u64> = (0..nn).map(|l| if al(l) { p.base } else { 0 }).collect();
    let sb: Vec<u64> = (0..n)
        .map(|s| p.max_shard_bandwidth - p.base * cnt_s(n, &allowed, s))
        .collect();
    let rb: Vec<u64> = (0..n)
        .map(|x| p.max_shard_bandwidth - p.base * cnt_r(n, &allowed, x))
        .collect();
    let mut segs = Vec::new();
    for l in 0..nn {
        segs.push(Seg {
            addr: addr_of(tau, 0, l),
            is_l: true,
            al: al(l),
            vin0: n2(al(l)),
            v0: a2[l as usize],
            w0: g2[l as usize],
            ops: Vec::new(),
        });
    }
    for (kind, bud) in [(1u64, &sb), (2u64, &rb)] {
        for x in 0..n {
            segs.push(Seg {
                addr: addr_of(tau, kind, x),
                is_l: false,
                al: false,
                vin0: 0,
                v0: bud[x as usize],
                w0: 0,
                ops: Vec::new(),
            });
        }
    }
    let key = le_words(&seed);
    let run = Run {
        tau,
        n,
        base: p.base,
        d: p.max_single_grant - p.base,
        seed,
        key: key.clone(),
        a2: a2.clone(),
        conv: Vec::new(),
        used: Vec::new(),
        rounds: Vec::new(),
        segs,
        cmps: Vec::new(),
        kfin: 0,
        fin: PState {
            sb,
            rb,
            al: a2,
            g: g2.clone(),
            rng: Rng {
                key,
                ctr: 0,
                buf: Vec::new(),
            },
        },
    };
    let mut b = SchedIn {
        run,
        ids,
        allowed,
        params: p,
        present,
        vid: r.below(1 << 30),
        gb: Vec::new(),
        fwd: Vec::new(),
        ash,
        a0,
        prev_hash,
    };
    b.gb = dist_rows(&b)
        .map(|d| d.gb)
        .unwrap_or_else(|| vec![0; nn as usize]);
    if tau == 0 {
        for l in 0..nn {
            if r.coin() {
                let cap = g2[l as usize] + b.gb[l as usize];
                b.fwd.push((l, r.below(cap + 1)));
            }
        }
    }
    b
}

/// `n` honest request-free blocks `τ = 0 … n−1` (`n = 0`: no scheduler
/// instance, every table is padding).  Blocks with requests and rounds come from
/// the Lean sampler (`np-lean-render-v3-sched sample`, the native scheduler).
pub fn sample(r: &mut super::sample::Rng, n: usize) -> Vec<SchedIn> {
    (0..n as u64).map(|tau| sample_block(r, tau)).collect()
}

/// The legacy `sched` table name: the scheduler is five `nearAirV3` tables, so
/// dispatch one of `codec`, `scandist`, `proc`, `mem`, `cmp`.
pub fn render(_json: &str) -> Result<Tab, String> {
    Err("sched: use one of codec/scandist/proc/mem/cmp".into())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cmp_pad_and_bits() {
        // x = 5, y = 3 => b = 1, d = 2
        let a = cmp_row(5, 3, 1);
        assert_eq!(&a[..6], &[1, 5, 3, 1, 0, 1]);
        // y > x => b = 0, d = y - x - 1 = 1
        let a = cmp_row(3, 5, 0);
        assert_eq!(a[3], 0);
        assert_eq!(a[4], 1);
        // the table: height 2^22, padding rows have b = 1
        let t = cmp_aligned(&[(1, 1, 1)]);
        assert_eq!(t.log, SCHED_LOG);
        assert_eq!(t.cells[t.width + 3], 1);
        assert_eq!(t.cells[(t.height() - 1) * t.width + 3], 1);
        assert_eq!(t.cells[t.width], 0);
    }

    #[test]
    fn mem_segment_shape() {
        let r = Run {
            segs: vec![Seg {
                addr: 7,
                is_l: true,
                al: true,
                vin0: 10,
                v0: 9,
                w0: 4,
                ops: vec![MOp {
                    t: 3,
                    op: OP_GRANT,
                    vin: 9,
                    v: 5,
                    wp: 4,
                    w: 8,
                    inc: 4,
                    ok: true,
                    c: true,
                    sf: true,
                }],
            }],
            ..Default::default()
        };
        let t = mem_aligned(&[&r, &r]);
        let at = |row: usize, c: usize| t.cells[row * MEM_WIDTH + c];
        // the shared clock 2^22; the second run's rows follow the first's
        assert_eq!(t.log, SCHED_LOG);
        assert_eq!(at(2, M_FST), 1);
        assert_eq!(at(3, M_W), 8);
        assert_eq!(at(4, M_ACT), 0);
        assert_eq!(at(0, M_ACT), 1);
        assert_eq!(at(0, M_FST), 1);
        assert_eq!(at(0, M_LST), 0);
        assert_eq!(at(0, M_ADDR), 7);
        assert_eq!(at(0, M_VIN), 10);
        assert_eq!(at(1, M_LST), 1);
        assert_eq!(at(1, M_IS_GR), 1);
        assert_eq!(at(1, M_W), 8);
    }

    #[test]
    fn proc_key_and_padding() {
        let r = Run {
            tau: 2,
            seed: (0..32u64).collect(),
            ..Default::default()
        };
        let r2 = Run {
            tau: 3,
            seed: (32..64u64).collect(),
            ..Default::default()
        };
        let rows: Vec<Vec<u64>> = proc_rows(&r).into_iter().chain(proc_rows(&r2)).collect();
        assert_eq!(rows.len(), 32);
        let at = |row: usize, c: usize| rows[row][c];
        assert_eq!(at(0, P_ACT), 1);
        assert_eq!(at(0, P_KK), 1);
        assert_eq!(at(0, P_TAU), 2);
        assert_eq!(at(0, P_COL_L), 256); // limb 0 = seed[0] + 256·seed[1]
        assert_eq!(at(0, P_COL_L + 1), 2 + 256 * 3); // limb 1 = seed[2] + 256·seed[3]
        assert_eq!(at(15, P_KL), 1);
        // the next instance's key block follows directly (boundary-repaired rotation)
        assert_eq!(at(16, P_KK), 1);
        assert_eq!(at(16, P_TAU), 3);
        assert_eq!(at(16, P_COL_L), 32 + 256 * 33);
        // tail row (the last run's) carries ikcPad and Kq = KSENT
        let tail = proc_tail_row(&r2);
        assert_eq!(tail[P_IKC], ikc_pad());
        assert_eq!(tail[P_KQQ], KSENT);
        assert_eq!(tail[P_TAU], 3);
        assert_eq!(tail[P_ACT], 0);
    }

    #[test]
    fn scandist_param_and_grid() {
        // n = 1, one request, one sender/receiver shard row and one cell.
        let inp = SchedIn {
            run: Run {
                tau: 0,
                n: 1,
                base: 10,
                d: 90,
                conv: vec![CReq {
                    cid: 0,
                    s: 0,
                    r: 0,
                    link: 0,
                    bm: vec![32, 0, 0, 0, 0],
                    bits: vec![5],
                    incs: vec![5],
                    key: 90,
                }],
                used: vec![vec![true]],
                fin: PState {
                    sb: vec![85],
                    rb: vec![85],
                    al: vec![85],
                    g: vec![15],
                    ..Default::default()
                },
                ..Default::default()
            },
            ids: vec![0],
            allowed: vec![true],
            params: Params {
                base: 10,
                max_shard_bandwidth: 100,
                max_single_grant: 100,
                ..Default::default()
            },
            ..Default::default()
        };
        let rows = scandist_rows(std::slice::from_ref(&inp));
        let w = SCANDIST_WIDTH;
        let cells: Vec<u64> = rows.iter().flatten().copied().collect();
        let t = Tab {
            log: 0,
            width: w,
            cells: cells.iter().map(|&x| x as u32).collect(),
        };
        // row 0 is the scan param row `kP`; row 1 the first request row `kS`.
        assert_eq!(t.cells[D_ACT], 1);
        assert_eq!(t.cells[D_KP], 1);
        assert_eq!(t.cells[D_NN], 1);
        assert_eq!(t.cells[S_BASE], 10);
        assert_eq!(t.cells[S_DD], 90);
        assert_eq!(t.cells[S_Q + 3], byte_of(90, 0) as u32); // D byte 0
        assert_eq!(t.cells[w + D_KS], 1);
        assert_eq!(t.cells[w + D_FQ], 1);
        assert_eq!(t.cells[w + S_Q], 32); // bm[0] >> 0
        assert_eq!(t.cells[w + S_B0], 0); // bit 0 of bm[0]
        // bit 5 of bm[0] is `b1` of row rho = 2 (trace row 3): pos = 4.
        let rho2 = 3 * w;
        assert_eq!(t.cells[rho2 + S_U0], 0);
        assert_eq!(t.cells[rho2 + S_U1], 1);
        assert_eq!(t.cells[rho2 + S_B0], 0);
        assert_eq!(t.cells[rho2 + S_B1], 1);
        // the request-end row 20 is `re`; the shard row follows at 21.
        let last_req = 20;
        assert_eq!(t.cells[last_req * w + D_RE], 1);
        assert_eq!(t.cells[21 * w + D_KSH], 1);
        // the grid header (kGH) and its cell (kC) follow the two shard rows.
        assert_eq!(t.cells[23 * w + D_KGH], 1);
        assert_eq!(t.cells[23 * w + D_B], 255);
        assert_eq!(t.cells[24 * w + D_KC], 1);
        assert_eq!(t.cells[24 * w + D_AL], 1);
        // the cell's grid grant is min(85, 85) = 85; link 0 is its own source
        // and is used (`use`), `hasSrc = 1`.
        assert_eq!(t.cells[24 * w + D_KP2], 85);
        assert_eq!(t.cells[24 * w + D_LNK], 1);
        assert_eq!(t.cells[24 * w + D_BY0], 1);
        assert_eq!(rows.len(), 25);
        // the comparator requests: the two shard keys, then the cell
        let d = dist_rows(&inp).unwrap();
        assert_eq!(d.cmps, vec![(85 * 64, 0, 1), (85 * 64, 0, 1), (85, 85, 1)]);
        assert_eq!(d.gb, vec![85]);
    }

    #[test]
    fn codec_height_and_header() {
        let inp = SchedIn {
            run: Run {
                n: 1,
                ..Default::default()
            },
            ids: vec![0],
            allowed: vec![true],
            params: Params {
                base: 10,
                max_shard_bandwidth: 100,
                ..Default::default()
            },
            ..Default::default()
        };
        let (rows, cmps) = codec_block(&inp);
        // 5 header + 24·1 records + 64 hash rows.
        assert_eq!(rows.len(), 5 + 24 + 64);
        let r0 = &rows[0];
        assert_eq!(r0[CO_ACT], 1);
        assert_eq!(r0[CO_KH], 1);
        assert_eq!(r0[CO_KF], 1);
        assert_eq!(r0[CO_NN], 1);
        assert_eq!(r0[CO_BASE], 10);
        // absent previous state: bpre = 0, pres = 0.
        assert_eq!(r0[CO_PRES], 0);
        assert_eq!(r0[CO_BPRE], 0);
        // the header register holds `params`: `[0, 0, 1, 0, 0, …]` for N = 1,
        // followed by base bytes `[10, 0, 0]` and fair bytes `[100, 0, 0]`.
        assert_eq!(r0[CO_REG[1]], 1); // params[1] = N byte 0
        assert_eq!(r0[CO_REG[2]], 0); // params[2] = N / 256
        assert_eq!(r0[CO_REG[5]], 10); // params[5] = base byte 0
        assert_eq!(r0[CO_REG[8]], 100); // params[8] = fair byte 0
        // record 0 is the source of link 0 (`useC = 1`)
        assert_eq!(rows[5][57], 1);
        // instance 0: the allowance comparison, then the forwarding comparison
        assert_eq!(cmps.len(), 2);
        assert_eq!(cmps[0], (100, MA, 0));
        assert_eq!(cmps[1].2, 1);
    }

    #[test]
    fn parse_forms() {
        let r = serde_json::to_string(&Run {
            tau: 4,
            ..Default::default()
        })
        .unwrap();
        for j in [
            r.clone(),
            format!("[{r}, {r}]"),
            format!("{{\"run\": {r}}}"),
            format!("[{{\"run\": {r}}}]"),
        ] {
            let bs = parse_all(&j).unwrap();
            assert!(!bs.is_empty() && bs.iter().all(|b| b.run.tau == 4), "{j}");
        }
        assert_eq!(parse_all("[]").unwrap().len(), 0);
    }
}
