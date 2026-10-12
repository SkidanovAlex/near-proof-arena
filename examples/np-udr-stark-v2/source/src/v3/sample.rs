//! Seeded random entry lists for the differential tests of [`super`].
//!
//! Each sampler returns entries satisfying the Lean honest-input predicate of
//! its table (`BndWf`, `AkeyOk`, `HeadOk`, `ValOk`, `UOk`, `WalkOk`), so the
//! rendered trace must also satisfy the table's local constraints
//! (`npudr v3check`).  Sizes are kept small: the Lean cell functions recompute
//! record lists per cell.

use super::*;

/// splitmix64.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed ^ 0x9e37_79b9_7f4a_7c15)
    }
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
    pub fn coin(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }
    /// A field element, biased towards the edges `0`, `1`, `P − 1`.
    pub fn fe(&mut self) -> u64 {
        match self.below(8) {
            0 => 0,
            1 => 1,
            2 => P as u64 - 1,
            _ => self.below(P as u64),
        }
    }
    pub fn bytes(&mut self, n: usize) -> Vec<u64> {
        (0..n).map(|_| self.below(256)).collect()
    }
}

pub fn bnd(r: &mut Rng, n: usize) -> Vec<BndE> {
    (0..n)
        .map(|_| BndE {
            x: r.fe(),
            lo: r.fe(),
            hi: r.fe(),
            hn: r.fe(),
            u: r.fe(),
        })
        .collect()
}

pub fn akey(r: &mut Rng, n: usize) -> Vec<AkeyE> {
    (0..n)
        .map(|_| {
            let mut bytes = r.bytes(9);
            bytes[8] = 1;
            AkeyE {
                vid: r.fe(),
                u: r.fe(),
                bytes,
            }
        })
        .collect()
}

pub fn head(r: &mut Rng, n: usize) -> Vec<HeadE> {
    (0..n.max(1))
        .map(|_| HeadE {
            tau: r.fe(),
            rid: r.fe(),
            rlen: r.fe(),
            rres: r.fe(),
            m_e: r.fe(),
            pre: r.bytes(32),
            post: r.bytes(32),
        })
        .collect()
}

pub fn val(r: &mut Rng, n: usize) -> Vec<ValE> {
    (0..n as u64)
        .map(|vid| {
            let vz = r.below(4) == 0;
            let len = if vz { 0 } else { 1 + r.below(9) };
            ValE {
                vid,
                len,
                vz,
                dup: r.coin(),
                hd: r.coin(),
                rep_e: r.fe(),
                bytes: r.bytes(len as usize),
            }
        })
        .collect()
}

/// Sorted by `(τ, le256 bytes)`, `τ` stepping by `0` or `1`, with repeats.
pub fn uniq(r: &mut Rng, n: usize) -> Vec<UEnt> {
    let mut tau = r.below(3);
    let mut out: Vec<UEnt> = Vec::new();
    for _ in 0..n.max(1) {
        let fresh = out.is_empty() || r.below(4) == 0;
        if !fresh && r.below(3) == 0 {
            tau += 1;
        }
        let bytes = match out.last() {
            Some(p) if p.tau == tau && r.below(4) == 0 => p.bytes.clone(),
            Some(p) if p.tau == tau => {
                // a larger key: bump a random byte, randomize the lower ones
                let mut b = p.bytes.clone();
                let k = r.below(32) as usize;
                if let Some(i) = (k..32).find(|&i| b[i] < 255) {
                    b[i] += 1;
                    for x in b.iter_mut().take(i) {
                        *x = r.below(256);
                    }
                }
                b
            }
            _ => r.bytes(32),
        };
        out.push(UEnt {
            eid: r.fe(),
            tau,
            bytes,
        });
    }
    out
}

fn edge(r: &mut Rng) -> Vec<u64> {
    (0..6).map(|_| r.fe()).collect()
}

/// One walk of `n ≥ 2` steps satisfying `WalkWf3` (`START`, descents, then one of
/// the four endings: `VAL`, absent by key, absent at a branch, or a mode-3 tail).
fn walk1(r: &mut Rng, n: usize) -> WalkR {
    const EK_DOWN: u64 = 0;
    const EK_KEY: u64 = 1;
    const EK_VAL: u64 = 2;
    const EK_LEND: u64 = 3;
    const SYM_END: u64 = 16;
    const SYM_START: u64 = 18;
    let (w, tau) = (r.fe(), r.fe());
    let ending = r.below(5);
    // descents: rows 0 .. d−1 (mode 0, not last)
    let d = match ending {
        0 | 3 | 4 => n - 1,
        _ => n - 2,
    };
    let mut steps: Vec<WStep3> = Vec::new();
    let st = |r: &mut Rng, mode, sym, e: Vec<u64>| WStep3 {
        mode,
        sym,
        e,
        u: r.fe(),
        bm: 0,
        hv: 0,
        ub: r.fe(),
    };
    for i in 0..d {
        let sym = if i == 0 { SYM_START } else { r.below(16) };
        let mut e = edge(r);
        if i == 0 {
            e[1] = tau;
        } else {
            let p: &WStep3 = steps.last().unwrap();
            e[0] = p.e[3];
            e[1] = p.e[4];
        }
        e[2] = sym;
        e[5] = if r.coin() { EK_DOWN } else { EK_KEY };
        steps.push(st(r, 0, sym, e));
    }
    let chained = |r: &mut Rng, steps: &Vec<WStep3>| {
        let mut e = edge(r);
        let p = steps.last().unwrap();
        e[0] = p.e[3];
        e[1] = p.e[4];
        e
    };
    let bm_free = |r: &mut Rng, sym: u64| r.below(1 << 16) & !(1u64 << sym);
    match ending {
        // last row `VAL`
        0 => {
            let mut e = chained(r, &steps);
            e[2] = SYM_END;
            e[5] = EK_VAL;
            steps.push(st(r, 0, SYM_END, e));
        }
        // absent by key / at a branch, then a mode-3 tail row
        1 | 2 => {
            let sym = r.below(16);
            let mut e = chained(r, &steps);
            let mut s = if ending == 1 {
                e[5] = if r.coin() { EK_KEY } else { EK_LEND };
                e[2] = (sym + 1 + r.below(15)) % 16;
                st(r, 1, sym, e)
            } else {
                let p = steps.last_mut().unwrap();
                p.e[4] = 0;
                e[1] = 0;
                st(r, 2, sym, e)
            };
            if ending == 2 {
                s.bm = bm_free(r, sym);
                s.hv = r.below(2);
            }
            steps.push(s);
            let e = edge(r);
            let tail = st(r, 3, SYM_END, e);
            steps.push(tail);
        }
        // last row absent by key
        3 => {
            let mut e = chained(r, &steps);
            e[5] = if r.coin() { EK_KEY } else { EK_LEND };
            e[2] = r.below(16);
            steps.push(st(r, 1, SYM_END, e));
        }
        // last row absent at a branch
        _ => {
            let p = steps.last_mut().unwrap();
            p.e[4] = 0;
            let e = chained(r, &steps);
            let mut s = st(r, 2, SYM_END, e);
            s.bm = r.below(1 << 16);
            steps.push(s);
        }
    }
    WalkR { w, tau, steps }
}

pub fn walk(r: &mut Rng, n: usize) -> Vec<WalkR> {
    (0..n.max(1))
        .map(|_| {
            let len = 3 + r.below(6) as usize;
            walk1(r, len)
        })
        .collect()
}

/// `n` random entries of `table` as JSON.
pub fn sample_json(table: &str, seed: u64, n: usize) -> Result<String, String> {
    let r = &mut Rng::new(seed);
    let j = match table {
        "bnd" => serde_json::to_string(&bnd(r, n)),
        "akey" => serde_json::to_string(&akey(r, n)),
        "head" => serde_json::to_string(&head(r, n)),
        "val" => serde_json::to_string(&val(r, n)),
        "uniq" => serde_json::to_string(&uniq(r, n)),
        "walk" => serde_json::to_string(&walk(r, n)),
        "node" => serde_json::to_string(&node(r, n)),
        "acct" => serde_json::to_string(&acct(r, n)),
        "size" => serde_json::to_string(&size(r, n)),
        "srcp" => serde_json::to_string(&srcp(r, n)),
        "qv" => serde_json::to_string(&qv(r, n)),
        "rcpt" => serde_json::to_string(&rcpt(r, n)),
        "chacha" => serde_json::to_string(&chacha(r, n)),
        "rng" => serde_json::to_string(&rng(r, n)),
        "shuf" => serde_json::to_string(&shuf(r, n)),
        "sha_t" | "sha_r" => serde_json::to_string(&super::sha::sample(r, n)),
        "mrk" => serde_json::to_string(&super::mrksort::mrk(r, n as u64)),
        "sort" => serde_json::to_string(&super::mrksort::sort(r, n)),
        t => return Err(format!("unknown table {t}")),
    };
    j.map_err(|e| e.to_string())
}

/// `n ≥ 1` honest `AcctV` records: `k`, `tlast` canonical fields, 72 raw pre
/// bytes (< 256) whose amount is not `u128::MAX`, and 16 raw post bytes.  The
/// per-record `k` is distinct so the ascending-slot side condition of
/// `AcctV3Wf` holds.
pub fn acct(r: &mut Rng, n: usize) -> Vec<AcctV> {
    (0..n.max(1))
        .map(|s| {
            let mut pre = r.bytes(72);
            // AccountV1: not every amount byte is 255
            pre[r.below(16) as usize] = r.below(255);
            AcctV {
                k: s as u64 + 1,
                tlast: r.fe(),
                pre,
                post: r.bytes(16),
            }
        })
        .collect()
}

/// A `SizeV` plus the public `ovh`, satisfying `SizeOk` (both 24-bit slacks are
/// non-negative): `x_0 + x_1 ≤ 3,000,000` and `ovh + Σ x ≤ 8,388,608`.  The
/// sampler fixes `ovh = 0` so the trace also passes `npudr v3check` (which
/// supplies zero public inputs); a nonzero `ovh` is exercised separately by the
/// conformance script.
pub fn size(r: &mut Rng, _n: usize) -> Vec<SizeInput> {
    let x0 = r.below(1_500_000);
    let x1 = r.below(3_000_000 - x0);
    let rem = 8_388_608 - x0 - x1;
    let x2 = r.below(rem.min(1_000_000) + 1);
    vec![SizeInput { x0, x1, x2, ovh: 0 }]
}

// ------------------------------------------------------------------- node

use super::acct::AcctV;
use super::node::{Kid, NODE_WIDTH, NodeS3, NodeV3, Slot};
use super::size::SizeInput;

fn slot_ref(r: &mut Rng) -> Slot {
    Slot::Ref {
        lenB: vec![0, 0, 0, 0],
        h: r.bytes(32),
    }
}

fn slot_val(r: &mut Rng) -> Slot {
    Slot::Val {
        lenB: vec![1 + r.below(4) as u64, 0, 0, 0],
        vid: r.fe(),
        vlen: 1 + r.below(20),
        pre: r.bytes(32),
        post: r.bytes(32),
        written: r.coin(),
    }
}

fn kid(r: &mut Rng) -> Kid {
    match r.below(3) {
        0 => Kid::None,
        1 => Kid::Hash { h: r.bytes(32) },
        _ => {
            let mut pre = r.bytes(32);
            let post = if r.coin() { pre.clone() } else { r.bytes(32) };
            if !r.coin() {
                pre = post.clone();
            }
            Kid::Node {
                cid: r.fe(),
                clen: r.fe(),
                cres: r.fe(),
                pre,
                post,
            }
        }
    }
}

/// A random `NodeV3` (not necessarily honest; byte-identity only needs a
/// deterministic function of the entries).
fn nodev(r: &mut Rng) -> NodeV3 {
    match r.below(3) {
        0 => {
            let klen = r.below(6) as usize;
            NodeV3::Leaf {
                key: r.bytes(klen).into_iter().map(|x| x % 16).collect(),
                v: if r.coin() { slot_val(r) } else { slot_ref(r) },
                memB: r.bytes(8),
            }
        }
        1 => {
            let klen = r.below(6) as usize;
            NodeV3::Ext {
                key: r.bytes(klen).into_iter().map(|x| x % 16).collect(),
                kid: if r.coin() {
                    kid(r)
                } else {
                    Kid::Hash { h: r.bytes(32) }
                },
                memB: r.bytes(8),
            }
        }
        _ => {
            let kids: Vec<Kid> = (0..16)
                .map(|_| if r.below(3) == 0 { kid(r) } else { Kid::None })
                .collect();
            NodeV3::Branch {
                v: if r.coin() { Some(slot_val(r)) } else { None },
                kids,
                memB: r.bytes(8),
            }
        }
    }
}

// ------------------------------------------------------------------- srcp

use super::srcp::{SrcpB, SrcpItem};

/// A random `SrcpB` satisfying `SrcpWf` (`Rcpt/Extract/Srcp/Defs.lean`): the
/// lists are consecutive from `0`, message indices consecutive across the table,
/// the path items carry `pl = 32` first then `64`, and `dup → L = 12`.
fn srcp_block(r: &mut Rng, j: u64, ql: u64, d: usize) -> SrcpB {
    let dup = r.below(5) == 0;
    let l = if dup { 12 } else { 1 + r.below(20) };
    let mut path: Vec<SrcpItem> = Vec::with_capacity(d);
    for i in 0..d as u64 {
        path.push(SrcpItem {
            q: ql + 1 + i,
            dir: r.coin(),
            sib: r.bytes(32),
            acc: r.bytes(32),
            pq: ql + i,
            pl: if i == 0 { 32 } else { 64 },
        });
    }
    let dlen = d as u64;
    SrcpB {
        j,
        l,
        dup,
        root: r.bytes(32),
        qe: ql + dlen,
        le: if dlen == 0 { 32 } else { 64 },
        ql,
        leaf: r.bytes(32),
        path,
    }
}

pub fn srcp(r: &mut Rng, n: usize) -> Vec<SrcpB> {
    let n = n.max(1);
    let mut out: Vec<SrcpB> = Vec::with_capacity(n);
    let mut ql: u64 = 1;
    for j in 0..n as u64 {
        let d = r.below(4) as usize;
        let b = srcp_block(r, j, ql, d);
        ql = b.ql + b.path.len() as u64 + 1;
        out.push(b);
    }
    out
}

// ------------------------------------------------------------------- qv

use super::qv::{QvIn, QvItem, QvRecIn, QvWalkIn};

/// A `qvV3` walk (`CombinedWalkGen.Walk`): `code` is the `Kind.code` (`0`
/// delayed, `1` buffered, `2` yielded, `3` group).
fn qv_walk(
    code: u64,
    tau: u64,
    slot: u64,
    count: u64,
    value: Option<Vec<u64>>,
    vid: u64,
    last_main: bool,
    fin: bool,
    shard: u64,
) -> QvWalkIn {
    QvWalkIn {
        code,
        shard,
        tau,
        slot,
        count,
        value,
        vid,
        users: 0,
        last_main,
        fin,
    }
}

/// A valid `ValueGen.Record` (one of the three `Payload` shapes).
fn qv_record(r: &mut Rng) -> QvRecIn {
    let vid = r.fe();
    let tau = r.fe();
    let users = r.fe();
    match r.below(3) {
        0 => QvRecIn {
            rkind: 0,
            vid,
            tau,
            users,
            index: r.bytes(8),
            ..QvRecIn::default()
        },
        1 => {
            let n = r.below(4) as usize;
            let entries: Vec<QvItem> = (0..n)
                .map(|_| QvItem {
                    shard: r.bytes(8),
                    index: r.bytes(8),
                })
                .collect();
            QvRecIn {
                rkind: 1,
                vid,
                tau,
                users,
                entries,
                ..QvRecIn::default()
            }
        }
        _ => {
            let n = r.below(9) as usize;
            QvRecIn {
                rkind: 2,
                vid,
                tau,
                users,
                bytes: r.bytes(n),
                ..QvRecIn::default()
            }
        }
    }
}

/// The honest `qvV3` row plan `CombinedWalkGen.plan pre v pres resolve` with
/// `pres = []` and `K = 0`: the three main walks (delayed, buffered, yielded)
/// and one group walk per shard, the last marked `lastMain` and `final`.  The
/// buffered value is empty for no shards and otherwise the `g` buffered entries
/// (`4 + 24·g` bytes); a group walk needs its value present (constraint
/// `absent·count = 0` on the group window).  `n_rec` valid records follow.
pub fn qv(r: &mut Rng, n_rec: usize) -> QvIn {
    let g = r.below(4) as u64;
    let count = g;
    let last = |slot: u64| slot + 1 == 3 + g;
    let buffered_value = |r: &mut Rng| -> Option<Vec<u64>> {
        if g == 0 {
            None
        } else {
            let mut v = vec![g % 256, (g / 256) % 256, 0, 0];
            for _ in 0..g {
                let shard = r.bytes(8);
                let index = r.bytes(8);
                v.extend_from_slice(&shard);
                v.extend_from_slice(&index);
                v.extend_from_slice(&index);
            }
            Some(v)
        }
    };
    let mut walks = vec![
        qv_walk(0, 0, 0, count, None, r.fe(), last(0), last(0), 0),
        qv_walk(
            1,
            0,
            1,
            count,
            buffered_value(r),
            r.fe(),
            last(1),
            last(1),
            0,
        ),
        qv_walk(2, 0, 2, count, None, r.fe(), last(2), last(2), 0),
    ];
    for i in 0..g {
        let slot = 3 + i;
        walks.push(qv_walk(
            3,
            0,
            slot,
            count,
            Some(r.bytes(32)),
            r.fe(),
            last(slot),
            last(slot),
            i,
        ));
    }
    let records = (0..n_rec).map(|_| qv_record(r)).collect();
    QvIn { walks, records }
}

// ------------------------------------------------------------------- rcpt

use super::rcpt::{ListV3, RcptE, RcptIn, Rlk};

/// `Params.G`.
const GAS_G: u128 = 223182562500;

fn rcpt_bytes(r: &mut Rng, s: &[u8]) -> Vec<u64> {
    // a named, valid account id: `letters` with no separators, length ≤ 64
    let mut out: Vec<u64> = s.iter().map(|&x| x as u64).collect();
    out.truncate(3 + r.below(4) as usize);
    out
}

fn rcpt_one(r: &mut Rng, sys: bool, bgp: u128) -> RcptE {
    let pred: Vec<u64> = if sys {
        b"system".iter().map(|&x| x as u64).collect()
    } else {
        rcpt_bytes(r, b"alice")
    };
    let v = rcpt_bytes(r, b"bob");
    // `system` receipts either have `signer = receiver` (`ee`) or mismatch at
    // exactly one byte with equal lengths (`dd`).
    let s = if sys {
        if r.coin() {
            v.clone()
        } else {
            let mut t = v.clone();
            let k = r.below(t.len() as u64) as usize;
            t[k] = (t[k] + 1) % 256;
            t
        }
    } else {
        rcpt_bytes(r, b"carol")
    };
    let ee = sys && s == v;
    let gpv = r.below(1000) as u128;
    let ge = bgp <= gpv;
    let hr = !sys && ge && gpv > bgp;
    let brn: u128 = if sys { 0 } else { gpv.min(bgp) };
    let sur: u128 = if sys {
        0
    } else {
        gpv.saturating_sub(gpv.min(bgp))
    };
    let depv = r.below(1 << 16);
    let lkv = r.below(1 << 16);
    let befv = r.below(1 << 16);
    let aft = befv + depv;
    // routing interval: receiver inside `[receiver, upper)` with an empty upper
    // marker (`hn = 1`) so every comparison obligation is vacuous except the
    // lower prefix, which equals the receiver.
    let lv = v.len();
    let rlk: Vec<Rlk> = (0..=lv)
        .map(|i| Rlk {
            pos: i as u64,
            lo: if i < lv { v[i] } else { 0 },
            hi: 0,
            hn: 1,
            u: i as u64,
        })
        .collect();
    let kt = r.below(2);
    RcptE {
        p: pred,
        v: v.clone(),
        s: if ee { v.clone() } else { s },
        rid: r.bytes(32),
        kt,
        pk: r.bytes(32 + 32 * kt as usize),
        gp: (0..16)
            .map(|i| ((gpv as u128 >> (8 * i)) & 255) as u64)
            .collect(),
        dep: (0..16)
            .map(|i| ((depv as u128 >> (8 * i)) & 255) as u64)
            .collect(),
        hr,
        ge,
        kslot: r.fe(),
        tprev: 0,
        bef: (0..16)
            .map(|i| ((befv as u128 >> (8 * i)) & 255) as u64)
            .collect(),
        lk: (0..16)
            .map(|i| ((lkv as u128 >> (8 * i)) & 255) as u64)
            .collect(),
        st: vec![0; 16],
        aft: (0..16)
            .map(|i| ((aft as u128 >> (8 * i)) & 255) as u64)
            .collect(),
        burnt: rcpt_num(GAS_G * brn),
        ramt: rcpt_num(GAS_G * sur),
        rfid: r.bytes(32),
        peoh: r.bytes(32),
        sys,
        ee,
        gv: Vec::new(),
        gs: Vec::new(),
        sx: Vec::new(),
        akf: r.below(2),
        akk: r.fe(),
        aku: r.fe(),
        q: r.below(128),
        rlk,
    }
}

fn rcpt_num(x: u128) -> Vec<u64> {
    (0..16).map(|i| ((x >> (8 * i)) & 255) as u64).collect()
}

/// `n` applied source lists of honest receipts (`RcptOk`-shaped): `system` and
/// ordinary receivers, with `hr` only on a non-system surplus.
pub fn rcpt(r: &mut Rng, n: usize) -> RcptIn {
    let nlists = n.max(1).min(4);
    let bgp = r.below(1000);
    let mut lists = Vec::with_capacity(nlists);
    for _ in 0..nlists {
        let m = r.below(3) as usize;
        let mut rs = Vec::with_capacity(m);
        for _ in 0..m {
            let sys = r.below(4) == 0;
            rs.push(rcpt_one(r, sys, bgp as u128));
        }
        lists.push(ListV3 {
            n0: (m % 256) as u64,
            n1: (m / 256) as u64,
            rs,
        });
    }
    RcptIn {
        lists,
        own: r.fe(),
        height: r.fe(),
        bgp,
    }
}

pub fn node(r: &mut Rng, n: usize) -> Vec<NodeS3> {
    (0..n.max(1))
        .map(|i| {
            let v = nodev(r);
            let len = v.ser_len();
            NodeS3 {
                v,
                tau: r.fe(),
                depth: if i == 0 { 0 } else { r.below(6) },
                res: r.fe(),
                uses: r.bytes(4),
                ubm: r.fe(),
                dup: r.coin(),
                hd: r.coin(),
                rep_e: r.fe(),
                ucid: r.bytes(len),
                m_u: r.bytes(len),
            }
        })
        .collect()
}

// ----------------------------------------------------------------- chacha

use super::chacha::{ChachaReq, RngCall, ShuffleInst};

/// A 256-bit key as eight `u32` words with simple values.
fn cha_key(r: &mut Rng) -> Vec<u64> {
    (0..8).map(|_| r.below(1 << 32)).collect()
}

/// `n ≥ 1` requests satisfying `ZkFormal.Chacha.Gen.ReqOk` (`ctr < 2^26`).
pub fn chacha(r: &mut Rng, n: usize) -> Vec<ChachaReq> {
    (0..n.max(1))
        .map(|_| ChachaReq {
            key: cha_key(r),
            ctr: r.below(1 << 26),
            used: (0..16).map(|_| r.coin()).collect(),
        })
        .collect()
}

/// `n ≥ 1` calls satisfying `ZkFormal.Chacha.Rng.Gen.CallOk` (`1 ≤ n < 2^14`).
pub fn rng(r: &mut Rng, n: usize) -> Vec<RngCall> {
    (0..n.max(1))
        .map(|_| RngCall {
            key: cha_key(r),
            kstart: r.below(64),
            n: 1 + r.below((1 << 14) - 1) as u64,
        })
        .collect()
}

/// `n ≥ 1` instances satisfying `ZkFormal.Chacha.Shuffle.Gen` (`1 ≤ L ≤ 2^14`).
pub fn shuf(r: &mut Rng, n: usize) -> Vec<ShuffleInst> {
    (0..n.max(1))
        .map(|_| {
            let l = 1 + r.below(24) as usize;
            ShuffleInst {
                lid: r.fe(),
                key: cha_key(r),
                kstart: r.below(32),
                vals: (0..l).map(|_| r.below(1 << 32)).collect(),
            }
        })
        .collect()
}
