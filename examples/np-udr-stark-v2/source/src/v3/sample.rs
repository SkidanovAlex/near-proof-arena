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
        "val" => with_rpl(&val(r, n), r),
        "uniq" => serde_json::to_string(&uniq(r, n)),
        "walk" => serde_json::to_string(&walk(r, n)),
        "node" => with_rpl(&node(r, n), r),
        "ups" => serde_json::to_string(&ups(r, n)),
        "acct" => serde_json::to_string(&acct(r, n)),
        "size" => serde_json::to_string(&size(r, n)),
        "srcp" => serde_json::to_string(&srcp(r, n)),
        "qv" => serde_json::to_string(&qv(r, n)),
        "rcpt" => serde_json::to_string(&rcpt(r, n)),
        "chacha" => serde_json::to_string(&chacha(r, n)),
        "rng" => serde_json::to_string(&rng(r, n)),
        "shuf" => serde_json::to_string(&shuf(r, n)),
        "codec" | "scandist" | "proc" | "mem" | "cmp" => {
            serde_json::to_string(&super::sched::sample(r, n))
        }
        "sha_t" | "sha_r" => serde_json::to_string(&super::sha::sample(r, n)),
        "mrk" => serde_json::to_string(&super::mrksort::mrk(r, n as u64)),
        "sort" => serde_json::to_string(&super::mrksort::sort(r, n)),
        t => return Err(format!("unknown table {t}")),
    };
    j.map_err(|e| e.to_string())
}

/// `n` honest `AcctV` records (none for `n = 0`: the empty chunk,
/// `AcctV3OkE`): `k`, `tlast` canonical fields, 72 raw pre
/// bytes (< 256) whose amount is not `u128::MAX`, and 16 raw post bytes.  The
/// per-record `k` is distinct so the ascending-slot side condition of
/// `AcctV3Wf` holds.
pub fn acct(r: &mut Rng, n: usize) -> Vec<AcctV> {
    (0..n)
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
/// conformance script.  The A7 totals `yN` sum to at most `B0` (the honest
/// `sizeA7` precondition), with the edge `Σ y = B0` one time in four.
pub fn size(r: &mut Rng, _n: usize) -> Vec<SizeInput> {
    let x0 = r.below(1_500_000);
    let x1 = r.below(3_000_000 - x0);
    let rem = 8_388_608 - x0 - x1;
    let x2 = r.below(rem.min(1_000_000) + 1);
    let b0 = super::size::B0;
    let y0 = r.below(b0 / 2 + 1);
    let y1 = r.below(b0 - y0 + 1);
    let y2 = if r.below(4) == 0 {
        b0 - y0 - y1
    } else {
        r.below(b0 - y0 - y1 + 1)
    };
    vec![SizeInput {
        x0,
        x1,
        x2,
        ovh: 0,
        y_n: vec![y0, y1, y2],
    }]
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

/// One source key's proof entry: root, leaf, path items `(dir, sib)`.
struct SrcpKey {
    root: Vec<u64>,
    leaf: Vec<u64>,
    path: Vec<(bool, Vec<u64>, Vec<u64>)>,
    len: u64,
}

/// `blockOfProof root dup j ql entry`: the block of occurrence `j` with
/// message counter `ql` (`Rcpt/Render/Srcp/FromProof.lean`).
fn srcp_block(k: &SrcpKey, j: u64, ql: u64, dup: bool, rep: bool) -> SrcpB {
    let path: Vec<SrcpItem> = k
        .path
        .iter()
        .enumerate()
        .map(|(i, (dir, sib, acc))| SrcpItem {
            q: ql + 1 + i as u64,
            dir: *dir,
            sib: sib.clone(),
            acc: acc.clone(),
            pq: ql + i as u64,
            pl: if i == 0 { 32 } else { 64 },
        })
        .collect();
    let d = path.len() as u64;
    SrcpB {
        j,
        l: if rep { 12 } else { k.len },
        dup,
        root: k.root.clone(),
        qe: ql + d,
        le: if d == 0 { 32 } else { 64 },
        ql,
        leaf: k.leaf.clone(),
        path,
        rep,
    }
}

/// Honest table-20 input (`DedupRender.TableFacts bs rep`, A10 depth `≤ DP0`):
/// `n` source occurrences (none for `n = 0`); an occurrence reuses an earlier
/// key with probability `1/4` (`dup`, a reference block sharing the first
/// occurrence's proof entry); every occurrence of a repeated key has `rep` and
/// `L = 12`; the first occurrence is computed with `ql = 1`, and `ql` advances by
/// `1 + |path|` after a computed block only.
pub fn srcp(r: &mut Rng, n: usize) -> Vec<SrcpB> {
    let mut keys: Vec<SrcpKey> = Vec::new();
    let mut occ: Vec<usize> = Vec::with_capacity(n);
    for j in 0..n {
        if j > 0 && r.below(4) == 0 {
            occ.push(r.below(keys.len() as u64) as usize);
        } else {
            let d = r.below(4) as usize;
            keys.push(SrcpKey {
                root: r.bytes(32),
                leaf: r.bytes(32),
                path: (0..d)
                    .map(|_| (r.coin(), r.bytes(32), r.bytes(32)))
                    .collect(),
                len: 1 + r.below(20),
            });
            occ.push(keys.len() - 1);
        }
    }
    let mut out: Vec<SrcpB> = Vec::with_capacity(n);
    let mut seen = vec![false; keys.len()];
    let mut ql: u64 = 1;
    for (j, &k) in occ.iter().enumerate() {
        let dup = seen[k];
        seen[k] = true;
        let rep = occ.iter().filter(|&&x| x == k).count() >= 2;
        let b = srcp_block(&keys[k], j as u64, ql, dup, rep);
        if !dup {
            ql = b.ql + b.path.len() as u64 + 1;
        }
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

use super::rcpt::{Iv, ListV3, RcptE, RcptIn, Rlk};

/// `Params.G`.
const GAS_G: u128 = 223182562500;

fn rcpt_bytes(r: &mut Rng, s: &[u8]) -> Vec<u64> {
    // a named, valid account id: `letters` with no separators, length ≤ 64
    let mut out: Vec<u64> = s.iter().map(|&x| x as u64).collect();
    out.truncate(3 + r.below(4) as usize);
    out
}

fn rcpt_num(x: u128) -> Vec<u64> {
    (0..16).map(|i| ((x >> (8 * i)) & 255) as u64).collect()
}

/// A routing interval containing `v`: an optional lower bound (a prefix of `v`)
/// and an optional upper bound (`v[..m] ‖ v[m] + 1`).
fn rcpt_interval(r: &mut Rng, v: &[u64]) -> Iv {
    let lo = if r.coin() {
        Some(v[..r.below(v.len() as u64 + 1) as usize].to_vec())
    } else {
        None
    };
    let hi = if r.coin() {
        let m = r.below(v.len() as u64) as usize;
        let mut h = v[..m].to_vec();
        h.push(v[m] + 1);
        Some(h)
    } else {
        None
    };
    Iv { lo, hi }
}

/// The view's `rlk`: the receiver positions `0 ..= Lv` with `gBd = 1` (`rcptOf`),
/// with zero use counters (the renderer ranks `uB` itself).
fn rcpt_rlk(v: &[u64], iv: &Iv) -> Vec<Rlk> {
    let g = |x: &[u64], i: usize| x.get(i).copied().unwrap_or(0);
    let same = |x: &[u64], n: usize| (0..n).all(|i| g(v, i) == g(x, i));
    let lo = iv.lo.clone().unwrap_or_default();
    let hi = iv.hi.clone().unwrap_or_default();
    (0..=v.len())
        .filter(|&pos| same(&lo, pos) || (iv.hi.is_some() && same(&hi, pos)))
        .map(|pos| Rlk {
            pos: pos as u64,
            lo: g(&lo, pos),
            hi: g(&hi, pos),
            hn: u64::from(iv.hi.is_none()),
            u: 0,
        })
        .collect()
}

fn rcpt_one(r: &mut Rng, sys: bool, bgp: u128, v: Vec<u64>, tprev: u64) -> RcptE {
    let pred: Vec<u64> = if sys {
        b"system".iter().map(|&x| x as u64).collect()
    } else {
        rcpt_bytes(r, b"alice")
    };
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
    let gpv: u128 = match r.below(5) {
        0 if sys => u128::MAX,
        1 => r.next_u64() as u128,
        _ => r.below(1000) as u128,
    };
    let ge = bgp <= gpv;
    let hr = !sys && gpv > bgp;
    let brn: u128 = if sys { 0 } else { gpv.min(bgp) };
    let sur: u128 = if sys { 0 } else { gpv - gpv.min(bgp) };
    let depv = r.below(1 << 16) as u128;
    let lkv = r.below(1 << 16) as u128;
    // either a staked account (`big`) or a small one with storage ≤ 770
    let (befv, stv): (u128, u128) = if r.coin() {
        let st = r.below(3000) as u128;
        (r.next_u64() as u128 + 10_000_000_000_000_000_000 * st, st)
    } else {
        (r.below(1 << 16) as u128, r.below(771) as u128)
    };
    let iv = rcpt_interval(r, &v);
    let rlk = rcpt_rlk(&v, &iv);
    let kt = r.below(2);
    RcptE {
        p: pred,
        v: v.clone(),
        s,
        rid: r.bytes(32),
        kt,
        pk: r.bytes(32 + 32 * kt as usize),
        gp: rcpt_num(gpv),
        dep: rcpt_num(depv),
        hr,
        ge,
        kslot: r.fe(),
        tprev,
        bef: rcpt_num(befv),
        lk: rcpt_num(lkv),
        st: rcpt_num(stv),
        aft: rcpt_num(befv + depv),
        burnt: rcpt_num(GAS_G * brn),
        ramt: rcpt_num(GAS_G * sur),
        rfid: if hr { r.bytes(32) } else { vec![0; 32] },
        peoh: r.bytes(32),
        sys,
        ee,
        gv: Vec::new(),
        gs: Vec::new(),
        sx: Vec::new(),
        akf: r.below(2),
        akk: r.fe(),
        aku: 0,
        q: r.below(128),
        rlk,
        iv: Some(iv),
    }
}

/// `n` applied source lists of honest receipts (`RcptOk`-shaped): `system` and
/// ordinary receivers (receivers repeat, `tprev` = `latestReceiverVersion`), `hr`
/// only on a non-system surplus, system receipts up to gas price `u128::MAX`.
pub fn rcpt(r: &mut Rng, n: usize) -> RcptIn {
    let nlists = n.clamp(1, 4);
    let bgp = r.below(1000) as u128;
    let mut lists = Vec::with_capacity(nlists);
    let mut seen: Vec<Vec<u64>> = Vec::new();
    for _ in 0..nlists {
        let m = r.below(4) as usize;
        let mut rs = Vec::with_capacity(m);
        for _ in 0..m {
            let sys = r.below(4) == 0;
            let v = if !seen.is_empty() && r.below(3) == 0 {
                seen[r.below(seen.len() as u64) as usize].clone()
            } else {
                rcpt_bytes(r, b"bob")
            };
            let tprev = seen
                .iter()
                .rposition(|x| *x == v)
                .map(|k| k as u64 + 1)
                .unwrap_or(0);
            rs.push(rcpt_one(r, sys, bgp, v.clone(), tprev));
            seen.push(v);
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

// -------------------------------------------------------------- A7 (val/node/ups)

/// The entry list `es` as JSON with a random `"rpl"` flag on each entry (the
/// replaced-record predicate of `nodeA7` / `valA7`; any choice is locally
/// legal, so both values are drawn).
fn with_rpl<T: serde::Serialize>(es: &[T], r: &mut Rng) -> serde_json::Result<String> {
    let mut v = serde_json::to_value(es)?;
    if let Some(arr) = v.as_array_mut() {
        for x in arr {
            if let Some(o) = x.as_object_mut() {
                o.insert("rpl".into(), serde_json::Value::Bool(r.coin()));
            }
        }
    }
    serde_json::to_string(&v)
}

use super::ups::{UpsInst, UpsPartI};

/// `n` **shape-valid, not honest** `upsV3` instances (no `UpsRenderOk`
/// sampler exists: honest instances come from a native upsert run): four walk
/// steps, three path records, a short value and 1–3 parts with byte strings
/// and field shapes covering them.  For the Rust/Lean render differential of
/// `upsA7` only (`v3check` does not hold on these).
pub fn ups(r: &mut Rng, n: usize) -> Vec<UpsInst> {
    (0..n as u64)
        .map(|tau| {
            let step = |r: &mut Rng| WStep3 {
                mode: r.below(3),
                sym: r.below(19),
                e: (0..6).map(|_| r.below(8)).collect(),
                u: r.below(3),
                bm: r.below(1 << 16),
                hv: r.below(2),
                ub: r.below(2),
            };
            let walk = (0..4).map(|_| step(r)).collect();
            let nq = 1 + r.below(3) as usize;
            let parts = (0..nq)
                .map(|_| {
                    let ql = 1 + r.below(6) as usize;
                    let mut shape = Vec::new();
                    let mut left = ql as u64;
                    while left > 0 {
                        let l = 1 + r.below(left);
                        shape.push((r.below(9), l));
                        left -= l;
                    }
                    let pl = 1 + r.below(6) as usize;
                    UpsPartI {
                        kind: r.below(12),
                        sd: r.below(3),
                        s_n: r.below(8),
                        pdep: r.below(4),
                        rc: r.below(3),
                        c_n: r.below(8),
                        pb: r.bytes(pl),
                        pcid: (0..pl).map(|_| r.below(4)).collect(),
                        ty: r.below(4),
                        qhk: r.below(3),
                        qodd: r.below(2),
                        phk: r.below(3),
                        podd: r.below(2),
                        nochild: r.below(2),
                        shape,
                        q: r.bytes(ql),
                        jm: r.below(16),
                        clen: r.below(40),
                        m_b: r.below(1000),
                        soff: r.below(pl as u64),
                        neg: r.below(2),
                    }
                })
                .collect();
            UpsInst {
                tau,
                rid: r.below(8),
                n: (0..3).map(|_| r.below(8)).collect(),
                dep: (0..3).collect(),
                walk,
                ci: r.below(11),
                d: r.below(3),
                ts: 1 + r.below(3),
                ti: r.below(3),
                x: r.below(16),
                v: {
                    let l = 1 + r.below(5) as usize;
                    r.bytes(l)
                },
                mid: r.bytes(32),
                post: r.bytes(32),
                parts,
            }
        })
        .collect()
}
