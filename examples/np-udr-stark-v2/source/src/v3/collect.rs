//! SHA-256 job collector for `nearAirV3` tables 0/1 (`sha_t`, `sha_r`, the two
//! `L5` SHA instances).
//!
//! The SHA tables have no entry list of their own: their input is the list of
//! SHA *jobs* (`Gen.Msg = {id, bytes, dmult}`) whose `BYTES` receives and
//! `DIGEST` sends balance the other tables' traffic.  This module builds the
//! jobs exactly as the Lean completeness proof does
//! (`Assembly/TrieSide.lean` `trie_side_exact`, instantiated by
//! `Assembly/RenderV3RcptTrieSide.lean` `rcpt_trie_side`): four job families
//!
//! * **scheduler** `schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us`
//!   (`Assembly/UpsertShaCapacity.lean`, `SchedulerSanityJobs.lean`): per
//!   scheduler call `τ` (main, then each implicit step) the new state value
//!   (`upsertJobId τ 0 = 12 + 16·512τ`) and the bottom-up node outputs of the
//!   upsert (`upsertJobId τ (k+1)`), all calls first; then per call the 64-byte
//!   sanity input `old.sanityHash ‖ sha256(all_shards)` (`K_SCH + 16τ`).
//!   Sources: `ups` entries (`UpsInst.tau/v/parts[].q`, the ups table's `BYTES`
//!   sends `upsBytes`) and `codec` entries (`present/prev_hash/ash`, the codec
//!   `kZ`/`kA` rows' `BYTES` sends);
//! * **native** `jobsToSha (TrieShaEmpty.nativeShaJobsE ns es)`: per node record
//!   `n` (list position) `NPRE(n) = ser false`, `NPOST(n) = ser true`, then per
//!   value record `VPRE(vid) = bytes` **including empty values** (a zero-length
//!   job: the node table receives `DIGEST(VPRE vid, 0, sha256 [])`, no `BYTES`);
//!   sources: `node`, `val` entries;
//! * **receipt** `ReceiptGatedShaJobs.jobs pub ls accts (sourceDup lists)`
//!   (`Candidates/ReceiptGatedShaJobs.lean`): `RC(j)` per applied source list
//!   (`hdrBytes ‖ concat enc`, digest output gated: `dmult = !dup j`, duplicate
//!   occurrences get no digest), then per receipt `r` (global index)
//!   `PEO(r)`, `LEAF(r)` and, with a refund, `RID(r) = rid ‖ u64 height ‖ 0⁸`
//!   (`receiptJobsAt`), then the account jobs `VPOST(k) = post ‖ pre[16..]`
//!   (`accountShaJobs`), then the outcome Merkle jobs `merkleShaJobs leaves`
//!   (`Rcpt/Candidates/MerkleShaJobs.lean`); sources: `rcpt` (`RcptIn`),
//!   `srcp` (the `dup` bits), `acct` entries;
//! * **source** `sourceShaMessages lists entries` (= `AcceptedV3.srcShaAll`):
//!   per non-duplicate block the leaf `SRC(ql)` and the path nodes `SRC(q)`;
//!   source: `srcp` entries.
//!
//! and the two bins `TrieShaTwo.twoShaJobBins` (`Assembly/TrieShaTwo.lean`):
//! `b0 = native ++ src₀` (`sha_t`), `b1 = scheduler ++ receipt ++ src₁`
//! (`sha_r`), where `(src₀, src₁) = splitJobs rows (2^22 − rows native) source`
//! splits the source family between whole jobs (the longest prefix that fits).
//! Every job but the gated `RC` ones has `dmult = true` (`jobsToSha`).
//!
//! **Families not derivable from the supplied entries.**  When the `ups`/`codec`
//! (scheduler) or `rcpt` (receipt) entries are absent, the family can be read
//! from an external job list (`sha_scheduler` / `sha_receipt` in the entry map,
//! e.g. the `np-lean-shabins-v3` dump of a real fixture); otherwise it is empty
//! and reported in [`Collected::notes`].
//!
//! **Bus check.**  [`bus_check`] mirrors the senders' `BYTES` traffic and the
//! receivers' `DIGEST` traffic (`nodeTraffic3`, `valTraffic`, `headTraffic`,
//! `acctV3Traffic`, `srcpTraffic` (dedup form), `rcptTraffic3`, `upsBytes`,
//! codec `BYTES`, `mrk`) from the entry structs and checks that every send is an
//! expected byte of the bins and every receive an expected digest
//! (`Sha.Gen.expectedBytes` / `expectedDigests`).

use std::collections::{BTreeMap, HashMap};

use serde::Deserialize;

use crate::sha::Msg as ShaMessage;

use super::acct::AcctV;
use super::mrksort::{MrkNode, MrkV};
use super::node::{Kid, NodeS3, NodeV3, Slot};
use super::rcpt::{RcptE, RcptIn};
use super::srcp::{SrcpB, SrcpItem};
use super::{HeadE, ValE};

/// `B_BYTES` (`ZkFormal.Near.Ids`).
pub const B_BYTES: usize = 0;
/// `B_DIGEST`.
pub const B_DIGEST: usize = 1;

/// SHA message kinds (`ZkFormal.Near.Ids` / `NearV3.IdsUps` / `Rcpt.Ids`).
pub const K_RC: u64 = 1;
pub const K_RF: u64 = 2;
pub const K_PEO: u64 = 3;
pub const K_LEAF: u64 = 4;
pub const K_RID: u64 = 5;
pub const K_MRK: u64 = 6;
pub const K_NPRE: u64 = 7;
pub const K_NPOST: u64 = 8;
pub const K_VPRE: u64 = 9;
pub const K_VPOST: u64 = 10;
pub const K_SCH: u64 = 11;
pub const K_VUPS: u64 = 12;
pub const K_SRC: u64 = 13;
pub const K_VAK: u64 = 14;

/// SHA rows available per instance (`2^22`, `TrieShaTwo.twoBudget_fit`).
pub const BIN_ROWS: u64 = 1 << 22;

/// `msgId kind idx = kind + 16·idx`.
#[inline]
pub fn msg_id(kind: u64, idx: u64) -> u64 {
    kind + 16 * idx
}

/// `upsertJobId τ j = 12 + 16·(512τ + j)` (`Assembly/UpsertShaJobs.lean`).
#[inline]
pub fn upsert_job_id(tau: u64, j: u64) -> u64 {
    msg_id(K_VUPS, 512 * tau + j)
}

/// The 32-byte SHA-256 digest of a preimage, as `u64`s `< 256`.
pub fn digest(bytes: &[u8]) -> Vec<u64> {
    use sha2::{Digest, Sha256};
    Sha256::digest(bytes).iter().map(|&x| x as u64).collect()
}

fn digest_n(bytes: &[u64]) -> Vec<u64> {
    digest(&bytes.iter().map(|&x| x as u8).collect::<Vec<u8>>())
}

/// `(Gen.msgRows M).length = 1 + 17·nblocks` (`Render.rowsOf`).
#[inline]
pub fn job_rows(len: usize) -> u64 {
    1 + 17 * ((len as u64 + 72) / 64)
}

fn u64_le(x: u64) -> Vec<u64> {
    (0..8).map(|i| (x >> (8 * i)) & 0xff).collect()
}

// ---------------------------------------------------------------------------
// Jobs
// ---------------------------------------------------------------------------

/// One SHA job (`Gen.Msg` with the bytes still as naturals).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Job {
    pub id: u64,
    pub bytes: Vec<u64>,
    pub dmult: bool,
}

impl Job {
    fn new(id: u64, bytes: Vec<u64>) -> Job {
        Job {
            id,
            bytes,
            dmult: true,
        }
    }
    fn rows(&self) -> u64 {
        job_rows(self.bytes.len())
    }
}

fn to_sha(jobs: &[Job]) -> Result<Vec<ShaMessage>, String> {
    jobs.iter()
        .map(|j| {
            if j.bytes.iter().any(|&x| x >= 256) {
                return Err(format!("collect: job {} has a byte >= 256", j.id));
            }
            let id =
                u32::try_from(j.id).map_err(|_| format!("collect: job id {} >= 2^32", j.id))?;
            Ok(ShaMessage {
                id,
                bytes: j.bytes.iter().map(|&x| x as u8).collect(),
                dmult: j.dmult,
            })
        })
        .collect()
}

fn from_json(ms: &[ShaMsgJson]) -> Vec<Job> {
    ms.iter()
        .map(|m| Job {
            id: m.id as u64,
            bytes: m.bytes.iter().map(|&x| x as u64).collect(),
            dmult: m.dmult,
        })
        .collect()
}

// ---------------------------------------------------------------------------
// `NodeV3.ser` (re-derived; the generator's is private)
// ---------------------------------------------------------------------------

fn u32_bytes(n: u64) -> Vec<u64> {
    vec![
        n % 256,
        (n / 256) % 256,
        (n / 65536) % 256,
        (n / 16777216) % 256,
    ]
}

/// `hpN nibs leaf`.
fn hpn(nibs: &[u64], leaf: bool) -> Vec<u64> {
    let leaf_bit = if leaf { 32u64 } else { 0 };
    let mut out = Vec::new();
    if nibs.len() % 2 == 1 {
        out.push(16 + nibs[0] + leaf_bit);
        pack_nibbles(&nibs[1..], &mut out);
    } else {
        out.push(leaf_bit);
        pack_nibbles(nibs, &mut out);
    }
    out
}

fn pack_nibbles(xs: &[u64], out: &mut Vec<u64>) {
    let mut i = 0;
    while i + 1 < xs.len() {
        out.push(xs[i] * 16 + xs[i + 1]);
        i += 2;
    }
}

fn kid_bitmap(kids: &[Kid]) -> u64 {
    kids.iter().enumerate().fold(0u64, |a, (j, k)| {
        a | (if matches!(k, Kid::None) { 0 } else { 1 << j })
    })
}

fn kid_bytes(k: &Kid, post: bool) -> Vec<u64> {
    match k {
        Kid::None => vec![],
        Kid::Hash { h } => h.clone(),
        Kid::Node { pre, post: po, .. } => {
            if post {
                po.clone()
            } else {
                pre.clone()
            }
        }
    }
}

fn slot_bytes(s: &Slot, post: bool) -> Vec<u64> {
    match s {
        Slot::Ref { lenB, h } => {
            let mut v = lenB.clone();
            v.extend_from_slice(h);
            v
        }
        Slot::Val {
            lenB,
            pre,
            post: po,
            ..
        } => {
            let mut v = lenB.clone();
            v.extend_from_slice(if post { po } else { pre });
            v
        }
    }
}

/// `NodeV3.ser post`.
pub fn node_ser(v: &NodeV3, post: bool) -> Vec<u64> {
    match v {
        NodeV3::Leaf { key, v, memB } => {
            let h = hpn(key, true);
            let mut o = vec![0u64];
            o.extend(u32_bytes(h.len() as u64));
            o.extend(h);
            o.extend(slot_bytes(v, post));
            o.extend_from_slice(memB);
            o
        }
        NodeV3::Ext { key, kid, memB } => {
            let h = hpn(key, false);
            let mut o = vec![3u64];
            o.extend(u32_bytes(h.len() as u64));
            o.extend(h);
            o.extend(kid_bytes(kid, post));
            o.extend_from_slice(memB);
            o
        }
        NodeV3::Branch { v, kids, memB } => {
            let mut o = match v {
                None => vec![1u64],
                Some(s) => {
                    let mut x = vec![2u64];
                    x.extend(slot_bytes(s, post));
                    x
                }
            };
            let bm = kid_bitmap(kids);
            o.push(bm % 256);
            o.push(bm / 256);
            for k in kids {
                o.extend(kid_bytes(k, post));
            }
            o.extend_from_slice(memB);
            o
        }
    }
}

/// `NodeV3.revealed`: `(cid, clen, pre, post)` in slot order.
fn node_revealed(v: &NodeV3) -> Vec<(u64, u64, Vec<u64>, Vec<u64>)> {
    let kid = |k: &Kid| match k {
        Kid::Node {
            cid,
            clen,
            pre,
            post,
            ..
        } => Some((*cid, *clen, pre.clone(), post.clone())),
        _ => None,
    };
    match v {
        NodeV3::Ext { kid: k, .. } => kid(k).into_iter().collect(),
        NodeV3::Branch { kids, .. } => kids.iter().filter_map(kid).collect(),
        _ => vec![],
    }
}

/// `NodeV3.value`: `(vid, vlen, pre, post, written)`.
fn node_value(v: &NodeV3) -> Option<(u64, u64, Vec<u64>, Vec<u64>, bool)> {
    let s = match v {
        NodeV3::Leaf { v: s, .. } => s,
        NodeV3::Branch { v: Some(s), .. } => s,
        _ => return None,
    };
    match s {
        Slot::Val {
            vid,
            vlen,
            pre,
            post,
            written,
            ..
        } => Some((*vid, *vlen, pre.clone(), post.clone(), *written)),
        Slot::Ref { .. } => None,
    }
}

// ---------------------------------------------------------------------------
// Receipt encodings (`Near/Extract/RcptView.lean` `RcptV.enc/peo/leaf`)
// ---------------------------------------------------------------------------

/// `u32r x = [x, 0, 0, 0]` (`Near/Extract/Common.lean`).
fn u32r(x: u64) -> Vec<u64> {
    vec![x, 0, 0, 0]
}

/// `borshN s = u32r |s| ++ s`.
fn borsh_n(s: &[u64]) -> Vec<u64> {
    let mut v = u32r(s.len() as u64);
    v.extend_from_slice(s);
    v
}

/// `G_LEn`.
const G_LEN: [u64; 8] = [196, 164, 183, 246, 51, 0, 0, 0];
/// `tailN`.
const TAIL_N: [u64; 13] = [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3];

/// `RcptV.enc`: the receipt's encoding as the `RC` rows emit it.
pub fn rcpt_enc(x: &RcptE) -> Vec<u64> {
    let mut o = borsh_n(&x.p);
    o.extend(borsh_n(&x.v));
    o.extend_from_slice(&x.rid);
    o.push(0);
    o.extend(borsh_n(&x.s));
    o.push(x.kt);
    o.extend_from_slice(&x.pk);
    o.extend_from_slice(&x.gp);
    o.extend_from_slice(&TAIL_N);
    o.extend_from_slice(&x.dep);
    o
}

/// `RcptV.peo`: the partial outcome encoding.
pub fn rcpt_peo(x: &RcptE) -> Vec<u64> {
    let mut o = u32r(if x.hr { 1 } else { 0 });
    if x.hr {
        o.extend_from_slice(&x.rfid);
    }
    o.extend_from_slice(&G_LEN);
    o.extend_from_slice(&x.burnt);
    o.extend(borsh_n(&x.v));
    o.extend_from_slice(&[2, 0, 0, 0, 0]);
    o
}

/// `RcptV.leaf = [2,0,0,0] ++ rid ++ peoh`.
pub fn rcpt_leaf(x: &RcptE) -> Vec<u64> {
    let mut o = vec![2, 0, 0, 0];
    o.extend_from_slice(&x.rid);
    o.extend_from_slice(&x.peoh);
    o
}

/// The `RID` preimage `rid ++ pubBytes PH_HEIGHT 8 ++ 0⁸`.
fn rcpt_rid_pre(x: &RcptE, height: u64) -> Vec<u64> {
    let mut o = x.rid.clone();
    o.extend(u64_le(height));
    o.extend(std::iter::repeat_n(0, 8));
    o
}

/// `hdrBytes pub L = pubBytes PH_OWN 8 ++ [n0, n1, 0, 0]`.
fn rcpt_hdr(own: u64, n0: u64, n1: u64) -> Vec<u64> {
    let mut o = u64_le(own);
    o.extend_from_slice(&[n0, n1, 0, 0]);
    o
}

// ---------------------------------------------------------------------------
// Lenient views of the scheduler-side entries (only the SHA-relevant fields)
// ---------------------------------------------------------------------------

/// The fields of a `ups` entry (`UpsInst`) the collector reads.
#[derive(Clone, Debug, Default, Deserialize)]
pub struct UpsLite {
    #[serde(default)]
    pub tau: u64,
    #[serde(default)]
    pub v: Vec<u64>,
    #[serde(default)]
    pub parts: Vec<UpsPartLite>,
}

/// The fields of a `UpsPartI` the collector reads (`q`: the bytes of `Q`).
#[derive(Clone, Debug, Default, Deserialize)]
pub struct UpsPartLite {
    #[serde(default)]
    pub q: Vec<u64>,
}

/// The fields of a `codec` block (`SchedIn`) the collector reads: whether a
/// canonical prior state is present, its sanity hash and `sha256(all_shards)`.
#[derive(Clone, Debug, Default, Deserialize)]
pub struct CodecLite {
    #[serde(default)]
    pub tau: Option<u64>,
    #[serde(default)]
    pub present: bool,
    #[serde(default)]
    pub prev_hash: Vec<u64>,
    #[serde(default)]
    pub ash: Vec<u64>,
}

impl CodecLite {
    /// `schedulerSanityInput = old.sanityHash ++ allShardsHash`, `old =
    /// State.initial` (sanity hash `zeroHash`) without a canonical prior.
    pub fn sanity(&self) -> Vec<u64> {
        let mut o = if self.present {
            self.prev_hash.clone()
        } else {
            vec![0; 32]
        };
        o.extend_from_slice(&self.ash);
        o
    }
}

fn parse_codec(s: &str) -> Result<Vec<CodecLite>, String> {
    if let Ok(v) = serde_json::from_str::<Vec<CodecLite>>(s) {
        return Ok(v);
    }
    serde_json::from_str::<CodecLite>(s)
        .map(|c| vec![c])
        .map_err(|e| format!("collect: codec entries: {e}"))
}

// ---------------------------------------------------------------------------
// The four families
// ---------------------------------------------------------------------------

/// `jobsToSha (nativeShaJobsE ns es)`: `NPRE(n)`, `NPOST(n)` per node record
/// (list position `n`), then `VPRE(vid)` per value record, empty ones included.
pub fn native_family(nodes: &[NodeS3], vals: &[ValE]) -> Vec<Job> {
    let mut out = Vec::with_capacity(2 * nodes.len() + vals.len());
    for (n, s) in nodes.iter().enumerate() {
        out.push(Job::new(msg_id(K_NPRE, n as u64), node_ser(&s.v, false)));
        out.push(Job::new(msg_id(K_NPOST, n as u64), node_ser(&s.v, true)));
    }
    for e in vals {
        out.push(Job::new(msg_id(K_VPRE, e.vid), e.bytes.clone()));
    }
    out
}

/// `schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us` from the ups instances
/// (in `τ` order) and the codec blocks (the `i`-th block is call `τ = i` unless
/// it names its `tau`).
pub fn scheduler_family(ups: &[UpsLite], codec: &[CodecLite]) -> Vec<Job> {
    let mut us: Vec<&UpsLite> = ups.iter().collect();
    us.sort_by_key(|u| u.tau);
    let mut out = Vec::new();
    for u in &us {
        out.push(Job::new(upsert_job_id(u.tau, 0), u.v.clone()));
        for (k, p) in u.parts.iter().enumerate() {
            out.push(Job::new(upsert_job_id(u.tau, k as u64 + 1), p.q.clone()));
        }
    }
    let mut cs: Vec<(u64, &CodecLite)> = codec
        .iter()
        .enumerate()
        .map(|(i, c)| (c.tau.unwrap_or(i as u64), c))
        .collect();
    cs.sort_by_key(|c| c.0);
    for (tau, c) in cs {
        out.push(Job::new(msg_id(K_SCH, tau), c.sanity()));
    }
    out
}

/// `size n j` (`MrkGen.size`).
fn mrk_size(n: u64, j: u64) -> u64 {
    (0..j).fold(n, |s, _| s.div_ceil(2))
}

/// `qBase n j` (`MrkGen.qBase`).
fn mrk_qbase(n: u64, j: u64) -> u64 {
    (2..=j).map(|l| mrk_size(n, l - 2) / 2).sum()
}

/// `mrkShape n = mrkLevels (n + 1) 1 n`: `(level, index, hashed)`.
fn mrk_shape(n: u64) -> Vec<(u64, u64, bool)> {
    let mut out = Vec::new();
    let (mut fuel, mut j, mut sp) = (n + 1, 1u64, n);
    while fuel > 0 {
        let s = sp.div_ceil(2);
        for i in 0..s {
            out.push((j, i, 2 * i + 1 < sp));
        }
        if s == 1 {
            break;
        }
        fuel -= 1;
        j += 1;
        sp = s;
    }
    out
}

/// `merkleShaJobs leaves` (`Rcpt/Candidates/MerkleShaJobs.lean`): the hashed
/// nodes of the outcome tree in `mrkShape` order, `MRK(qBase n j + i)` with
/// preimage `C(2i).dig ++ C(2i+1).dig` over the level below.
pub fn merkle_jobs(leaves: &[Vec<u64>]) -> Vec<Job> {
    let n = leaves.len() as u64;
    // level digests (`levelsFromLeaves`); a promoted node keeps its child's digest
    let mut levels: Vec<Vec<Vec<u64>>> = vec![leaves.iter().map(|b| digest_n(b)).collect()];
    while levels.last().map(|l| l.len()).unwrap_or(0) > 1 {
        let prev = levels.last().unwrap();
        let next = (0..prev.len().div_ceil(2))
            .map(|i| {
                if 2 * i + 1 < prev.len() {
                    let mut b = prev[2 * i].clone();
                    b.extend_from_slice(&prev[2 * i + 1]);
                    digest_n(&b)
                } else {
                    prev[2 * i].clone()
                }
            })
            .collect();
        levels.push(next);
    }
    let dflt: Vec<u64> = vec![];
    mrk_shape(n)
        .into_iter()
        .filter(|x| x.2)
        .map(|(j, i, _)| {
            let c = levels.get(j as usize - 1);
            let get = |k: u64| c.and_then(|l| l.get(k as usize)).unwrap_or(&dflt).clone();
            let mut b = get(2 * i);
            b.extend(get(2 * i + 1));
            Job::new(msg_id(K_MRK, mrk_qbase(n, j) + i), b)
        })
        .collect()
}

/// `accountShaJobs as`: `VPOST(k) = post ++ pre.drop 16`.
pub fn account_jobs(accts: &[AcctV]) -> Vec<Job> {
    accts
        .iter()
        .map(|a| {
            let mut b = a.post.clone();
            b.extend(a.pre.iter().skip(16).copied());
            Job::new(msg_id(K_VPOST, a.k), b)
        })
        .collect()
}

/// `ReceiptGatedShaJobs.jobs pub ls accts dup`: `RC(j)` per list (digest gated
/// by `!dup j`), the per-receipt `PEO`/`LEAF`/`RID` jobs, the account jobs and
/// the outcome Merkle jobs.
pub fn receipt_family(rc: &RcptIn, dup: &dyn Fn(usize) -> bool, accts: &[AcctV]) -> Vec<Job> {
    let mut out = Vec::new();
    for (j, l) in rc.lists.iter().enumerate() {
        let mut b = rcpt_hdr(rc.own, l.n0, l.n1);
        for x in &l.rs {
            b.extend(rcpt_enc(x));
        }
        out.push(Job {
            id: msg_id(K_RC, j as u64),
            bytes: b,
            dmult: !dup(j),
        });
    }
    let flat: Vec<&RcptE> = rc.lists.iter().flat_map(|l| l.rs.iter()).collect();
    for (r, x) in flat.iter().enumerate() {
        let r = r as u64;
        out.push(Job::new(msg_id(K_PEO, r), rcpt_peo(x)));
        out.push(Job::new(msg_id(K_LEAF, r), rcpt_leaf(x)));
        if x.hr {
            out.push(Job::new(msg_id(K_RID, r), rcpt_rid_pre(x, rc.height)));
        }
    }
    out.extend(account_jobs(accts));
    let leaves: Vec<Vec<u64>> = flat.iter().map(|x| rcpt_leaf(x)).collect();
    out.extend(merkle_jobs(&leaves));
    out
}

/// `DedupProof.payloads`: a duplicate block hashes nothing; a computed block its
/// leaf `SRC(ql)` and path nodes `SRC(q)`.
pub fn source_family(bs: &[SrcpB]) -> Vec<Job> {
    let mut out = Vec::new();
    for b in bs.iter().filter(|b| !b.dup) {
        out.push(Job::new(msg_id(K_SRC, b.ql), b.leaf.clone()));
        for it in &b.path {
            out.push(Job::new(msg_id(K_SRC, it.q), srcp_item_bytes(it)));
        }
    }
    out
}

/// `SrcpItem.bytes = if dir then acc ++ sib else sib ++ acc`.
fn srcp_item_bytes(it: &SrcpItem) -> Vec<u64> {
    let mut v = Vec::new();
    if it.dir {
        v.extend_from_slice(&it.acc);
        v.extend_from_slice(&it.sib);
    } else {
        v.extend_from_slice(&it.sib);
        v.extend_from_slice(&it.acc);
    }
    v
}

/// The four job families, in the proof's order.
#[derive(Clone, Debug, Default)]
pub struct Families {
    pub scheduler: Vec<Job>,
    pub native: Vec<Job>,
    pub receipt: Vec<Job>,
    pub source: Vec<Job>,
}

/// `splitJobs weight cap xs`: the longest prefix whose running weight fits `cap`.
pub fn split_jobs(cap: u64, xs: &[Job]) -> usize {
    let mut left = cap;
    for (i, x) in xs.iter().enumerate() {
        let w = x.rows();
        if w > left {
            return i;
        }
        left -= w;
    }
    xs.len()
}

/// `twoShaJobBins rows scheduler native receipt source = [b0, b1]` and the
/// source split capacity `2^22 − rows native` (truncated at `0`).
pub fn two_bins(f: &Families) -> (Vec<Job>, Vec<Job>, u64) {
    let nat: u64 = f.native.iter().map(Job::rows).sum();
    let cap = BIN_ROWS.saturating_sub(nat);
    let k = split_jobs(cap, &f.source);
    let mut b0 = f.native.clone();
    b0.extend_from_slice(&f.source[..k]);
    let mut b1 = f.scheduler.clone();
    b1.extend_from_slice(&f.receipt);
    b1.extend_from_slice(&f.source[k..]);
    (b0, b1, cap)
}

// ---------------------------------------------------------------------------
// Raw bus traffic (mirrors the senders' / receivers' `*Traffic`)
// ---------------------------------------------------------------------------

/// A table's SHA traffic: `BYTES` sends `(Id, bytes)` (`emitAt Id 0 bytes`) and
/// `DIGEST` receives `(Id, len, digest)` (`digMsg`).
#[derive(Clone, Debug, Default)]
pub struct Raw {
    pub sends: Vec<(u64, u64, Vec<u64>)>,
    pub recvs: Vec<(u64, usize, Vec<u64>)>,
}

impl Raw {
    /// `emitAt id off bytes`.
    fn emit_at(&mut self, id: u64, off: u64, bytes: &[u64]) {
        self.sends.push((id, off, bytes.to_vec()));
    }
    fn emit(&mut self, id: u64, bytes: &[u64]) {
        self.emit_at(id, 0, bytes);
    }
    fn recv(&mut self, id: u64, len: usize, d: &[u64]) {
        self.recvs.push((id, len, d.to_vec()));
    }
}

/// `nodeSends3 vs B_BYTES` ++ `nodeRecvs3 vs B_DIGEST`.
pub fn node_raw(vs: &[NodeS3]) -> Raw {
    let mut r = Raw::default();
    for (n, s) in vs.iter().enumerate() {
        r.emit(msg_id(K_NPRE, n as u64), &node_ser(&s.v, false));
        r.emit(msg_id(K_NPOST, n as u64), &node_ser(&s.v, true));
        for (c, l, pre, po) in node_revealed(&s.v) {
            r.recv(msg_id(K_NPRE, c), l as usize, &pre);
            r.recv(msg_id(K_NPOST, c), l as usize, &po);
        }
        if let Some((i, l, pre, po, w)) = node_value(&s.v) {
            r.recv(msg_id(K_VPRE, i), l as usize, &pre);
            if w {
                r.recv(msg_id(K_VPOST, i), l as usize, &po);
            }
        }
    }
    r
}

/// `valSends es B_BYTES` (`VPRE`, none for an empty value); no digest receives.
pub fn val_raw(es: &[ValE]) -> Raw {
    let mut r = Raw::default();
    for e in es.iter().filter(|e| !e.vz) {
        r.emit(msg_id(K_VPRE, e.vid), &e.bytes);
    }
    r
}

/// `headRecvs hs B_DIGEST` (`NPRE`/`NPOST` of the root record).
pub fn head_raw(hs: &[HeadE]) -> Raw {
    let mut r = Raw::default();
    for h in hs {
        r.recv(msg_id(K_NPRE, h.rid), h.rlen as usize, &h.pre);
        r.recv(msg_id(K_NPOST, h.rid), h.rlen as usize, &h.post);
    }
    r
}

/// `acctV3Sends as B_BYTES`: `VPOST(k) = post ++ pre.drop 16`.
pub fn acct_raw(as_: &[AcctV]) -> Raw {
    let mut r = Raw::default();
    for j in account_jobs(as_) {
        r.emit(j.id, &j.bytes);
    }
    r
}

/// The dedup source table's traffic (`ddTraffic`): a computed block sends its
/// leaf / path payloads and receives the root `SRC(qe)`, the `RC(j)` digest
/// (`= leaf`) and the path digests; a duplicate block touches no SHA bus.
pub fn srcp_raw(bs: &[SrcpB]) -> Raw {
    let mut r = Raw::default();
    for b in bs.iter().filter(|b| !b.dup) {
        r.recv(msg_id(K_SRC, b.qe), b.le as usize, &b.root);
        r.emit(msg_id(K_SRC, b.ql), &b.leaf);
        r.recv(msg_id(K_RC, b.j), b.l as usize, &b.leaf);
        for it in &b.path {
            r.emit(msg_id(K_SRC, it.q), &srcp_item_bytes(it));
            r.recv(msg_id(K_SRC, it.pq), it.pl as usize, &it.acc);
        }
    }
    r
}

/// `rcptSends3 pub ls B_BYTES` (without the public `RF` refund fragments) and
/// `rcptRecvs3 ls B_DIGEST`.
pub fn rcpt_raw(rc: &RcptIn) -> Raw {
    let mut r = Raw::default();
    let mut gr = 0u64;
    for (j, l) in rc.lists.iter().enumerate() {
        let j = j as u64;
        r.emit(msg_id(K_RC, j), &rcpt_hdr(rc.own, l.n0, l.n1));
        let mut off = 12u64;
        for x in &l.rs {
            let enc = rcpt_enc(x);
            r.emit_at(msg_id(K_RC, j), off, &enc);
            off += enc.len() as u64;
            let peo = rcpt_peo(x);
            r.emit(msg_id(K_PEO, gr), &peo);
            r.emit(msg_id(K_LEAF, gr), &rcpt_leaf(x));
            if x.hr {
                r.emit(msg_id(K_RID, gr), &rcpt_rid_pre(x, rc.height));
                r.recv(msg_id(K_RID, gr), 48, &x.rfid);
            }
            r.recv(msg_id(K_PEO, gr), peo.len(), &x.peoh);
            gr += 1;
        }
    }
    r
}

/// The ups table's `BYTES` sends `upsBytes` (value, then each part's `Q`).
pub fn ups_raw(us: &[UpsLite]) -> Raw {
    let mut r = Raw::default();
    for u in us {
        r.emit(upsert_job_id(u.tau, 0), &u.v);
        for (k, p) in u.parts.iter().enumerate() {
            r.emit(upsert_job_id(u.tau, k as u64 + 1), &p.q);
        }
    }
    r
}

/// The codec's `BYTES` sends (`kZ`/`kA` rows: `SCH(τ)`, the sanity input) and its
/// `DIGEST` receive (`dgg`: the new sanity hash).
pub fn codec_raw(cs: &[CodecLite]) -> Raw {
    let mut r = Raw::default();
    for (i, c) in cs.iter().enumerate() {
        let tau = c.tau.unwrap_or(i as u64);
        let s = c.sanity();
        r.emit(msg_id(K_SCH, tau), &s);
        r.recv(msg_id(K_SCH, tau), 64, &digest_n(&s));
    }
    r
}

/// `mrk`: the hashed nodes (`l ++ r`, `MRK(#hashed before)`) and the child digests.
pub fn mrk_raw(v: &MrkV) -> Raw {
    let mut r = Raw::default();
    let mut hbefore = 0u64;
    for nd in &v.nodes {
        if let MrkNode::Hashed {
            l_id,
            l_len,
            l,
            r_id,
            r_len,
            r: rw,
        } = nd
        {
            let mut b = l.clone();
            b.extend_from_slice(rw);
            r.emit(msg_id(K_MRK, hbefore), &b);
            r.recv(*l_id, *l_len as usize, l);
            r.recv(*r_id, *r_len as usize, rw);
            hbefore += 1;
        }
    }
    r
}

/// The outcome of [`bus_check`].
#[derive(Clone, Debug, Default)]
pub struct BusReport {
    /// sends checked / sends that are not an expected byte of the bins
    pub sends: usize,
    pub bad_sends: Vec<(u64, u64, u64)>,
    /// receives checked / receives that are not an expected digest of the bins
    pub recvs: usize,
    pub bad_recvs: Vec<(u64, usize)>,
    /// expected bytes / digests of the bins not produced by any checked table
    pub unsent: usize,
    pub unreceived: usize,
}

impl BusReport {
    pub fn ok(&self) -> bool {
        self.bad_sends.is_empty() && self.bad_recvs.is_empty()
    }
}

/// Multiset inclusion of the tables' `BYTES` sends in `expectedBytes (b0 ++ b1)`
/// and of their `DIGEST` receives in `expectedDigests (b0 ++ b1)`.
pub fn bus_check(raws: &[Raw], jobs: &[Job]) -> BusReport {
    let mut want_b: BTreeMap<(u64, u64, u64), i64> = BTreeMap::new();
    let mut want_d: BTreeMap<(u64, usize, Vec<u64>), i64> = BTreeMap::new();
    for j in jobs {
        for (p, &x) in j.bytes.iter().enumerate() {
            *want_b.entry((j.id, p as u64, x)).or_default() += 1;
        }
        if j.dmult {
            *want_d
                .entry((j.id, j.bytes.len(), digest_n(&j.bytes)))
                .or_default() += 1;
        }
    }
    let mut rep = BusReport::default();
    for raw in raws {
        for (id, off, bs) in &raw.sends {
            for (p, &x) in bs.iter().enumerate() {
                rep.sends += 1;
                let key = (*id, off + p as u64, x);
                match want_b.get_mut(&key) {
                    Some(c) if *c > 0 => *c -= 1,
                    _ => rep.bad_sends.push(key),
                }
            }
        }
        for (id, len, d) in &raw.recvs {
            rep.recvs += 1;
            match want_d.get_mut(&(*id, *len, d.clone())) {
                Some(c) if *c > 0 => *c -= 1,
                _ => rep.bad_recvs.push((*id, *len)),
            }
        }
    }
    rep.unsent = want_b.values().map(|&c| c.max(0) as usize).sum();
    rep.unreceived = want_d.values().map(|&c| c.max(0) as usize).sum();
    rep
}

// ---------------------------------------------------------------------------
// Entry bundle
// ---------------------------------------------------------------------------

/// The per-table entry lists the collector consumes (absent = empty / `None`),
/// plus the external family lists for families whose tables are absent.
#[derive(Clone, Debug, Default)]
pub struct Bundle {
    pub node: Vec<NodeS3>,
    pub val: Vec<ValE>,
    pub head: Vec<HeadE>,
    pub acct: Vec<AcctV>,
    pub srcp: Vec<SrcpB>,
    pub mrk: Option<MrkV>,
    pub rcpt: Option<RcptIn>,
    pub ups: Option<Vec<UpsLite>>,
    pub codec: Option<Vec<CodecLite>>,
    /// `sha_scheduler`: the scheduler family as a `Gen.Msg` list
    pub ext_scheduler: Option<Vec<ShaMsgJson>>,
    /// `sha_receipt`: the receipt family as a `Gen.Msg` list
    pub ext_receipt: Option<Vec<ShaMsgJson>>,
}

/// The collector's result.
#[derive(Clone, Debug, Default)]
pub struct Collected {
    pub families: Families,
    pub b0: Vec<Job>,
    pub b1: Vec<Job>,
    pub cap: u64,
    /// how each family was obtained / what is missing
    pub notes: Vec<String>,
}

/// Build the four families and the two bins of `bundle`.
pub fn collect(bundle: &Bundle) -> Collected {
    let mut notes = Vec::new();
    let native = native_family(&bundle.node, &bundle.val);
    if bundle.node.is_empty() && bundle.val.is_empty() {
        notes.push("native: no node/val entries".into());
    }
    let scheduler = match (&bundle.ups, &bundle.codec, &bundle.ext_scheduler) {
        (Some(u), c, _) => {
            if c.is_none() {
                notes.push("scheduler: no codec entries (sanity jobs missing)".into());
            }
            scheduler_family(u, c.as_deref().unwrap_or(&[]))
        }
        (None, _, Some(e)) => {
            notes.push("scheduler: external job list (sha_scheduler)".into());
            from_json(e)
        }
        (None, _, None) => {
            notes.push("scheduler: no ups/codec entries".into());
            vec![]
        }
    };
    let receipt = match (&bundle.rcpt, &bundle.ext_receipt) {
        (Some(rc), _) => {
            if bundle.srcp.is_empty() && !rc.lists.is_empty() {
                notes.push("receipt: no srcp entries, RC digests assumed ungated".into());
            }
            let dup = |j: usize| bundle.srcp.iter().any(|b| b.j == j as u64 && b.dup);
            receipt_family(rc, &dup, &bundle.acct)
        }
        (None, Some(e)) => {
            notes.push("receipt: external job list (sha_receipt)".into());
            from_json(e)
        }
        (None, None) => {
            notes.push("receipt: no rcpt entries (account jobs only)".into());
            account_jobs(&bundle.acct)
        }
    };
    let source = source_family(&bundle.srcp);
    let families = Families {
        scheduler,
        native,
        receipt,
        source,
    };
    let (b0, b1, cap) = two_bins(&families);
    Collected {
        families,
        b0,
        b1,
        cap,
        notes,
    }
}

/// The supplied tables' raw SHA traffic (for [`bus_check`]).
pub fn bundle_raws(bundle: &Bundle) -> Vec<Raw> {
    let mut raws = vec![
        node_raw(&bundle.node),
        val_raw(&bundle.val),
        head_raw(&bundle.head),
        acct_raw(&bundle.acct),
        srcp_raw(&bundle.srcp),
    ];
    if let Some(rc) = &bundle.rcpt {
        raws.push(rcpt_raw(rc));
    }
    if let Some(u) = &bundle.ups {
        raws.push(ups_raw(u));
    }
    if let Some(c) = &bundle.codec {
        raws.push(codec_raw(c));
    }
    if let Some(m) = &bundle.mrk {
        raws.push(mrk_raw(m));
    }
    raws
}

/// Parse a table's entry JSON, if present in `entries`.
fn get<T: serde::de::DeserializeOwned>(
    entries: &HashMap<String, String>,
    name: &str,
) -> Result<Option<T>, String> {
    match entries.get(name) {
        Some(s) if !s.trim().is_empty() => serde_json::from_str(s)
            .map(Some)
            .map_err(|e| format!("collect: {name} entries: {e}")),
        _ => Ok(None),
    }
}

/// The entry-map names the collector reads (besides the tables: the external
/// family lists).
pub const EXTRA_INPUTS: &[&str] = &["sha_scheduler", "sha_receipt"];

/// Build the [`Bundle`] from a map `name → JSON` (table entries and
/// [`EXTRA_INPUTS`]).
pub fn bundle_from_entries(entries: &HashMap<String, String>) -> Result<Bundle, String> {
    let codec = match entries.get("codec") {
        Some(s) if !s.trim().is_empty() => Some(parse_codec(s)?),
        _ => None,
    };
    Ok(Bundle {
        node: get(entries, "node")?.unwrap_or_default(),
        val: get(entries, "val")?.unwrap_or_default(),
        head: get(entries, "head")?.unwrap_or_default(),
        acct: get(entries, "acct")?.unwrap_or_default(),
        srcp: get(entries, "srcp")?.unwrap_or_default(),
        mrk: get(entries, "mrk")?,
        rcpt: get(entries, "rcpt")?,
        ups: get(entries, "ups")?,
        codec,
        ext_scheduler: get(entries, "sha_scheduler")?,
        ext_receipt: get(entries, "sha_receipt")?,
    })
}

/// The `Gen.Msg` JSON mirror (`{id, bytes, dmult}`), as [`super::sha`] parses.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ShaMsgJson {
    pub id: u32,
    pub bytes: Vec<u8>,
    pub dmult: bool,
}

/// Serialize a message list as `Gen.Msg` JSON.
pub fn msgs_json(msgs: &[ShaMessage]) -> Result<String, String> {
    let j: Vec<ShaMsgJson> = msgs
        .iter()
        .map(|m| ShaMsgJson {
            id: m.id,
            bytes: m.bytes.clone(),
            dmult: m.dmult,
        })
        .collect();
    serde_json::to_string(&j).map_err(|e| e.to_string())
}

/// Serialize jobs as `Gen.Msg` JSON (bytes checked `< 256`).
pub fn jobs_json(jobs: &[Job]) -> Result<String, String> {
    msgs_json(&to_sha(jobs)?)
}

/// The collector's full result as one JSON object: `b0`, `b1`, the four
/// families, `cap` and `notes` (the `np-lean-shabins-v3` layout).
pub fn collected_json(c: &Collected) -> Result<String, String> {
    let v = |jobs: &[Job]| -> Result<serde_json::Value, String> {
        serde_json::from_str(&jobs_json(jobs)?).map_err(|e| e.to_string())
    };
    let j = serde_json::json!({
        "b0": v(&c.b0)?,
        "b1": v(&c.b1)?,
        "scheduler": v(&c.families.scheduler)?,
        "native": v(&c.families.native)?,
        "receipt": v(&c.families.receipt)?,
        "source": v(&c.families.source)?,
        "cap": c.cap,
        "notes": c.notes,
    });
    Ok(j.to_string())
}

/// Collect the two SHA instances from a map `name → JSON` and return
/// `(sha_t_json, sha_r_json)` = `(b0, b1)` as `Gen.Msg` JSON.
pub fn instances_from_entries(
    entries: &HashMap<String, String>,
) -> Result<(String, String), String> {
    let c = collect(&bundle_from_entries(entries)?);
    Ok((jobs_json(&c.b0)?, jobs_json(&c.b1)?))
}

/// D1 (`nearAirV3D1`, lane v3-d1-tables): the two SHA instances from the entry map with the
/// outcome-Merkle jobs over **all** leaves (`all_leaves` = every outcome leaf preimage:
/// transactions, local receipts, incoming receipts; the first `M0` leaves are public digests,
/// only the inner nodes are hashed) in place of the receipts-only ones, and the access-key
/// post values `VPOST(vid) = nonce ‖ [1]` of the FullAccess keys transactions read
/// (`akm_posts`) appended to the receipt family.
pub fn instances_d1(
    entries: &HashMap<String, String>,
    all_leaves: &[Vec<u8>],
    akm_posts: &[(u64, Vec<u8>)],
) -> Result<(String, String), String> {
    let mut c = collect(&bundle_from_entries(entries)?);
    let mrk_kind = |id: u64| id % 16 == K_MRK;
    c.families.receipt.retain(|j| !mrk_kind(j.id));
    for (vid, b) in akm_posts {
        c.families.receipt.push(Job::new(
            msg_id(K_VPOST, *vid),
            b.iter().map(|&x| x as u64).collect(),
        ));
    }
    let leaves: Vec<Vec<u64>> = all_leaves
        .iter()
        .map(|b| b.iter().map(|&x| x as u64).collect())
        .collect();
    c.families.receipt.extend(merkle_jobs(&leaves));
    let (b0, b1, _) = two_bins(&c.families);
    Ok((jobs_json(&b0)?, jobs_json(&b1)?))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::v3::rcpt::ListV3;

    fn leaf_node(key: Vec<u64>, h: Vec<u64>) -> NodeS3 {
        NodeS3 {
            v: NodeV3::Leaf {
                key,
                v: Slot::Ref {
                    lenB: vec![2, 0, 0, 0],
                    h,
                },
                memB: vec![0; 8],
            },
            tau: 0,
            depth: 0,
            res: 0,
            uses: vec![0],
            ubm: 0,
            dup: false,
            hd: false,
            rep_e: 0,
            ucid: vec![],
            m_u: vec![],
        }
    }

    fn val(vid: u64, bytes: Vec<u64>) -> ValE {
        ValE {
            vid,
            len: bytes.len() as u64,
            vz: bytes.is_empty(),
            dup: false,
            hd: false,
            rep_e: 0,
            bytes,
        }
    }

    #[test]
    fn rows_formula() {
        // `Render.rowsOf`: 0 → 18, 55 → 18, 56 → 35, 64 → 35, 68 → 35, 133 → 52
        for (l, r) in [
            (0, 18),
            (48, 18),
            (55, 18),
            (56, 35),
            (64, 35),
            (68, 35),
            (133, 52),
        ] {
            assert_eq!(job_rows(l), r, "len {l}");
        }
    }

    #[test]
    fn native_includes_empty_values() {
        let n = leaf_node(vec![1, 2], digest(b"he"));
        let f = native_family(&[n.clone()], &[val(0, vec![104, 105]), val(1, vec![])]);
        let ids: Vec<u64> = f.iter().map(|j| j.id).collect();
        assert_eq!(
            ids,
            vec![
                msg_id(K_NPRE, 0),
                msg_id(K_NPOST, 0),
                msg_id(K_VPRE, 0),
                msg_id(K_VPRE, 1)
            ]
        );
        assert!(f[3].bytes.is_empty() && f[3].dmult);
        assert_eq!(f[0].bytes, node_ser(&n.v, false));
        // the node/val BYTES sends are exactly the native bytes; the empty value sends none
        let rep = bus_check(
            &[
                node_raw(&[n]),
                val_raw(&[val(0, vec![104, 105]), val(1, vec![])]),
            ],
            &f,
        );
        assert!(rep.ok() && rep.unsent == 0, "{rep:?}");
    }

    #[test]
    fn merkle_shape_and_ids() {
        for n in 0..12usize {
            let leaves: Vec<Vec<u64>> = (0..n).map(|r| vec![r as u64; 68]).collect();
            let js = merkle_jobs(&leaves);
            assert_eq!(js.len(), n.saturating_sub(1), "n = {n}");
            let ids: Vec<u64> = js.iter().map(|j| j.id).collect();
            let want: Vec<u64> = (0..js.len() as u64).map(|q| msg_id(K_MRK, q)).collect();
            assert_eq!(ids, want, "MRK ids are the hashed-node counter, n = {n}");
        }
        // n = 3: level 1 hashes (0,1), promotes 2; level 2 hashes (h01, d2)
        let leaves: Vec<Vec<u64>> = (0..3).map(|r| vec![r; 68]).collect();
        let d: Vec<Vec<u64>> = leaves.iter().map(|l| digest_n(l)).collect();
        let js = merkle_jobs(&leaves);
        assert_eq!(js[0].bytes, [d[0].clone(), d[1].clone()].concat());
        let h01 = digest_n(&js[0].bytes);
        assert_eq!(js[1].bytes, [h01, d[2].clone()].concat());
    }

    fn rcpt_x(hr: bool, seed: u64) -> RcptE {
        RcptE {
            p: vec![97 + seed; 3],
            v: vec![98; 4],
            s: vec![99; 2],
            rid: vec![seed; 32],
            kt: 0,
            pk: vec![7; 32],
            gp: vec![1; 16],
            dep: vec![2; 16],
            hr,
            burnt: vec![3; 16],
            rfid: vec![4; 32],
            peoh: vec![5; 32],
            ..Default::default()
        }
    }

    #[test]
    fn receipt_family_layout_and_gating() {
        let rc = RcptIn {
            lists: vec![
                ListV3 {
                    n0: 2,
                    n1: 0,
                    rs: vec![rcpt_x(true, 1), rcpt_x(false, 2)],
                },
                ListV3 {
                    n0: 0,
                    n1: 0,
                    rs: vec![],
                },
            ],
            own: 3,
            height: 0x0102,
            bgp: 0,
            d1: None,
        };
        let dup = |j: usize| j == 1;
        let acct = AcctV {
            k: 5,
            tlast: 0,
            pre: (0..72).collect(),
            post: vec![9; 16],
        };
        let f = receipt_family(&rc, &dup, &[acct.clone()]);
        let ids: Vec<u64> = f.iter().map(|j| j.id).collect();
        assert_eq!(
            ids,
            vec![
                msg_id(K_RC, 0),
                msg_id(K_RC, 1),
                msg_id(K_PEO, 0),
                msg_id(K_LEAF, 0),
                msg_id(K_RID, 0),
                msg_id(K_PEO, 1),
                msg_id(K_LEAF, 1),
                msg_id(K_VPOST, 5),
                msg_id(K_MRK, 0),
            ]
        );
        assert!(f[0].dmult && !f[1].dmult, "duplicate RC gets no digest");
        assert_eq!(f[1].bytes, vec![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(f[4].bytes.len(), 48);
        assert_eq!(&f[4].bytes[32..34], &[2, 1]);
        assert_eq!(f[7].bytes.len(), 72);
        // the rcpt/acct sends are exactly the receipt bytes but the Merkle node's
        let rep = bus_check(&[rcpt_raw(&rc), acct_raw(&[acct])], &f);
        assert!(rep.bad_sends.is_empty(), "{rep:?}");
        assert_eq!(rep.unsent, 64);
    }

    fn job(id: u64, len: usize) -> Job {
        Job::new(id, vec![0; len])
    }

    #[test]
    fn two_bins_split_whole_jobs() {
        let mut f = Families::default();
        // native: 2 jobs of 1,048,577 rows-ish: use many 64-byte jobs (35 rows)
        f.native = (0..100).map(|i| job(msg_id(K_NPRE, i), 64)).collect();
        f.scheduler = vec![job(msg_id(K_SCH, 0), 64)];
        f.receipt = vec![job(msg_id(K_RC, 0), 12)];
        f.source = (0..10).map(|i| job(msg_id(K_SRC, i), 64)).collect();
        let (b0, b1, cap) = two_bins(&f);
        assert_eq!(cap, BIN_ROWS - 3500);
        assert_eq!(b0.len(), 110);
        assert_eq!(b1.len(), 2);
        // a tight capacity splits between whole jobs, keeping the order
        assert_eq!(split_jobs(70, &f.source), 2);
        assert_eq!(split_jobs(69, &f.source), 1);
        assert_eq!(split_jobs(0, &f.source), 0);
        let mut big = Families::default();
        big.native = vec![Job::new(msg_id(K_NPRE, 0), vec![0; 64 * 246_000])];
        big.source = f.source.clone();
        big.receipt = f.receipt.clone();
        let rows0 = big.native[0].rows();
        let (b0, b1, cap) = two_bins(&big);
        assert_eq!(cap, BIN_ROWS - rows0);
        let k = ((BIN_ROWS - rows0) / 35) as usize;
        assert_eq!(b0.len(), 1 + k.min(10));
        assert_eq!(b1.len(), 1 + 10 - k.min(10));
        assert_eq!(b1[0].id, msg_id(K_RC, 0));
    }

    #[test]
    fn scheduler_family_order() {
        let ups = vec![
            UpsLite {
                tau: 1,
                v: vec![1, 2],
                parts: vec![UpsPartLite { q: vec![3] }],
            },
            UpsLite {
                tau: 0,
                v: vec![4],
                parts: vec![UpsPartLite { q: vec![5] }, UpsPartLite { q: vec![6, 7] }],
            },
        ];
        let codec = vec![
            CodecLite {
                tau: None,
                present: false,
                prev_hash: vec![],
                ash: vec![8; 32],
            },
            CodecLite {
                tau: None,
                present: true,
                prev_hash: vec![9; 32],
                ash: vec![8; 32],
            },
        ];
        let f = scheduler_family(&ups, &codec);
        let ids: Vec<u64> = f.iter().map(|j| j.id).collect();
        assert_eq!(
            ids,
            vec![
                upsert_job_id(0, 0),
                upsert_job_id(0, 1),
                upsert_job_id(0, 2),
                upsert_job_id(1, 0),
                upsert_job_id(1, 1),
                msg_id(K_SCH, 0),
                msg_id(K_SCH, 1),
            ]
        );
        assert_eq!(f[5].bytes[..32], [0; 32]);
        assert_eq!(f[6].bytes[..32], [9; 32]);
        let rep = bus_check(&[ups_raw(&ups), codec_raw(&codec)], &f);
        // the 5 upsert digests are received by the ups compact relay
        // (`compactGeneratedDigests`), which `ups_raw` does not model
        assert!(
            rep.ok() && rep.unsent == 0 && rep.unreceived == 5,
            "{rep:?}"
        );
    }

    #[test]
    fn source_family_skips_duplicates() {
        let it = SrcpItem {
            q: 3,
            dir: true,
            sib: vec![1; 32],
            acc: vec![2; 32],
            pq: 2,
            pl: 32,
        };
        let b = SrcpB {
            j: 0,
            l: 12,
            dup: false,
            root: vec![0; 32],
            qe: 3,
            le: 64,
            ql: 2,
            leaf: vec![2; 32],
            path: vec![it],
            rep: false,
        };
        let d = SrcpB {
            j: 1,
            dup: true,
            ..b.clone()
        };
        let f = source_family(&[b.clone(), d]);
        assert_eq!(f.len(), 2);
        assert_eq!(f[1].bytes, [vec![2; 32], vec![1; 32]].concat());
        let rep = bus_check(&[srcp_raw(&[b])], &f);
        assert!(rep.bad_sends.is_empty() && rep.unsent == 0, "{rep:?}");
    }

    #[test]
    fn collect_from_entry_map() {
        let n = leaf_node(vec![1, 2], digest(b"he"));
        let mut m = HashMap::new();
        m.insert("node".to_string(), serde_json::to_string(&vec![n]).unwrap());
        m.insert(
            "sha_receipt".to_string(),
            r#"[{"id":1,"bytes":[1,2],"dmult":false}]"#.to_string(),
        );
        let b = bundle_from_entries(&m).unwrap();
        let c = collect(&b);
        assert_eq!(c.b0.len(), 2);
        assert_eq!(c.b1.len(), 1);
        assert!(!c.b1[0].dmult);
        let (t, r) = instances_from_entries(&m).unwrap();
        assert!(t.starts_with('[') && r.contains("\"dmult\":false"));
    }
}
