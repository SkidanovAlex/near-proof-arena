//! Honest native entries of the trie tables `nodeV3` (2), `valV3` (4), `headV3` (3) and
//! `uniqV3` (6): Rust twin of `Assembly/TrieNative.lean` (`nodes`, `vals`, `heads`) and
//! `Assembly/TrieUniqDup.lean` (`uniqNative`), on the native objects ([`Native`]).
//!
//! * `nodes m steps oldPost writes q = assignList q 0 (records (forestOldInputs
//!   (nativeReplayForest m steps oldPost writes)) (ChainMetadata.assign (chain m steps) 0
//!   (seedNodes m steps)))`;
//! * `vals m steps = ChainMetadata.assignValues (chain m steps) (seedVals m steps)`;
//! * `heads m steps oldPost writes keys = assignHeadUses keys (forestWalkHeads 0 0
//!   ((nativeReplayForest …).map (pre, post)))`;
//! * `uniqNative m steps = uniqBlocks (occsOf m steps)`.
//!
//! The Lean definitions use quadratic list operations (`find?`, `count`, `eraseDups`,
//! `getD`); here they are hash maps keyed the same way, keeping first-occurrence and
//! stable-sort semantics, so the outputs are identical.

use std::collections::HashMap;

use crate::near::reexec::sha256;
use crate::near::spec::{PTrie, Slot, u32b, u64b};

use super::native::Native;
use super::node::{Kid, NodeS3, NodeV3, Slot as NSlot3};
use super::{HeadE, UEnt, ValE};

/// `UseRequests` (`Rcpt/Candidates/NodeUsage.lean`): EDGE / BMAP / UPB-window request keys.
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Deserialize, serde::Serialize)]
pub struct UseRequests {
    pub edges: Vec<Vec<u64>>,
    pub bmaps: Vec<Vec<u64>>,
    pub windows: Vec<Vec<u64>>,
}

/// `Near/Ids.lean`: `K_NPRE`, `K_NPOST`, `K_VPRE`, `SYM_END`, `SYM_START`.
const K_NPRE: u64 = 7;
const K_NPOST: u64 = 8;
const K_VPRE: u64 = 9;
const SYM_END: u64 = 16;
const SYM_START: u64 = 18;
/// `NearV3/Ids.lean`: edge kinds.
const EK_DOWN: u64 = 0;
const EK_KEY: u64 = 1;
const EK_VAL: u64 = 2;
const EK_LEND: u64 = 3;

/// `msgId kind idx = kind + 16·idx` (`Near/Ids.lean`).
fn msg_id(kind: u64, idx: u64) -> u64 {
    kind + 16 * idx
}

/// `eidN n` (`Extract/NodeView.lean`).
fn eid_n(n: u64) -> u64 {
    msg_id(K_NPRE, n)
}

/// `eidV e` (`Extract/ValProof.lean`).
fn eid_v(e: &ValE) -> u64 {
    msg_id(K_VPRE, e.vid)
}

fn nats(b: &[u8]) -> Vec<u64> {
    b.iter().map(|&x| x as u64).collect()
}

/// `toBytes` (`UInt8.ofNat` per entry).
fn to_bytes(xs: &[u64]) -> Vec<u8> {
    xs.iter().map(|&x| x as u8).collect()
}

/// `(sha256 b).map UInt8.toNat` (`NodePostUpdate.digest`, `TrieUniqDup.dig`).
fn digest(b: &[u8]) -> Vec<u64> {
    nats(&sha256(b))
}

// ---------------------------------------------------------------------------
// Occurrences (`Spec/Occs.lean`, `Spec/TreeRecs.lean`, `Spec/Codec.lean`)
// ---------------------------------------------------------------------------

/// `isNode` (`Spec/Codec.lean`).
fn is_node(t: &PTrie) -> bool {
    !matches!(t, PTrie::Hash(_))
}

/// `occs t` (`Spec/Occs.lean`): revealed node subtrees, pre-order.
fn occs<'a>(t: &'a PTrie, out: &mut Vec<&'a PTrie>) {
    match t {
        PTrie::Hash(_) => {}
        PTrie::Leaf(..) => out.push(t),
        PTrie::Ext(_, c, _) => {
            out.push(t);
            occs(c, out);
        }
        PTrie::Branch(_, cs, _) => {
            out.push(t);
            for c in cs.iter().flatten() {
                occs(c, out);
            }
        }
    }
}

/// `tsize t = (occs t).length` (`Spec/TreeRecs.lean`).
fn tsize(t: &PTrie) -> u64 {
    match t {
        PTrie::Hash(_) => 0,
        PTrie::Leaf(..) => 1,
        PTrie::Ext(_, c, _) => 1 + tsize(c),
        PTrie::Branch(_, cs, _) => 1 + cs.iter().flatten().map(tsize).sum::<u64>(),
    }
}

/// `slotVal` (`Spec/Occs.lean`).
fn slot_val(s: &Slot) -> Option<&Vec<u8>> {
    match s {
        Slot::Val(v) => Some(v),
        Slot::Ref(..) => None,
    }
}

/// `ownVals` (`Spec/Occs.lean`).
fn own_vals(t: &PTrie) -> Option<&Vec<u8>> {
    match t {
        PTrie::Leaf(_, s, _) => slot_val(s),
        PTrie::Branch(Some(s), _, _) => slot_val(s),
        _ => None,
    }
}

/// `valsOf t = (occs t).flatMap ownVals` (`Spec/Occs.lean`).
fn vals_of(t: &PTrie) -> Vec<&Vec<u8>> {
    let mut os = vec![];
    occs(t, &mut os);
    os.into_iter().filter_map(own_vals).collect()
}

/// `nodeEnc` (`Spec/Codec.lean`) = `PTrie::node_ser`.
fn node_enc(t: &PTrie) -> Vec<u8> {
    t.node_ser()
}

// ---------------------------------------------------------------------------
// Seeded views (`Render/Ups/TreeViews.lean`, `Render/Ups/TreeViewSeeds.lean`)
// ---------------------------------------------------------------------------

/// `viewSlot vid` (`Render/Ups/TreeViews.lean`).
fn view_slot(vid: u64, s: &Slot) -> NSlot3 {
    match s {
        Slot::Val(v) => {
            let d = digest(v);
            NSlot3::Val {
                lenB: nats(&u32b(v.len() as u128)),
                vid,
                vlen: v.len() as u64,
                pre: d.clone(),
                post: d,
                written: false,
            }
        }
        Slot::Ref(len, h) => NSlot3::Ref {
            lenB: nats(&u32b(*len)),
            h: nats(h),
        },
    }
}

/// `viewTarget` (`Render/Ups/TreeViews.lean`): the node reached after skipping empty
/// revealed extensions.
fn view_target(n: u64, t: &PTrie) -> u64 {
    match t {
        PTrie::Ext(k, c, _) if k.is_empty() => {
            if is_node(c) {
                view_target(n + 1, c)
            } else {
                n
            }
        }
        _ => n,
    }
}

/// `viewKid nid child` (`Render/Ups/TreeViews.lean`).
fn view_kid(nid: u64, c: &PTrie) -> Kid {
    let h = nats(&c.hash_of());
    if is_node(c) {
        Kid::Node {
            cid: nid,
            clen: node_enc(c).len() as u64,
            cres: view_target(nid, c),
            pre: h.clone(),
            post: h,
        }
    } else {
        Kid::Hash { h }
    }
}

/// `viewKids` (`Render/Ups/TreeViews.lean`): one `NKid` per child slot.
fn view_kids(mut n: u64, cs: &[Option<PTrie>]) -> Vec<Kid> {
    cs.iter()
        .map(|c| match c {
            None => Kid::None,
            Some(c) => {
                let k = view_kid(n, c);
                n += tsize(c);
                k
            }
        })
        .collect()
}

/// `viewNode nid vid` (`Render/Ups/TreeViews.lean`).
fn view_node(nid: u64, vid: u64, t: &PTrie) -> NodeV3 {
    match t {
        PTrie::Hash(_) => NodeV3::Branch {
            v: None,
            kids: vec![],
            memB: nats(&u64b(0)),
        },
        PTrie::Leaf(k, s, m) => NodeV3::Leaf {
            key: k.iter().map(|&x| x as u64).collect(),
            v: view_slot(vid, s),
            memB: nats(&u64b(*m)),
        },
        PTrie::Ext(k, c, m) => NodeV3::Ext {
            key: k.iter().map(|&x| x as u64).collect(),
            kid: view_kid(nid + 1, c),
            memB: nats(&u64b(*m)),
        },
        PTrie::Branch(v, cs, m) => NodeV3::Branch {
            v: v.as_ref().map(|s| view_slot(vid, s)),
            kids: view_kids(nid + 1, cs),
            memB: nats(&u64b(*m)),
        },
    }
}

/// `seedNodeView tau depth nid vid t` (`Render/Ups/TreeViewSeeds.lean`).
fn seed_node_view(tau: u64, depth: u64, nid: u64, vid: u64, t: &PTrie) -> NodeS3 {
    NodeS3 {
        v: view_node(nid, vid, t),
        tau,
        depth,
        res: view_target(nid, t),
        uses: vec![],
        ubm: 0,
        dup: false,
        hd: false,
        rep_e: 0,
        ucid: vec![],
        m_u: vec![],
    }
}

/// `seedNodesT tau d n v t` / `seedKidsT` (`Render/Ups/TreeViewSeeds.lean`): pre-order, so
/// the node id `n` and value id `v` are running counters (`tsize`, `valsOf` offsets).
fn seed_nodes_t(tau: u64, d: u64, n: &mut u64, v: &mut u64, t: &PTrie, out: &mut Vec<NodeS3>) {
    match t {
        PTrie::Hash(_) => {}
        PTrie::Leaf(_, s, _) => {
            out.push(seed_node_view(tau, d, *n, *v, t));
            *n += 1;
            *v += slot_val(s).is_some() as u64;
        }
        PTrie::Ext(_, c, _) => {
            out.push(seed_node_view(tau, d, *n, *v, t));
            *n += 1;
            seed_nodes_t(tau, d + 1, n, v, c, out);
        }
        PTrie::Branch(sv, cs, _) => {
            out.push(seed_node_view(tau, d, *n, *v, t));
            *n += 1;
            *v += sv.as_ref().and_then(slot_val).is_some() as u64;
            for c in cs.iter().flatten() {
                seed_nodes_t(tau, d + 1, n, v, c, out);
            }
        }
    }
}

/// `forestNodes 0 0 0 ts` (`Assembly/ForestViews.lean`): one address space, `τ` = tree index.
fn forest_nodes(ts: &[&PTrie]) -> Vec<NodeS3> {
    let (mut n, mut v, mut out) = (0, 0, vec![]);
    for (tau, t) in ts.iter().enumerate() {
        seed_nodes_t(tau as u64, 0, &mut n, &mut v, t, &mut out);
    }
    out
}

/// `forestBytes ts = ts.flatMap valsOf` (`Assembly/ForestViews.lean`).
fn forest_bytes<'a>(ts: &[&'a PTrie]) -> Vec<&'a Vec<u8>> {
    ts.iter().flat_map(|t| vals_of(t)).collect()
}

/// `seedValue` / `seedValuesFrom vid` (`Render/Ups/TreeViewValues.lean`).
fn seed_values_from(vid: u64, bs: &[&Vec<u8>]) -> Vec<ValE> {
    bs.iter()
        .enumerate()
        .map(|(i, b)| ValE {
            vid: vid + i as u64,
            len: b.len() as u64,
            vz: b.is_empty(),
            dup: false,
            hd: false,
            rep_e: 0,
            bytes: nats(b),
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Local metadata (`Rcpt/Candidates/NodeWindowIds.lean`, `Extract/NodeView.lean`)
// ---------------------------------------------------------------------------

/// `keyEdges3 n k` (`Extract/NodeView.lean`).
fn key_edges3(n: u64, k: &[u64], out: &mut Vec<Vec<u64>>) {
    for (i, &x) in k.iter().enumerate() {
        out.push(vec![n, i as u64, x, n, i as u64 + 1, EK_KEY]);
    }
}

/// `edgesOf3 n s` (`Extract/NodeView.lean`): the edges record `n` provides.
fn edges_of3(n: u64, s: &NodeS3) -> Vec<Vec<u64>> {
    let mut o = vec![];
    match &s.v {
        NodeV3::Leaf { key, v, .. } => {
            key_edges3(n, key, &mut o);
            let kl = key.len() as u64;
            if let NSlot3::Val { vid, .. } = v {
                o.push(vec![n, kl, SYM_END, *vid, 0, EK_VAL]);
            }
            o.push(vec![n, kl, SYM_END, n, kl, EK_LEND]);
        }
        NodeV3::Ext { key, kid, .. } => {
            key_edges3(n, &key[..key.len().saturating_sub(1)], &mut o);
            if let Some(&x) = key.last() {
                let kl = key.len() as u64;
                match kid {
                    Kid::Node { cres, .. } => o.push(vec![n, kl - 1, x, *cres, 0, EK_KEY]),
                    _ => o.push(vec![n, kl - 1, x, n, kl, EK_KEY]),
                }
            }
        }
        NodeV3::Branch { v, kids, .. } => {
            for (j, k) in kids.iter().enumerate() {
                if let Kid::Node { cres, .. } = k {
                    o.push(vec![n, 0, j as u64, *cres, 0, EK_DOWN]);
                }
            }
            if let Some(NSlot3::Val { vid, .. }) = v {
                o.push(vec![n, 0, SYM_END, *vid, 0, EK_VAL]);
            }
        }
    }
    o
}

/// `kidBitmap` (`Near/Extract/NodeView.lean`).
fn kid_bitmap(kids: &[Kid]) -> u64 {
    kids.iter()
        .enumerate()
        .map(|(j, k)| if matches!(k, Kid::None) { 0 } else { 1u64 << j })
        .sum()
}

/// `NodeV3.bmap` (`Extract/NodeView.lean`): `(bm, hasValue)` of a branch.
fn bmap(v: &NodeV3) -> Option<(u64, u64)> {
    match v {
        NodeV3::Branch { v, kids, .. } => Some((kid_bitmap(kids), v.is_some() as u64)),
        _ => None,
    }
}

/// `kidIds` (`Rcpt/Candidates/NodeWindowIds.lean`).
fn kid_ids(k: &Kid, out: &mut Vec<u64>) {
    match k {
        Kid::None => {}
        Kid::Hash { .. } => out.extend([0; 32]),
        Kid::Node { cid, .. } => out.extend([*cid; 32]),
    }
}

/// `windowIds` (`Rcpt/Candidates/NodeWindowIds.lean`).
fn window_ids(v: &NodeV3) -> Vec<u64> {
    match v {
        NodeV3::Leaf { .. } => vec![0; v.ser_len()],
        NodeV3::Ext { key, kid, .. } => {
            // `(hpN k false).length = 1 + |k| / 2`.
            let mut o = vec![0; 5 + 1 + key.len() / 2];
            kid_ids(kid, &mut o);
            o.extend([0; 8]);
            o
        }
        NodeV3::Branch { v, kids, .. } => {
            let mut o = vec![0; if v.is_some() { 37 } else { 1 } + 2];
            for k in kids {
                kid_ids(k, &mut o);
            }
            o.extend([0; 8]);
            o
        }
    }
}

/// `initializeMetadata nid s` (`Rcpt/Candidates/NodeWindowIds.lean`).
fn initialize_metadata(nid: u64, mut s: NodeS3) -> NodeS3 {
    s.uses = vec![0; edges_of3(nid, &s).len()];
    s.ucid = window_ids(&s.v);
    s.m_u = vec![0; s.v.ser_len()];
    s
}

/// `initializeList 0` (`Rcpt/Candidates/NativeForestMetadata.lean`).
fn initialize_list(ss: Vec<NodeS3>) -> Vec<NodeS3> {
    ss.into_iter()
        .enumerate()
        .map(|(i, s)| initialize_metadata(i as u64, s))
        .collect()
}

// ---------------------------------------------------------------------------
// Store occurrences and duplicate chain (`Candidates/*`)
// ---------------------------------------------------------------------------

/// `HonestStoreRepresentatives.Key = Nat × Bytes`.
type Key = (u64, Vec<u8>);

/// `StoreDuplicateMetadata.Occurrence`.
#[derive(Clone, Debug)]
struct Occurrence {
    key: Key,
    eid: u64,
}

/// `StoreDuplicateChain.Entry`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Entry {
    eid: u64,
    dup: bool,
    hd: bool,
    rep_e: u64,
}

/// `StoreDuplicateMetadata.nodeKey s = (s.tau, toBytes (s.v.ser false))`.
fn node_key(s: &NodeS3) -> Key {
    (s.tau, to_bytes(&s.v.ser(false)))
}

/// `Link3.valTau (forestNodes 0 0 0 ts)` as a map: value id ↦ the `τ` of the first node
/// whose revealed value slot is that id (`NativeStoreProvenance.valueTau`; absent ↦ 0).
fn value_tau(ns: &[NodeS3]) -> HashMap<u64, u64> {
    let mut m = HashMap::new();
    for s in ns {
        if let Some(i) = s.v.value_id() {
            m.entry(i).or_insert(s.tau);
        }
    }
    m
}

/// `CombinedStoreOccurrences.allOccurrences vs tau es` (node occurrences, then values).
fn all_occurrences(vs: &[NodeS3], tau: &HashMap<u64, u64>, es: &[ValE]) -> Vec<Occurrence> {
    let nodes = vs.iter().enumerate().map(|(i, s)| Occurrence {
        key: node_key(s),
        eid: eid_n(i as u64),
    });
    let vals = es.iter().map(|e| Occurrence {
        key: (tau.get(&e.vid).copied().unwrap_or(0), to_bytes(&e.bytes)),
        eid: eid_v(e),
    });
    nodes.chain(vals).collect()
}

/// `StoreClassPartition.keys` (`representatives = eraseDups`, first-occurrence order) with
/// each key's `members` (occurrence order).
fn classes(rs: &[Occurrence]) -> Vec<(&Key, Vec<&Occurrence>)> {
    let mut idx: HashMap<&Key, usize> = HashMap::new();
    let mut out: Vec<(&Key, Vec<&Occurrence>)> = vec![];
    for r in rs {
        let i = *idx.entry(&r.key).or_insert_with(|| {
            out.push((&r.key, vec![]));
            out.len() - 1
        });
        out[i].1.push(r);
    }
    out
}

/// `StoreDuplicateChain.entries` (with `tailEntries`).
fn entries(ids: &[u64]) -> Vec<Entry> {
    ids.iter()
        .enumerate()
        .map(|(j, &e)| Entry {
            eid: e,
            dup: j > 0,
            hd: j + 1 < ids.len(),
            rep_e: if j > 0 { ids[j - 1] } else { 0 },
        })
        .collect()
}

/// `StoreClassPartition.chain rs`.
fn chain(rs: &[Occurrence]) -> Vec<Entry> {
    classes(rs)
        .into_iter()
        .flat_map(|(_, ms)| entries(&ms.iter().map(|r| r.eid).collect::<Vec<_>>()))
        .collect()
}

/// `ChainMetadata.metadata rs` as a lookup (first entry per `eid`; default
/// `⟨eid, false, false, 0⟩`).
struct Metadata(HashMap<u64, Entry>);

impl Metadata {
    fn new(rs: &[Entry]) -> Metadata {
        let mut m = HashMap::new();
        for r in rs {
            m.entry(r.eid).or_insert(*r);
        }
        Metadata(m)
    }
    fn get(&self, eid: u64) -> Entry {
        self.0.get(&eid).copied().unwrap_or(Entry {
            eid,
            dup: false,
            hd: false,
            rep_e: 0,
        })
    }
}

/// `ChainMetadata.assign rs 0` (`patch` per node, `eidN n`).
fn chain_assign(md: &Metadata, ss: Vec<NodeS3>) -> Vec<NodeS3> {
    ss.into_iter()
        .enumerate()
        .map(|(n, mut s)| {
            let m = md.get(eid_n(n as u64));
            (s.dup, s.hd, s.rep_e) = (m.dup, m.hd, m.rep_e);
            s
        })
        .collect()
}

/// `ChainMetadata.assignValues rs es` (`patchValue`, `eidV e`).
fn assign_values(md: &Metadata, es: Vec<ValE>) -> Vec<ValE> {
    es.into_iter()
        .map(|mut e| {
            let m = md.get(eid_v(&e));
            (e.dup, e.hd, e.rep_e) = (m.dup, m.hd, m.rep_e);
            e
        })
        .collect()
}

impl NodeV3 {
    /// The value id of `NodeV3.value` (`Extract/NodeView.lean`).
    fn value_id(&self) -> Option<u64> {
        match self {
            NodeV3::Leaf {
                v: NSlot3::Val { vid, .. },
                ..
            }
            | NodeV3::Branch {
                v: Some(NSlot3::Val { vid, .. }),
                ..
            } => Some(*vid),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// The forest (`Assembly/TrieNative.lean`)
// ---------------------------------------------------------------------------

/// `TrieNative.forest m steps = m.pre :: steps.map pre`.
fn forest(n: &Native) -> Vec<&PTrie> {
    std::iter::once(&n.pre)
        .chain(n.steps.iter().map(|s| &s.pre))
        .collect()
}

/// `NodePostUpdate.ReplayTree` (`Rcpt/Candidates/NativeForestInputs.lean`).
struct ReplayTree<'a> {
    pre: &'a PTrie,
    post: &'a PTrie,
    writes: &'a [(Vec<u8>, Vec<u8>)],
}

/// `nativeReplayForest m steps oldPost writes = ⟨m.pre, oldPost, writes⟩ ::
/// steps.map ⟨s.pre, s.pre, []⟩` (`Rcpt/Candidates/NativeExecutionPayloads.lean`).
fn native_replay_forest(n: &Native) -> Vec<ReplayTree<'_>> {
    std::iter::once(ReplayTree {
        pre: &n.pre,
        post: &n.old_post,
        writes: &n.writes,
    })
    .chain(n.steps.iter().map(|s| ReplayTree {
        pre: &s.pre,
        post: &s.pre,
        writes: &[],
    }))
    .collect()
}

/// The shared pre-forest bookkeeping: `seedNodes`, `seedVals`, and the occurrences
/// `CombinedStoreOccurrences.allOccurrences seedNodes (valueTau forest) seedVals`.
struct Seeds {
    nodes: Vec<NodeS3>,
    vals: Vec<ValE>,
    occs: Vec<Occurrence>,
}

/// `TrieNative.seedNodes`, `seedVals` and `TrieUniqDup.occsOf`.
fn seeds(n: &Native) -> Seeds {
    let ts = forest(n);
    let raw = forest_nodes(&ts);
    let tau = value_tau(&raw);
    let nodes = initialize_list(raw);
    let vals = seed_values_from(0, &forest_bytes(&ts));
    let occs = all_occurrences(&nodes, &tau, &vals);
    Seeds { nodes, vals, occs }
}

// ---------------------------------------------------------------------------
// Old-record inputs (`Rcpt/Candidates/NativeForestInputs.lean`, `NodePostUpdate.lean`)
// ---------------------------------------------------------------------------

/// `valueIndex t key` / `kidValueIndex` (`Assembly/ValueIndex.lean`): ordinal of the
/// value at `key` in `valsOf t`.
fn value_index(t: &PTrie, key: &[u8]) -> Option<u64> {
    match t {
        PTrie::Hash(_) => None,
        PTrie::Leaf(k, s, _) => {
            if k.as_slice() == key {
                slot_val(s).map(|_| 0)
            } else {
                None
            }
        }
        PTrie::Ext(k, c, _) => {
            if key.starts_with(k) {
                value_index(c, &key[k.len()..])
            } else {
                None
            }
        }
        PTrie::Branch(v, cs, _) => {
            let own = v.as_ref().and_then(slot_val).is_some() as u64;
            match key.split_first() {
                None => v.as_ref().and_then(slot_val).map(|_| 0),
                Some((&j, rest)) => {
                    let j = j as usize;
                    let c = cs.get(j)?.as_ref()?;
                    let off: u64 = cs[..j]
                        .iter()
                        .flatten()
                        .map(|c| vals_of(c).len() as u64)
                        .sum();
                    value_index(c, rest).map(|i| own + off + i)
                }
            }
        }
    }
}

/// `forestOldInputs rs` (`Rcpt/Candidates/NativeForestInputs.lean`): `child` = `nodeEnc`
/// of the global post-forest occurrences, `value` = `forestPostValue rs` (through
/// `oldTreeInputs` / `writtenValueIds`, `Rcpt/Candidates/NativeOldPostInputs.lean`).
struct Inputs {
    child: Vec<Vec<u8>>,
    value: HashMap<u64, Vec<u8>>,
}

fn forest_old_inputs(rs: &[ReplayTree]) -> Inputs {
    let mut posts = vec![];
    for r in rs {
        occs(r.post, &mut posts);
    }
    let child = posts.into_iter().map(node_enc).collect();
    let mut value = HashMap::new();
    let mut base = 0u64;
    for r in rs {
        let npre = vals_of(r.pre).len() as u64;
        let post_vals = vals_of(r.post);
        for w in r.writes {
            if let Some(i) = value_index(r.pre, &w.0) {
                // `i < |valsOf r.pre|` always (it is an ordinal of `valsOf r.pre`).
                if i < npre
                    && let Some(b) = post_vals.get(i as usize)
                {
                    value.entry(base + i).or_insert_with(|| (*b).clone());
                }
            }
        }
        base += npre;
    }
    Inputs { child, value }
}

/// `NodePostUpdate.kid u`.
fn upd_kid(u: &Inputs, k: Kid) -> Kid {
    match k {
        Kid::Node {
            cid,
            clen,
            cres,
            pre,
            ..
        } => {
            let c: &[u8] = u.child.get(cid as usize).map_or(&[], |v| v);
            Kid::Node {
                cid,
                clen,
                cres,
                pre,
                post: digest(c),
            }
        }
        k => k,
    }
}

/// `NodePostUpdate.slot u`.
fn upd_slot(u: &Inputs, s: NSlot3) -> NSlot3 {
    match s {
        NSlot3::Val {
            lenB,
            vid,
            vlen,
            pre,
            post,
            written,
        } => match u.value.get(&vid) {
            None => NSlot3::Val {
                lenB,
                vid,
                vlen,
                pre,
                post,
                written,
            },
            Some(b) => NSlot3::Val {
                lenB,
                vid,
                vlen,
                pre,
                post: digest(b),
                written: true,
            },
        },
        s => s,
    }
}

/// `NodePostUpdate.records u ss` (`record` / `node`).
fn records(u: &Inputs, ss: Vec<NodeS3>) -> Vec<NodeS3> {
    ss.into_iter()
        .map(|mut s| {
            s.v = match s.v {
                NodeV3::Leaf { key, v, memB } => NodeV3::Leaf {
                    key,
                    v: upd_slot(u, v),
                    memB,
                },
                NodeV3::Ext { key, kid, memB } => NodeV3::Ext {
                    key,
                    kid: upd_kid(u, kid),
                    memB,
                },
                NodeV3::Branch { v, kids, memB } => NodeV3::Branch {
                    v: v.map(|s| upd_slot(u, s)),
                    kids: kids.into_iter().map(|k| upd_kid(u, k)).collect(),
                    memB,
                },
            };
            s
        })
        .collect()
}

/// Multiset of messages (`List.count`).
fn counts(xs: &[Vec<u64>]) -> HashMap<&[u64], u64> {
    let mut m = HashMap::new();
    for x in xs {
        *m.entry(x.as_slice()).or_insert(0) += 1;
    }
    m
}

/// `assignList q 0` / `assignUses q n s` (`Rcpt/Candidates/NodeUsageList.lean`,
/// `NodeUsage.lean`; `windowKey n p s`).
fn assign_list(q: &UseRequests, ss: Vec<NodeS3>) -> Vec<NodeS3> {
    let (ce, cb, cw) = (counts(&q.edges), counts(&q.bmaps), counts(&q.windows));
    let c = |m: &HashMap<&[u64], u64>, k: &[u64]| m.get(k).copied().unwrap_or(0);
    ss.into_iter()
        .enumerate()
        .map(|(n, mut s)| {
            let n = n as u64;
            s.uses = edges_of3(n, &s).iter().map(|e| c(&ce, e)).collect();
            s.ubm = match bmap(&s.v) {
                None => 0,
                Some((bm, hv)) => c(&cb, &[n, bm, hv]),
            };
            let (pre, post) = (s.v.ser(false), s.v.ser(true));
            s.m_u = (0..pre.len())
                .map(|p| {
                    let key = [
                        msg_id(K_NPOST, n),
                        p as u64,
                        post.get(p).copied().unwrap_or(0),
                        pre.len() as u64,
                        s.depth,
                        s.ucid.get(p).copied().unwrap_or(0),
                    ];
                    c(&cw, &key)
                })
                .collect();
            s
        })
        .collect()
}

// ---------------------------------------------------------------------------
// The four tables
// ---------------------------------------------------------------------------

/// `TrieNative.nodes m steps oldPost writes q`.
pub fn nodes(n: &Native, q: &UseRequests) -> Result<Vec<NodeS3>, String> {
    let Seeds {
        nodes: seeded,
        occs,
        ..
    } = seeds(n);
    let md = Metadata::new(&chain(&occs));
    let u = forest_old_inputs(&native_replay_forest(n));
    Ok(assign_list(q, records(&u, chain_assign(&md, seeded))))
}

/// `TrieNative.vals m steps`.
pub fn vals(n: &Native) -> Result<Vec<ValE>, String> {
    let Seeds { vals, occs, .. } = seeds(n);
    let md = Metadata::new(&chain(&occs));
    Ok(assign_values(&md, vals))
}

/// `TrieNative.heads m steps oldPost writes keys = assignHeadUses keys (forestWalkHeads 0 0
/// pairs)` (`Rcpt/Candidates/HeadNodeBalance.lean`, `Render/Ups/ForestWalkHeads.lean`;
/// `mE = keys.count (headEdgeKey h)`, `headEdgeKey h = [0, τ, SYM_START, rres, 0, EK_DOWN]`).
pub fn heads(n: &Native, keys: &[Vec<u64>]) -> Result<Vec<HeadE>, String> {
    let ck = counts(keys);
    let mut rid = 0u64;
    Ok(native_replay_forest(n)
        .iter()
        .enumerate()
        .map(|(tau, r)| {
            let tau = tau as u64;
            let rres = view_target(rid, r.pre);
            let h = HeadE {
                tau,
                rid,
                rlen: node_enc(r.pre).len() as u64,
                rres,
                m_e: ck
                    .get([0, tau, SYM_START, rres, 0, EK_DOWN].as_slice())
                    .copied()
                    .unwrap_or(0),
                pre: nats(&r.pre.hash_of()),
                post: nats(&r.post.hash_of()),
            };
            rid += tsize(r.pre);
            h
        })
        .collect())
}

/// `TrieUniqDup.uniqNative m steps = uniqBlocks (occsOf m steps)`: the classes
/// (`keys`) stably sorted by `kle` = `(τ, le256 (dig bytes))`, each followed by its
/// members as `occEnt` (`⟨eid, τ, dig bytes⟩`).
pub fn uniq(n: &Native) -> Result<Vec<UEnt>, String> {
    let Seeds { occs, .. } = seeds(n);
    let mut cls: Vec<(u64, Vec<u64>, Vec<&Occurrence>)> = classes(&occs)
        .into_iter()
        .map(|(k, ms)| (k.0, digest(&k.1), ms))
        .collect();
    // `le256` is little-endian: compare from the last byte (all entries are `< 256`).
    cls.sort_by(|a, b| {
        a.0.cmp(&b.0)
            .then_with(|| a.1.iter().rev().cmp(b.1.iter().rev()))
    });
    Ok(cls
        .into_iter()
        .flat_map(|(tau, d, ms)| {
            ms.into_iter().map(move |r| UEnt {
                eid: r.eid,
                tau,
                bytes: d.clone(),
            })
        })
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf(k: &[u8], v: &[u8]) -> PTrie {
        PTrie::Leaf(k.to_vec(), Slot::Val(v.to_vec()), 7)
    }

    #[test]
    fn chain_entries_link_successors() {
        assert_eq!(
            entries(&[5, 9, 12]),
            vec![
                Entry {
                    eid: 5,
                    dup: false,
                    hd: true,
                    rep_e: 0
                },
                Entry {
                    eid: 9,
                    dup: true,
                    hd: true,
                    rep_e: 5
                },
                Entry {
                    eid: 12,
                    dup: true,
                    hd: false,
                    rep_e: 9
                },
            ]
        );
        assert_eq!(
            entries(&[3]),
            vec![Entry {
                eid: 3,
                dup: false,
                hd: false,
                rep_e: 0
            }]
        );
    }

    #[test]
    fn value_index_counts_preorder_values() {
        let mut cs = vec![None; 16];
        cs[1] = Some(leaf(&[2], b"a"));
        cs[4] = Some(leaf(&[3], b"b"));
        let t = PTrie::Branch(Some(Slot::Val(b"r".to_vec())), cs, 1);
        assert_eq!(value_index(&t, &[]), Some(0));
        assert_eq!(value_index(&t, &[1, 2]), Some(1));
        assert_eq!(value_index(&t, &[4, 3]), Some(2));
        assert_eq!(value_index(&t, &[4, 2]), None);
        assert_eq!(value_index(&t, &[5]), None);
        assert_eq!(vals_of(&t).len(), 3);
    }

    #[test]
    fn seeds_number_preorder_and_skip_empty_ext() {
        let inner = leaf(&[1], b"x");
        let e = PTrie::Ext(vec![], Box::new(inner), 2);
        assert_eq!(view_target(4, &e), 5);
        let mut cs = vec![None; 16];
        cs[0] = Some(e);
        cs[3] = Some(leaf(&[], b""));
        let t = PTrie::Branch(None, cs, 3);
        let ns = forest_nodes(&[&t, &leaf(&[], b"y")]);
        assert_eq!(ns.len(), 5);
        assert_eq!(
            ns.iter().map(|s| s.depth).collect::<Vec<_>>(),
            [0, 1, 2, 1, 0]
        );
        assert_eq!(
            ns.iter().map(|s| s.tau).collect::<Vec<_>>(),
            [0, 0, 0, 0, 1]
        );
        assert_eq!(ns[1].res, 2);
        assert_eq!(
            ns.iter().filter_map(|s| s.v.value_id()).collect::<Vec<_>>(),
            [0, 1, 2]
        );
        match &ns[0].v {
            NodeV3::Branch { kids, .. } => match (&kids[0], &kids[3]) {
                (
                    Kid::Node {
                        cid: 1, cres: 2, ..
                    },
                    Kid::Node {
                        cid: 3, cres: 3, ..
                    },
                ) => {}
                k => panic!("{k:?}"),
            },
            v => panic!("{v:?}"),
        }
        // Every window-id list matches the pre serialization.
        for s in initialize_list(ns) {
            assert_eq!(s.ucid.len(), s.v.ser_len());
        }
    }
}
