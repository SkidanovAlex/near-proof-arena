//! The native lookup walks of an accepted witness (`walkV3`, table 5): Rust twin of
//! `TrieEntriesV3.lean`'s `mainValuesOf` and of `allLookupQueries`
//! (`Rcpt/Candidates/NativeLookupQueryBounds.lean`), `nativeQueryWalks`
//! (`NativeLookupQueryList.lean`), `NativeQueueIds.resolve` (`Candidates/NativeQueueIds.lean`)
//! and `rankWalks` (`Rcpt/Candidates/WalkRanks.lean`).
//!
//! Lean ↔ Rust map:
//!
//! | Lean | Rust |
//! |---|---|
//! | `mainValuesOf` (`TrieEntriesV3.lean`) | [`main_values`] |
//! | `allLookupQueries` | [`queries`] |
//! | `accountLookupQueries` (`NativeAccountQueries.lean`) | [`account_lookup_queries`] |
//! | `accessKeyLookupQueries` (`NativeAccessKeyQueries.lean`) | [`access_key_lookup_queries`] |
//! | `queueLookupQueries` / `queueLookupQuery` (`NativeQueueLookup.lean`) | [`queue_lookup_queries`] |
//! | `plan` / `mainPlan` / `implicitPlan` / `Walk.request` (`Qv/Candidates/CombinedWalkGen.lean`) | [`queue_lookup_queries`] |
//! | `walkId` (`Qv/ReadPlan.lean`) | [`walk_id`] |
//! | `nativeQueryWalks` / `nativeQueryWalk` | [`query_walks`] / [`native_query_walk`] |
//! | `forestLookupNid` / `forestLookupVid` (`NativeForestLookup.lean`) | prefix sums in [`query_walks`] |
//! | `tsize` / `occs` (`Spec/Occs.lean`, `Spec/TreeRecs.lean`) | [`tsize`] |
//! | `valsOf` / `ownVals` / `optSlotVal` / `slotVal` | [`vals_len`], [`opt_slot_val_len`] |
//! | `isNode` (`Spec/Codec.lean`) | [`is_node`] |
//! | `viewTarget` (`Render/Ups/TreeViews.lean`) | [`view_target`] |
//! | `nativeLookupWalk` (`NativeLookupWalk.lean`) | [`native_lookup_walk`] |
//! | `nativeLookupSteps` / `nativeKidsLookupSteps` (`NativeLookupTree.lean`) | [`native_lookup_steps`] / [`native_kids_lookup_steps`] |
//! | `lookupExtensionEdges` / `lookupBranchAbsent` | [`lookup_extension_edges`] / [`lookup_branch_absent`] |
//! | `lookupDrain` / `lookupEdge` / `leafLookupSteps` (`NativeLookupLeaf.lean`) | [`lookup_drain`] / [`lookup_edge`] / [`leaf_lookup_steps`] |
//! | `extensionMismatchFix` / `extensionMismatchStep` (`NativeLookupExtensionFix.lean`) | [`extension_mismatch_fix`] / [`extension_mismatch_step`] |
//! | `rankWalks` / `rankWalk` / `rankWalkStep` (`WalkRanks.lean`, `WalkRequestInventory.lean`) | [`rank_walks`] |
//!
//! `NativeQueueIds.resolve` only feeds the `vid`/`users` fields of the queue plan's
//! `Walk`s, which `queueLookupQuery` drops (`NativeQueueIds.queries_independent`), so the
//! queries are computed without it.

use std::collections::HashMap;

use super::native::{MainValues, Native};
use super::{WStep3, WalkR};
use crate::near::spec::{
    PTrie, Receipt, SYSTEM, Slot, account_key_path, is_prefix, kids_bitmap, nibbles, u64b,
};
use crate::v3::hint::{find, key_access_key, key_buffered_idx, key_delayed_idx, key_yield_idx};

/// `NativeLookupQuery`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Query {
    pub wid: u64,
    pub tau: u64,
    pub key: Vec<u8>,
}

/// `SYM_END`, `SYM_START` (`Near/Ids.lean`).
const SYM_END: u64 = 16;
const SYM_START: u64 = 18;
/// `EK_DOWN`, `EK_KEY`, `EK_VAL`, `EK_LEND` (`NearV3/Ids.lean`).
const EK_DOWN: u64 = 0;
const EK_KEY: u64 = 1;
const EK_VAL: u64 = 2;
const EK_LEND: u64 = 3;
/// `W_AK`, `W_QV` (`Rcpt/Ids.lean`).
const W_AK: u64 = 8192;
const W_QV: u64 = 16384;

// ------------------------------------------------------------------ main values

/// The unique `MainValues` read from the main pre trie (`mainValuesOf`):
/// `⟨pre.find keyDelayedIdx, pre.find keyBufferedIdx, m.bufferedShards, pre.find keyYieldIdx⟩`,
/// each `find` must be determined (`some _`).
pub fn main_values(n: &Native) -> Result<MainValues, String> {
    let rd = |key: Vec<u8>, what: &str| {
        find(&n.pre, &key).ok_or_else(|| format!("main values: {what} unread"))
    };
    let delayed = rd(key_delayed_idx(), "delayed")?;
    let buffered = rd(key_buffered_idx(), "buffered")?;
    let yielded = rd(key_yield_idx(), "yield")?;
    Ok(MainValues {
        delayed,
        buffered,
        shards: n.buffered_shards.clone(),
        yielded,
    })
}

// ---------------------------------------------------------------------- queries

/// `allLookupQueries (appliedReceipts k w) m.pre v (steps.map pre) (resolve …)`
/// `= accountLookupQueries rs ++ accessKeyLookupQueries rs ++ queueLookupQueries pre v pres _`.
pub fn queries(n: &Native, v: &MainValues) -> Result<Vec<Query>, String> {
    let mut qs = account_lookup_queries(&n.receipts);
    qs.extend(access_key_lookup_queries(&n.receipts));
    qs.extend(queue_lookup_queries(v, n.steps.len()));
    qs.extend(n.extra_queries.iter().cloned());
    Ok(qs)
}

/// `accountLookupQueries rs`: `⟨i, 0, accountKeyPath r.receiverId⟩` per receipt `(r, i)`.
fn account_lookup_queries(rs: &[Receipt]) -> Vec<Query> {
    rs.iter()
        .enumerate()
        .map(|(i, r)| Query {
            wid: i as u64,
            tau: 0,
            key: account_key_path(&r.receiver_id),
        })
        .collect()
}

/// `accessKeyLookupQueries rs`: `⟨W_AK + i, 0, keyAccessKey r.receiverId r.signerPk⟩` for
/// the receipts with `predecessorId = system ∧ signerId = receiverId`.
fn access_key_lookup_queries(rs: &[Receipt]) -> Vec<Query> {
    rs.iter()
        .enumerate()
        .filter(|(_, r)| r.predecessor_id == SYSTEM && r.signer_id == r.receiver_id)
        .map(|(i, r)| Query {
            wid: W_AK + i as u64,
            tau: 0,
            key: key_access_key(&r.receiver_id, &r.signer_pk),
        })
        .collect()
}

/// `walkId tau slot = W_QV + tau + 64·slot`.
fn walk_id(tau: u64, slot: u64) -> u64 {
    W_QV + tau + 64 * slot
}

/// `queueLookupQueries pre v pres _ = (plan pre v pres _).map (queueLookupQuery v.shards)`,
/// `queueLookupQuery w = ⟨walkId w.tau w.slot, w.tau, (w.request _).key⟩`,
/// `(w.request _).key = nibbles w.kind.bytes`.  `mainPlan`: `delayed` (slot 0), `buffered`
/// (1), `yielded` (2), then `group s` (slot `3 + i`) per shard, all at `tau = 0`;
/// `implicitPlan`: `delayed` at `tau = i + 1`, slot 0, per implicit prestate (`npres`).
fn queue_lookup_queries(v: &MainValues, npres: usize) -> Vec<Query> {
    let q = |tau: u64, slot: u64, bytes: Vec<u8>| Query {
        wid: walk_id(tau, slot),
        tau,
        key: nibbles(&bytes),
    };
    // `Kind.bytes`: delayed `[7]`, buffered `[13]`, yielded `[10]`, group s `[16] ++ u64 s`.
    let mut qs = vec![q(0, 0, vec![7]), q(0, 1, vec![13]), q(0, 2, vec![10])];
    for (i, &s) in v.shards.iter().enumerate() {
        let mut b = vec![16u8];
        b.extend(u64b(s as u128));
        qs.push(q(0, 3 + i as u64, b));
    }
    for i in 0..npres as u64 {
        qs.push(q(i + 1, 0, vec![7]));
    }
    qs
}

// ------------------------------------------------------------------ trie sizes

/// `tsize t = (occs t).length`: revealed (non-hash) nodes of `t`.
fn tsize(t: &PTrie) -> u64 {
    match t {
        PTrie::Hash(_) => 0,
        PTrie::Leaf(..) => 1,
        PTrie::Ext(_, c, _) => 1 + tsize(c),
        PTrie::Branch(_, cs, _) => 1 + cs.iter().flatten().map(tsize).sum::<u64>(),
    }
}

/// `(slotVal s).length`.
fn slot_val_len(s: &Slot) -> u64 {
    matches!(s, Slot::Val(_)) as u64
}

/// `(optSlotVal v).length`.
fn opt_slot_val_len(v: &Option<Slot>) -> u64 {
    v.as_ref().map_or(0, slot_val_len)
}

/// `(valsOf t).length = ((occs t).flatMap ownVals).length`.
fn vals_len(t: &PTrie) -> u64 {
    match t {
        PTrie::Hash(_) => 0,
        PTrie::Leaf(_, s, _) => slot_val_len(s),
        PTrie::Ext(_, c, _) => vals_len(c),
        PTrie::Branch(v, cs, _) => {
            opt_slot_val_len(v) + cs.iter().flatten().map(vals_len).sum::<u64>()
        }
    }
}

/// `isNode`: every constructor but `.hash`.
fn is_node(t: &PTrie) -> bool {
    !matches!(t, PTrie::Hash(_))
}

/// `viewTarget`: the node reached after skipping empty revealed extensions.
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

// --------------------------------------------------------------- lookup steps

/// `lookupEdge mode sym e = ⟨mode, sym, e, 0, 0, 0, 0⟩`.
fn lookup_edge(mode: u64, sym: u64, e: Vec<u64>) -> WStep3 {
    WStep3 {
        mode,
        sym,
        e,
        u: 0,
        bm: 0,
        hv: 0,
        ub: 0,
    }
}

/// `lookupDrain key = (key ++ [SYM_END]).map (⟨3, ·, [0,0,0,0,0,0], 0, 0, 0, 0⟩)`.
fn lookup_drain(key: &[u8]) -> Vec<WStep3> {
    key.iter()
        .map(|&x| x as u64)
        .chain([SYM_END])
        .map(|sym| lookup_edge(3, sym, vec![0; 6]))
        .collect()
}

/// `leafLookupSteps nid vid slot pos stored key`.
fn leaf_lookup_steps(
    nid: u64,
    vid: u64,
    slot: &Slot,
    pos: u64,
    stored: &[u8],
    key: &[u8],
) -> Option<Vec<WStep3>> {
    match (stored.split_first(), key.split_first()) {
        (None, None) => match slot {
            Slot::Val(_) => Some(vec![lookup_edge(
                0,
                SYM_END,
                vec![nid, pos, SYM_END, vid, 0, EK_VAL],
            )]),
            Slot::Ref(..) => None,
        },
        (Some((&a, _)), None) => Some(vec![lookup_edge(
            1,
            SYM_END,
            vec![nid, pos, a as u64, nid, pos + 1, EK_KEY],
        )]),
        (None, Some((&x, xs))) => {
            let mut v = vec![lookup_edge(
                1,
                x as u64,
                vec![nid, pos, SYM_END, nid, pos, EK_LEND],
            )];
            v.extend(lookup_drain(xs));
            Some(v)
        }
        (Some((&a, r#as)), Some((&x, xs))) => {
            let edge = |mode| {
                lookup_edge(
                    mode,
                    x as u64,
                    vec![nid, pos, a as u64, nid, pos + 1, EK_KEY],
                )
            };
            if a == x {
                leaf_lookup_steps(nid, vid, slot, pos + 1, r#as, xs).map(|ss| {
                    let mut v = vec![edge(0)];
                    v.extend(ss);
                    v
                })
            } else {
                let mut v = vec![edge(1)];
                v.extend(lookup_drain(xs));
                Some(v)
            }
        }
    }
}

/// `lookupExtensionEdges nid target key`: one `EK_KEY` edge per extension nibble; the
/// last one targets the resolved child.
fn lookup_extension_edges(nid: u64, target: u64, key: &[u8]) -> Vec<WStep3> {
    let n = key.len();
    (0..n)
        .map(|i| {
            let last = i + 1 == n;
            let k = key[i] as u64;
            lookup_edge(
                0,
                k,
                vec![
                    nid,
                    i as u64,
                    k,
                    if last { target } else { nid },
                    if last { 0 } else { i as u64 + 1 },
                    EK_KEY,
                ],
            )
        })
        .collect()
}

/// `lookupBranchAbsent nid bm hv sym rest`.
fn lookup_branch_absent(nid: u64, bm: u64, hv: u64, sym: u64, rest: &[u8]) -> Vec<WStep3> {
    let mut v = vec![WStep3 {
        mode: 2,
        sym,
        e: vec![nid, 0, 0, 0, 0, 0],
        u: 0,
        bm,
        hv,
        ub: 0,
    }];
    v.extend(lookup_drain(rest));
    v
}

/// `List.getD i 0`.
fn at(e: &[u64], i: usize) -> u64 {
    e.get(i).copied().unwrap_or(0)
}

/// `extensionMismatchStep target len s`.
fn extension_mismatch_step(target: u64, len: u64, s: WStep3) -> WStep3 {
    if s.mode == 1 && at(&s.e, 1) + 1 == len && at(&s.e, 5) == EK_KEY {
        let e = vec![
            at(&s.e, 0),
            at(&s.e, 1),
            at(&s.e, 2),
            target,
            0,
            at(&s.e, 5),
        ];
        WStep3 { e, ..s }
    } else {
        s
    }
}

/// `extensionMismatchFix nid child len ss`.
fn extension_mismatch_fix(nid: u64, child: &PTrie, len: u64, ss: Vec<WStep3>) -> Vec<WStep3> {
    if is_node(child) {
        let target = view_target(nid + 1, child);
        ss.into_iter()
            .map(|s| extension_mismatch_step(target, len, s))
            .collect()
    } else {
        ss
    }
}

/// `nativeLookupSteps nid vid tree key`.
fn native_lookup_steps(nid: u64, vid: u64, t: &PTrie, key: &[u8]) -> Option<Vec<WStep3>> {
    match t {
        PTrie::Hash(_) => None,
        PTrie::Leaf(stored, slot, _) => leaf_lookup_steps(nid, vid, slot, 0, stored, key),
        PTrie::Ext(stored, child, _) => {
            if is_prefix(stored, key) {
                native_lookup_steps(nid + 1, vid, child, &key[stored.len()..]).map(|ss| {
                    let mut v = lookup_extension_edges(nid, view_target(nid + 1, child), stored);
                    v.extend(ss);
                    v
                })
            } else {
                leaf_lookup_steps(nid, vid, &Slot::Ref(0, vec![]), 0, stored, key)
                    .map(|ss| extension_mismatch_fix(nid, child, stored.len() as u64, ss))
            }
        }
        PTrie::Branch(value, kids, _) => {
            let bm = kids_bitmap(kids) as u64;
            match key.split_first() {
                None => match value {
                    None => Some(vec![WStep3 {
                        mode: 2,
                        sym: SYM_END,
                        e: vec![nid, 0, 0, 0, 0, 0],
                        u: 0,
                        bm,
                        hv: 0,
                        ub: 0,
                    }]),
                    Some(Slot::Ref(..)) => None,
                    Some(Slot::Val(_)) => Some(vec![lookup_edge(
                        0,
                        SYM_END,
                        vec![nid, 0, SYM_END, vid, 0, EK_VAL],
                    )]),
                },
                Some((&x, xs)) => native_kids_lookup_steps(
                    nid,
                    bm,
                    value.is_some() as u64,
                    x as u64,
                    nid + 1,
                    vid + opt_slot_val_len(value),
                    kids,
                    x as usize,
                    xs,
                ),
            }
        }
    }
}

/// `nativeKidsLookupSteps parent bm hv sym nid vid kids j key`: the cursor IDs advance over
/// every revealed occurrence/value of the kids before position `j` (Lean's `Kids` linked
/// list ↔ the positional `Vec<Option<PTrie>>`; past its end is `.nil`).
#[allow(clippy::too_many_arguments)]
fn native_kids_lookup_steps(
    parent: u64,
    bm: u64,
    hv: u64,
    sym: u64,
    mut nid: u64,
    mut vid: u64,
    kids: &[Option<PTrie>],
    j: usize,
    key: &[u8],
) -> Option<Vec<WStep3>> {
    if j >= kids.len() {
        return Some(lookup_branch_absent(parent, bm, hv, sym, key));
    }
    for c in kids[..j].iter().flatten() {
        nid += tsize(c);
        vid += vals_len(c);
    }
    match &kids[j] {
        None => Some(lookup_branch_absent(parent, bm, hv, sym, key)),
        Some(child) => native_lookup_steps(nid, vid, child, key).map(|ss| {
            let mut v = vec![lookup_edge(
                0,
                sym,
                vec![parent, 0, sym, view_target(nid, child), 0, EK_DOWN],
            )];
            v.extend(ss);
            v
        }),
    }
}

/// `nativeLookupWalk wid tau nid tree steps`: the `START` edge, then `steps`.
fn native_lookup_walk(wid: u64, tau: u64, nid: u64, tree: &PTrie, steps: Vec<WStep3>) -> WalkR {
    let mut s = vec![lookup_edge(
        0,
        SYM_START,
        vec![0, tau, SYM_START, view_target(nid, tree), 0, EK_DOWN],
    )];
    s.extend(steps);
    WalkR {
        w: wid,
        tau,
        steps: s,
    }
}

/// `nativeQueryWalk pairs q`, given the transition prestates `trees = pairs.map Prod.fst`
/// and the prefix sums `nids[τ] = forestLookupNid (trees.take τ)`,
/// `vids[τ] = forestLookupVid (trees.take τ)`.
fn native_query_walk(trees: &[&PTrie], nids: &[u64], vids: &[u64], q: &Query) -> Option<WalkR> {
    let tau = usize::try_from(q.tau).ok()?;
    let tree = *trees.get(tau)?;
    let steps = native_lookup_steps(nids[tau], vids[tau], tree, &q.key)?;
    Some(native_lookup_walk(q.wid, q.tau, nids[tau], tree, steps))
}

/// `nativeQueryWalks pairs qs` (`pairs = (pre, post) :: steps.map (pre, post)`; only the
/// prestates are read): fails on any unresolved query.
pub fn query_walks(n: &Native, qs: &[Query]) -> Result<Vec<WalkR>, String> {
    let trees: Vec<&PTrie> = std::iter::once(&n.pre)
        .chain(n.steps.iter().map(|s| &s.pre))
        .collect();
    let (mut nids, mut vids) = (vec![0u64], vec![0u64]);
    for t in &trees {
        nids.push(nids.last().unwrap() + tsize(t));
        vids.push(vids.last().unwrap() + vals_len(t));
    }
    qs.iter()
        .enumerate()
        .map(|(i, q)| {
            native_query_walk(&trees, &nids, &vids, q).ok_or_else(|| {
                format!(
                    "nativeQueryWalks: query {i} (wid {}, tau {}) unresolved",
                    q.wid, q.tau
                )
            })
        })
        .collect()
}

// ------------------------------------------------------- unread-key walks (walkU)

/// `SYM_WILD` (`ZkFormal.NearV3.D1.UnreadIds`): the stub symbol of an extension's child.
pub const SYM_WILD: u64 = 19;
/// The `walkU` stub mode (`mT`).
pub const MODE_STUB: u64 = 4;

/// A stub step `(N, I, z)`: `SEDGE` at lookup position `(N, I)` with symbol slot `z`, consuming
/// the key symbol `sym`.
fn stub_step(n: u64, i: u64, z: u64, sym: u64) -> WStep3 {
    lookup_edge(MODE_STUB, sym, vec![n, i, z, 0, 0, 0])
}

/// The stub step on symbol `rest[0]` (or `END`), then the drain of what follows.
fn stub_then_drain(n: u64, i: u64, z: u64, rest: &[u8]) -> Vec<WStep3> {
    match rest.split_first() {
        None => vec![stub_step(n, i, z, SYM_END)],
        Some((&x, xs)) => {
            let mut v = vec![stub_step(n, i, z, x as u64)];
            v.extend(lookup_drain(xs));
            v
        }
    }
}

/// `leafLookupSteps` with the value stub: an exact match at an unrevealed value ends with the
/// stub `(nid, s, END)` (the value's hash is not in the store).
fn leaf_lookup_steps_u(
    nid: u64,
    vid: u64,
    slot: &Slot,
    pos: u64,
    stored: &[u8],
    key: &[u8],
) -> Vec<WStep3> {
    match (stored.split_first(), key.split_first()) {
        (None, None) => match slot {
            Slot::Val(_) => vec![lookup_edge(
                0,
                SYM_END,
                vec![nid, pos, SYM_END, vid, 0, EK_VAL],
            )],
            Slot::Ref(..) => vec![stub_step(nid, pos, SYM_END, SYM_END)],
        },
        (Some((&a, r#as)), Some((&x, xs))) if a == x => {
            let mut v = vec![lookup_edge(
                0,
                x as u64,
                vec![nid, pos, a as u64, nid, pos + 1, EK_KEY],
            )];
            v.extend(leaf_lookup_steps_u(nid, vid, slot, pos + 1, r#as, xs));
            v
        }
        // every mismatch is an absence, exactly as for the candidates' walks
        _ => leaf_lookup_steps(nid, vid, slot, pos, stored, key).unwrap_or_default(),
    }
}

/// `nativeLookupSteps` of an unread key (`walkU`): as [`native_lookup_steps`], but a child or a
/// value that is not revealed (its hash is not in the honest store, `buildFor`'s `.hash`/`.ref`)
/// ends the walk with a stub step.
pub fn native_lookup_steps_u(nid: u64, vid: u64, t: &PTrie, key: &[u8]) -> Option<Vec<WStep3>> {
    match t {
        PTrie::Hash(_) => None,
        PTrie::Leaf(stored, slot, _) => Some(leaf_lookup_steps_u(nid, vid, slot, 0, stored, key)),
        PTrie::Ext(stored, child, _) => {
            if is_prefix(stored, key) {
                let rest = &key[stored.len()..];
                let len = stored.len() as u64;
                if is_node(child) {
                    native_lookup_steps_u(nid + 1, vid, child, rest).map(|ss| {
                        let mut v =
                            lookup_extension_edges(nid, view_target(nid + 1, child), stored);
                        v.extend(ss);
                        v
                    })
                } else {
                    // dead extension: its last nibble leads to `(nid, s)`, the stub's position
                    let mut v: Vec<WStep3> = lookup_extension_edges(nid, nid, stored);
                    if let Some(last) = v.last_mut() {
                        last.e[4] = len;
                    }
                    v.extend(stub_then_drain(nid, len, SYM_WILD, rest));
                    Some(v)
                }
            } else {
                leaf_lookup_steps(nid, vid, &Slot::Ref(0, vec![]), 0, stored, key)
                    .map(|ss| extension_mismatch_fix(nid, child, stored.len() as u64, ss))
            }
        }
        PTrie::Branch(value, kids, _) => {
            let bm = kids_bitmap(kids) as u64;
            match key.split_first() {
                None => match value {
                    None => Some(vec![WStep3 {
                        mode: 2,
                        sym: SYM_END,
                        e: vec![nid, 0, 0, 0, 0, 0],
                        u: 0,
                        bm,
                        hv: 0,
                        ub: 0,
                    }]),
                    Some(Slot::Ref(..)) => Some(vec![stub_step(nid, 0, SYM_END, SYM_END)]),
                    Some(Slot::Val(_)) => Some(vec![lookup_edge(
                        0,
                        SYM_END,
                        vec![nid, 0, SYM_END, vid, 0, EK_VAL],
                    )]),
                },
                Some((&x, xs)) => {
                    let j = x as usize;
                    let (mut cn, mut cv) = (nid + 1, vid + opt_slot_val_len(value));
                    if j >= kids.len() || kids[j].is_none() {
                        return Some(lookup_branch_absent(
                            nid,
                            bm,
                            value.is_some() as u64,
                            x as u64,
                            xs,
                        ));
                    }
                    for c in kids[..j].iter().flatten() {
                        cn += tsize(c);
                        cv += vals_len(c);
                    }
                    let child = kids[j].as_ref().unwrap();
                    if !is_node(child) {
                        let mut v = vec![stub_step(nid, 0, x as u64, x as u64)];
                        v.extend(lookup_drain(xs));
                        return Some(v);
                    }
                    native_lookup_steps_u(cn, cv, child, xs).map(|ss| {
                        let mut v = vec![lookup_edge(
                            0,
                            x as u64,
                            vec![nid, 0, x as u64, view_target(cn, child), 0, EK_DOWN],
                        )];
                        v.extend(ss);
                        v
                    })
                }
            }
        }
    }
}

/// The `walkU` walk of an unread key on the main pre trie (`τ = 0`): `START`, then
/// [`native_lookup_steps_u`].
pub fn unread_walk(n: &Native, wid: u64, key: &[u8]) -> Result<WalkR, String> {
    let steps = native_lookup_steps_u(0, 0, &n.pre, key)
        .ok_or_else(|| format!("walkU: walk {wid}: the pre-state root is not revealed"))?;
    Ok(native_lookup_walk(wid, 0, 0, &n.pre, steps))
}

/// `rankWalks` over the candidates' walks `ws` then the unread walks `us` (one chain per
/// `EDGE` / `BMAP` key across both tables), with the stub steps of `us` ranked on their own
/// chain (`SEDGE (N, I, z)`).  Returns the ranked `us`.
pub fn rank_unread(ws: &[WalkR], us: &[WalkR]) -> Vec<WalkR> {
    let mut all: Vec<WalkR> = ws.to_vec();
    all.extend(us.iter().cloned());
    let ranked = rank_walks(&all);
    let mut stubs: HashMap<[u64; 3], u64> = HashMap::new();
    ranked[ws.len()..]
        .iter()
        .map(|w| WalkR {
            w: w.w,
            tau: w.tau,
            steps: w
                .steps
                .iter()
                .map(|st| {
                    if st.mode == MODE_STUB {
                        let k = [at(&st.e, 0), at(&st.e, 1), at(&st.e, 2)];
                        let c = stubs.entry(k).or_default();
                        let r = WStep3 { u: *c, ..st.clone() };
                        *c += 1;
                        r
                    } else {
                        st.clone()
                    }
                })
                .collect(),
        })
        .collect()
}

/// The `SEDGE` use counts `(N, I, z) ↦ #stub steps` of the unread walks.
pub fn stub_uses(us: &[WalkR]) -> HashMap<[u64; 3], u64> {
    let mut m: HashMap<[u64; 3], u64> = HashMap::new();
    for w in us {
        for st in &w.steps {
            if st.mode == MODE_STUB {
                *m.entry([at(&st.e, 0), at(&st.e, 1), at(&st.e, 2)]).or_default() += 1;
            }
        }
    }
    m
}

// ------------------------------------------------------------------------ ranks

/// `rankWalks [] ws`: every step gets `u` = the number of earlier EDGE keys
/// (`mode ≤ 1 ↦ e`) equal to its `e`, and `ub` = the number of earlier BMAP keys
/// (`mode = 2 ↦ [e[0], bm, hv]`) equal to `[e[0], bm, hv]` (`rankWalkStep`), "earlier"
/// being all previous walks' steps then this walk's earlier steps.  Lean recounts the
/// prefix per step; the running counters here give the same counts.
pub fn rank_walks(ws: &[WalkR]) -> Vec<WalkR> {
    let mut edges: HashMap<&[u64], u64> = HashMap::new();
    let mut bmaps: HashMap<[u64; 3], u64> = HashMap::new();
    ws.iter()
        .map(|w| WalkR {
            w: w.w,
            tau: w.tau,
            steps: w
                .steps
                .iter()
                .map(|st| {
                    let bk = [at(&st.e, 0), st.bm, st.hv];
                    let ranked = WStep3 {
                        u: edges.get(st.e.as_slice()).copied().unwrap_or(0),
                        ub: bmaps.get(&bk).copied().unwrap_or(0),
                        ..st.clone()
                    };
                    if st.mode <= 1 {
                        *edges.entry(st.e.as_slice()).or_default() += 1;
                    }
                    if st.mode == 2 {
                        *bmaps.entry(bk).or_default() += 1;
                    }
                    ranked
                })
                .collect(),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn st(mode: u64, e: Vec<u64>, bm: u64, hv: u64) -> WStep3 {
        WStep3 {
            mode,
            sym: 0,
            e,
            u: 9,
            bm,
            hv,
            ub: 9,
        }
    }

    /// The quadratic Lean `rankWalkStep` over the explicit prefix.
    fn rank_step_naive(prev: &[WStep3], s: &WStep3) -> (u64, u64) {
        let u = prev.iter().filter(|p| p.mode <= 1 && p.e == s.e).count() as u64;
        let bk = [at(&s.e, 0), s.bm, s.hv];
        let ub = prev
            .iter()
            .filter(|p| p.mode == 2 && [at(&p.e, 0), p.bm, p.hv] == bk)
            .count() as u64;
        (u, ub)
    }

    #[test]
    fn rank_walks_matches_naive() {
        let ws = vec![
            WalkR {
                w: 1,
                tau: 0,
                steps: vec![
                    st(0, vec![1, 2], 0, 0),
                    st(2, vec![5, 0], 3, 1),
                    st(1, vec![1, 2], 0, 0),
                ],
            },
            WalkR {
                w: 2,
                tau: 0,
                steps: vec![
                    st(0, vec![1, 2], 0, 0),
                    st(2, vec![5, 9], 3, 1),
                    st(3, vec![1, 2], 3, 1),
                    st(2, vec![5], 3, 0),
                ],
            },
        ];
        let r = rank_walks(&ws);
        let mut prev = vec![];
        for (w, rw) in ws.iter().zip(&r) {
            for (s, rs) in w.steps.iter().zip(&rw.steps) {
                assert_eq!((rs.u, rs.ub), rank_step_naive(&prev, s));
                prev.push(s.clone());
            }
        }
        assert_eq!(r[1].steps[0].u, 2);
        assert_eq!(r[1].steps[1].ub, 1);
    }

    #[test]
    fn branch_absent_and_leaf_value() {
        // branch with child 0 = leaf [3] (value), 2 = hash; look up [0,3], [1], [2,5].
        let leaf = PTrie::Leaf(vec![3], Slot::Val(vec![42]), 0);
        let t = PTrie::Branch(
            Some(Slot::Val(vec![1])),
            vec![Some(leaf), None, Some(PTrie::Hash(vec![0; 32]))],
            0,
        );
        let ss = native_lookup_steps(10, 20, &t, &[0, 3]).unwrap();
        assert_eq!(ss.len(), 3);
        assert_eq!(ss[0].e, vec![10, 0, 0, 11, 0, EK_DOWN]);
        assert_eq!(ss[1].e, vec![11, 0, 3, 11, 1, EK_KEY]);
        assert_eq!(ss[2].e, vec![11, 1, SYM_END, 21, 0, EK_VAL]);
        let ab = native_lookup_steps(10, 20, &t, &[1]).unwrap();
        assert_eq!((ab[0].mode, ab[0].bm, ab[0].hv), (2, 0b101, 1));
        assert_eq!(ab.len(), 2);
        assert!(native_lookup_steps(10, 20, &t, &[2, 5]).is_none());
        assert_eq!((tsize(&t), vals_len(&t)), (2, 2));
    }

    /// Differential against `np-lean-trie-v3` dumps: `$WALKS_REF` is a directory with
    /// `cases.txt` (`<case> <case_dir>` lines), `<case>.native.json` and `<case>.trie.json`.
    #[test]
    #[ignore]
    fn walks_differential() {
        let Ok(dir) = std::env::var("WALKS_REF") else {
            eprintln!("WALKS_REF unset: skipping");
            return;
        };
        let cases = std::fs::read_to_string(format!("{dir}/cases.txt")).unwrap();
        let (mut n_mv, mut n_q, mut n_ws, mut n_walk, mut total) = (0, 0, 0, 0, 0);
        for line in cases.lines().filter(|l| !l.trim().is_empty()) {
            let mut it = line.split_whitespace();
            let (case, cdir) = (it.next().unwrap(), it.next().unwrap());
            total += 1;
            let rd = |p: String| std::fs::read(&p).unwrap_or_else(|e| panic!("{p}: {e}"));
            let v: serde_json::Value =
                serde_json::from_slice(&rd(format!("{dir}/{case}.native.json"))).unwrap();
            let tr: serde_json::Value =
                serde_json::from_slice(&rd(format!("{dir}/{case}.trie.json"))).unwrap();
            let mut n = Native::from_json(&v).unwrap();
            let k = crate::v3::d0::walk_d0(&rd(format!("{cdir}/claim.bin"))).unwrap();
            let w = crate::v3::hint::decode_w(&rd(format!("{cdir}/witness.bin"))).unwrap();
            n.receipts = crate::v3::hint::applied_receipts(&k, &w);
            let mv = main_values(&n);
            let ok_mv = mv.as_ref().is_ok_and(|m| m.to_json() == v["mainValues"]);
            let mv = mv.unwrap_or_else(|_| MainValues::from_json(&v["mainValues"]).unwrap());
            let qs = queries(&n, &mv).unwrap();
            let qj: Vec<_> = qs
                .iter()
                .map(|x| serde_json::json!({"wid": x.wid, "tau": x.tau, "key": x.key}))
                .collect();
            let ok_q = serde_json::Value::from(qj) == v["queries"];
            let ws = query_walks(&n, &qs);
            let ok_ws = ws.as_ref().is_ok_and(|ws| serde_json::json!(ws) == v["ws"]);
            let ref_ws: Vec<WalkR> = serde_json::from_value(v["ws"].clone()).unwrap();
            let ok_walk = serde_json::json!(rank_walks(&ref_ws)) == tr["walk"];
            n_mv += ok_mv as usize;
            n_q += ok_q as usize;
            n_ws += ok_ws as usize;
            n_walk += ok_walk as usize;
            if !(ok_mv && ok_q && ok_ws && ok_walk) {
                eprintln!(
                    "{case}: mv {ok_mv} q {ok_q} ws {ok_ws} walk {ok_walk} {:?}",
                    ws.err()
                );
            }
        }
        eprintln!(
            "mainValues {n_mv}/{total} queries {n_q}/{total} ws {n_ws}/{total} walk {n_walk}/{total}"
        );
        assert_eq!((n_mv, n_q, n_ws, n_walk), (total, total, total, total));
    }
}
