//! Honest native `upsV3` instances (table 7) of the scheduler upserts: Rust twin of
//! `TrieEntriesV3.lean`'s `honestInst` (the construction inside
//! `Rcpt/Candidates/NativeReaderOrigin.lean` `scheduler_instance_origin_inputs`, with
//! `baseI := default`, `base := default`), `TrieUpsNative.upsRanked`
//! (`physicalPrefixUps`), the window request keys `PhysicalWindowRequests.keys`
//! (`Candidates/PhysicalWindowRequests.lean`) and `TrieUpsNative.useReq`.
//!
//! Lean `Nat` subtraction truncates at `0`; every such site uses `saturating_sub`.
//! Tries are `crate::near::spec::PTrie` (the Lean `Kids` list is the `Vec<Option<_>>`
//! at the same positions).

use std::collections::HashMap;

use super::forest::UseRequests;
use super::native::{TreePart, TreeRun, UpsertW};
use super::native::{UC_BR, UC_LP, UC_LSA, UK_PT, UK_RDB, UK_RDE, UK_SPB, UK_WEX};
use super::ups::{Mem, UpsInst, UpsPartI, pfx, ups_aligned};
use super::{WStep3, WalkR};
use crate::field::P;
use crate::near::spec::{PTrie, Slot, hex_prefix, is_prefix, kids_bitmap};

// ---------------------------------------------------------------------------
// Trie measures (`Spec/Occs.lean`, `Spec/TreeRecs.lean`, `Spec/StoreBuild.lean`)
// ---------------------------------------------------------------------------

/// `tsize t = (occs t).length`: the number of revealed (non-hash) nodes.
fn tsize(t: &PTrie) -> usize {
    match t {
        PTrie::Hash(_) => 0,
        PTrie::Leaf(..) => 1,
        PTrie::Ext(_, c, _) => 1 + tsize(c),
        PTrie::Branch(_, cs, _) => 1 + cs.iter().flatten().map(tsize).sum::<usize>(),
    }
}

/// `slotVal s`.length.
fn slot_vals(s: &Slot) -> usize {
    match s {
        Slot::Val(_) => 1,
        Slot::Ref(..) => 0,
    }
}

/// `optSlotVal sv`.length.
fn opt_slot_vals(s: &Option<Slot>) -> usize {
    s.as_ref().map(slot_vals).unwrap_or(0)
}

/// `(valsOf t).length = ((occs t).flatMap ownVals).length`.
fn vals_len(t: &PTrie) -> usize {
    match t {
        PTrie::Hash(_) => 0,
        PTrie::Leaf(_, s, _) => slot_vals(s),
        PTrie::Ext(_, c, _) => vals_len(c),
        PTrie::Branch(v, cs, _) => {
            opt_slot_vals(v) + cs.iter().flatten().map(vals_len).sum::<usize>()
        }
    }
}

/// `isNode` (`Spec/Codec.lean`).
fn is_node(t: &PTrie) -> bool {
    !matches!(t, PTrie::Hash(_))
}

/// `PTrie.memD` (`mem?.getD 0`).
fn mem_d(t: &PTrie) -> u128 {
    match t {
        PTrie::Hash(_) => 0,
        PTrie::Leaf(_, _, m) | PTrie::Ext(_, _, m) | PTrie::Branch(_, _, m) => *m,
    }
}

/// `Slot.len`.
fn slot_len(s: &Slot) -> u128 {
    match s {
        Slot::Val(v) => v.len() as u128,
        Slot::Ref(l, _) => *l,
    }
}

/// `fdepth t key` / `kfdepth` (`Spec/StoreBuild.lean`).
fn fdepth(t: &PTrie, key: &[u8]) -> u64 {
    match t {
        PTrie::Hash(_) => 0,
        PTrie::Leaf(..) => 1,
        PTrie::Ext(k, c, _) => {
            if is_prefix(k, key) {
                1 + fdepth(c, &key[k.len()..])
            } else {
                1
            }
        }
        PTrie::Branch(_, cs, _) => match key.split_first() {
            None => 1,
            Some((&n, rest)) => {
                1 + match cs.get(n as usize) {
                    Some(Some(c)) => fdepth(c, rest),
                    _ => 0,
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Occurrence addresses (`Assembly/*Addresses.lean`, `ForestAddress.lean`)
// ---------------------------------------------------------------------------

/// `OccurrenceAddress` (`Assembly/OccurrenceAddress.lean`), with the tree's `tsize`
/// cached (the only use of `tree` here).
#[derive(Clone, Copy, Debug)]
struct Addr {
    nid: u64,
    vid: u64,
    size: usize,
}

fn addr(n: u64, v: u64, t: &PTrie) -> Addr {
    Addr {
        nid: n,
        vid: v,
        size: tsize(t),
    }
}

/// `resolutionAddresses n v d t` (`Assembly/ResolutionAddresses.lean`).
fn resolution_addresses(n: u64, v: u64, t: &PTrie, out: &mut Vec<Addr>) {
    out.push(addr(n, v, t));
    if let PTrie::Ext(k, c, _) = t
        && k.is_empty()
    {
        resolution_addresses(n + 1, v, c, out);
    }
}

/// `extendedAddresses n v d t key` (`extended = true`) and `sourceAddresses n v d t key`
/// (`extended = false`; the non-prefix extension ends the path instead of following its
/// `resolutionAddresses`), with their `kid…Addresses` twins.  `depth` is not used.
fn path_addresses(extended: bool, n: u64, v: u64, t: &PTrie, key: &[u8], out: &mut Vec<Addr>) {
    match (t, key.split_first()) {
        (PTrie::Ext(k, c, _), _) => {
            out.push(addr(n, v, t));
            if is_prefix(k, key) {
                path_addresses(extended, n + 1, v, c, &key[k.len()..], out);
            } else if extended {
                resolution_addresses(n + 1, v, c, out);
            }
        }
        (PTrie::Branch(sv, cs, _), Some((&slot, rest))) => {
            out.push(addr(n, v, t));
            // `kid…Addresses (n+1) (v+(optSlotVal sv).length) (d+1) cs slot key`
            let (mut n, mut v) = (n + 1, v + opt_slot_vals(sv) as u64);
            for c in cs.iter().take(slot as usize).flatten() {
                n += tsize(c) as u64;
                v += vals_len(c) as u64;
            }
            if let Some(Some(c)) = cs.get(slot as usize) {
                path_addresses(extended, n, v, c, rest, out);
            }
        }
        _ => out.push(addr(n, v, t)),
    }
}

/// `forestRootAt 0 0 ts tau`: the node / value offsets of tree `tau` in the forest.
fn forest_root_at(ts: &[&PTrie], tau: usize) -> Option<(u64, u64)> {
    if tau >= ts.len() {
        return None;
    }
    let n = ts[..tau].iter().map(|t| tsize(t) as u64).sum();
    let v = ts[..tau].iter().map(|t| vals_len(t) as u64).sum();
    Some((n, v))
}

/// `pathRecordId addresses`: the first address with the same `tsize`, else `0`.
struct RecordId(Vec<Addr>);

impl RecordId {
    fn find(&self, t: &PTrie) -> Option<&Addr> {
        let s = tsize(t);
        self.0.iter().find(|a| a.size == s)
    }
    /// `pathRecordId addresses t`.
    fn id(&self, t: &PTrie) -> u64 {
        self.find(t).map(|a| a.nid).unwrap_or(0)
    }
    /// `occurrenceResolvedId recordId t = viewTarget (recordId t) t`.
    fn resolved(&self, t: &PTrie) -> u64 {
        view_target(self.id(t), t)
    }
}

/// `viewTarget n t` (`Render/Ups/TreeViews.lean`).
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

// ---------------------------------------------------------------------------
// Part plan metadata (`Render/Ups/*Allocation.lean`, `Extract/Ups/PlanDefs.lean`)
// ---------------------------------------------------------------------------

/// `descendKind` (`RDB`, `RDE`).
fn descend_kind(k: u8) -> bool {
    k == UK_RDB || k == UK_RDE
}

/// `descentCount parts`.
fn descent_count(parts: &[TreePart]) -> u64 {
    parts.iter().filter(|p| descend_kind(p.kind)).count() as u64
}

/// `(termPlan cs I).length` (`Extract/Ups/PlanDefs.lean`): the case's terminal parts plus
/// `WEX` when `cs.split && 1 ≤ I`.
fn term_plan_len(cs: u8, matched: u64) -> u64 {
    // LP BR BV BI LSa LSb LSc ESl0 ESl1 ESn0 ESn1
    const BASE: [u64; 11] = [1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2];
    let split = cs >= UC_LSA; // `UCase.split`: all but LP BR BV BI
    BASE.get(cs as usize).copied().unwrap_or(0) + u64::from(split && 1 <= matched)
}

/// `planDepth terminalDepth terminalParts index = terminalDepth − (index+1 − terminalParts)`.
fn plan_depth(td: u64, tp: u64, index: u64) -> u64 {
    td.saturating_sub((index + 1).saturating_sub(tp))
}

/// `planMemoryIndex kind index`.
fn plan_memory_index(kind: u64, index: u64) -> u64 {
    if kind == 0 || kind == 1 || kind == 9 || kind == 11 {
        index
    } else if kind == 10 {
        1
    } else {
        0
    }
}

/// `leafMem k vlen = 50 + 2·|hexPrefix k true| + (vlen + 50)` (`NearSpec/TrieUpsert.lean`).
fn leaf_mem(k: &[u8], vlen: u128) -> u128 {
    50 + 2 * hex_prefix(k, true).len() as u128 + (vlen + 50)
}

/// `extOwnMem k = 50 + 2·|hexPrefix k false|`.
fn ext_own_mem(k: &[u8]) -> u128 {
    50 + 2 * hex_prefix(k, false).len() as u128
}

fn drop<T>(xs: &[T], n: usize) -> &[T] {
    &xs[n.min(xs.len())..]
}

/// `splitChildMemory matched part` (`Render/Ups/TreeSplitMemoryLink.lean`).
fn split_child_memory(matched: u64, p: &TreePart) -> u128 {
    let m1 = (matched + 1) as usize;
    match (p.kind, &p.source, &p.output) {
        (UK_WEX, _, PTrie::Ext(_, child, _)) => mem_d(child),
        (UK_SPB, PTrie::Leaf(key, value, _), _) => leaf_mem(drop(key, m1), slot_len(value)),
        (UK_SPB, PTrie::Ext(key, _, mem), _) => {
            ext_own_mem(drop(key, m1)) + mem.saturating_sub(ext_own_mem(key))
        }
        _ => 0,
    }
}

// ---------------------------------------------------------------------------
// Node views (`Render/Ups/TreeNode.lean`, `NodeEncoding.lean`, `SourceCidBytes.lean`)
// ---------------------------------------------------------------------------

/// `NodeGen3.hplenOf` of a node view: `1 + |key|/2` for leaves/extensions, else `0`.
fn hplen(t: &PTrie) -> u64 {
    match t {
        PTrie::Leaf(k, ..) | PTrie::Ext(k, ..) => 1 + k.len() as u64 / 2,
        _ => 0,
    }
}

/// `NodeGen3.oddOf`.
fn odd(t: &PTrie) -> u64 {
    match t {
        PTrie::Leaf(k, ..) | PTrie::Ext(k, ..) => k.len() as u64 % 2,
        _ => 0,
    }
}

/// One field of `NodeGen3.fieldsOf` as `(state − 14, F.len hplen, cid)`; `cid` is the
/// child window's `cid` (`F.chw`), `0` elsewhere.
type Field = (u64, u64, u64);

/// `NodeGen3.fieldsOf v` for the view of `t` whose children carry the node ids `cid`
/// (`None` = unrevealed `.hash` kid, cid `0`).  States: `TAG HPL HPF KEY VLEN VH BM CH MEM`
/// = `0 … 8`.  A `.hash` tree views as `.branch none []` (`viewNode`); `treeNode` fails on
/// it, so it never reaches the shape/encoding uses.
fn fields_of(t: &PTrie, cid: &dyn Fn(usize) -> u64) -> Vec<Field> {
    let hp = hplen(t);
    let le = |o: &mut Vec<Field>| {
        o.extend([
            (0, 1, 0),
            (1, 4, 0),
            (2, 1, 0),
            (3, hp.saturating_sub(1), 0),
        ]);
    };
    let mut o = vec![];
    match t {
        PTrie::Hash(_) => o.extend([(0, 1, 0), (6, 2, 0), (8, 8, 0)]),
        PTrie::Leaf(..) => {
            le(&mut o);
            o.extend([(4, 4, 0), (5, 32, 0), (8, 8, 0)]);
        }
        PTrie::Ext(..) => {
            le(&mut o);
            o.extend([(7, 32, cid(0)), (8, 8, 0)]);
        }
        PTrie::Branch(v, cs, _) => {
            o.push((0, 1, 0));
            if v.is_some() {
                o.extend([(4, 4, 0), (5, 32, 0)]);
            }
            o.push((6, 2, 0));
            for (j, c) in cs.iter().enumerate() {
                if c.is_some() {
                    o.push((7, 32, cid(j)));
                }
            }
            o.push((8, 8, 0));
        }
    }
    o
}

/// `nonemptyFields (nodeRawShape (treeNode t))`.
fn shape(t: &PTrie) -> Vec<(u64, u64)> {
    fields_of(t, &|_| 0)
        .into_iter()
        .filter(|f| f.1 > 0)
        .map(|f| (f.0, f.1))
        .collect()
}

/// `nodeTypeCode`: leaf 0, extension 1, branch 2, branch with value 3.
fn type_code(t: &PTrie) -> u64 {
    match t {
        PTrie::Leaf(..) => 0,
        PTrie::Ext(..) => 1,
        PTrie::Branch(None, ..) | PTrie::Hash(_) => 2,
        PTrie::Branch(Some(_), ..) => 3,
    }
}

/// `nodeChildren (treeNode t)`: leaf 0, extension 1, branch its present kids.
fn node_children(t: &PTrie) -> usize {
    match t {
        PTrie::Leaf(..) | PTrie::Hash(_) => 0,
        PTrie::Ext(..) => 1,
        PTrie::Branch(_, cs, _) => cs.iter().flatten().count(),
    }
}

/// `valueOffset (treeNode t)` (`Render/Ups/EncodePart.lean`).
fn value_offset(t: &PTrie) -> u64 {
    match t {
        PTrie::Leaf(..) => 5 + hplen(t),
        PTrie::Branch(Some(_), ..) => 1,
        _ => 0,
    }
}

/// `sourceCidBytes (viewNode nid 0 t)`: per serialized byte, the `cid` of its child
/// window (`viewKid`: `.node` ids from `nid+1`, advancing by `tsize`; unrevealed `0`).
fn source_cid_bytes(nid: u64, t: &PTrie) -> Vec<u64> {
    let cids: Vec<u64> = match t {
        PTrie::Ext(_, c, _) => vec![if is_node(c) { nid + 1 } else { 0 }],
        PTrie::Branch(_, cs, _) => {
            let mut n = nid + 1;
            cs.iter()
                .map(|c| match c {
                    Some(c) => {
                        let id = if is_node(c) { n } else { 0 };
                        n += tsize(c) as u64;
                        id
                    }
                    None => 0,
                })
                .collect()
        }
        _ => vec![],
    };
    fields_of(t, &|j| cids.get(j).copied().unwrap_or(0))
        .into_iter()
        .flat_map(|(_, len, cid)| std::iter::repeat_n(cid, len as usize))
        .collect()
}

fn nats(b: &[u8]) -> Vec<u64> {
    b.iter().map(|&x| x as u64).collect()
}

// ---------------------------------------------------------------------------
// Parts (`NativePartEncoding.lean`, `NativeChildLengths.lean`, `PositionedPart.lean`)
// ---------------------------------------------------------------------------

/// `nativeSourceBase recordId run (fun _ => default) k` for a live part `k`
/// (`nativeCidBase ∘ nativeMemoryBase ∘ nativeLengthBase`): `clen`, `mB`, `pcid`.
fn source_base(rid: &RecordId, run: &TreeRun, k: usize, p: &TreePart) -> UpsPartI {
    // `nativeLengthBase`: `(run.parts[planMemoryIndex p.kind.ix k - 1]?).map (nodeEnc ·.output).length`
    let ci = plan_memory_index(p.kind as u64, k as u64).saturating_sub(1) as usize;
    let clen = run
        .parts
        .get(ci)
        .map(|c| c.output.node_ser().len() as u64)
        .unwrap_or(0);
    // `nativeMemoryBase`
    let m_b = if p.kind == UK_RDB || p.kind == UK_RDE || p.kind == UK_PT {
        run.parts
            .get(k.saturating_sub(1))
            .map(|prev| mem_d(&prev.output))
            .unwrap_or(0)
    } else {
        split_child_memory(run.matched, p)
    };
    // `nativeCidBase`
    let pcid = source_cid_bytes(rid.id(&p.source), &p.source);
    UpsPartI {
        clen,
        m_b: m_b as u64,
        pcid,
        ..Default::default()
    }
}

/// `positionedPart recordId depth run k part base` (`withPlanPosition` ∘
/// `withDescentPosition`, then `sN`/`cN`).
fn positioned_part(
    rid: &RecordId,
    depth: u64,
    run: &TreeRun,
    k: usize,
    part: &TreePart,
    base: UpsPartI,
) -> UpsPartI {
    let kind = part.kind as u64;
    let rc = descent_count(drop(&run.parts, k));
    let sd = if kind == 0 || kind == 1 {
        rc.saturating_sub(1)
    } else {
        descent_count(&run.parts)
    };
    let tp = term_plan_len(run.terminal, run.matched);
    UpsPartI {
        kind,
        rc,
        sd,
        pdep: plan_depth(depth, tp, k as u64),
        jm: plan_memory_index(kind, k as u64),
        s_n: rid.id(&part.source),
        c_n: if k == 0 {
            0
        } else {
            run.parts.get(k - 1).map(|p| rid.id(&p.source)).unwrap_or(0)
        },
        ..base
    }
}

/// `encodeTreePart base part`: `none` unless source and output are revealed; otherwise
/// `encodePart {base with kind} (treeNode source) (treeNode output)`.  `treeNode` views
/// every slot/kid as unrevealed, so `ser` is exactly `nodeEnc`.
fn encode_tree_part(base: UpsPartI, part: &TreePart) -> Option<UpsPartI> {
    let (src, dst) = (&part.source, &part.output);
    if !is_node(src) || !is_node(dst) {
        return None;
    }
    Some(UpsPartI {
        kind: part.kind as u64,
        pb: nats(&src.node_ser()),
        ty: type_code(dst),
        qhk: hplen(dst),
        qodd: odd(dst),
        phk: hplen(src),
        podd: odd(src),
        nochild: u64::from(node_children(dst) == 0),
        shape: shape(dst),
        q: nats(&dst.node_ser()),
        soff: value_offset(src),
        ..base
    })
}

/// `encodeNativeParts recordId root run (nativeSourceBase recordId run (fun _ => default))`
/// (`encodeTreeParts (nativePartBase …) 0 run.parts`).
fn encode_native_parts(rid: &RecordId, root: &PTrie, run: &TreeRun) -> Option<Vec<UpsPartI>> {
    let depth = fdepth(root, &[0, 15]).saturating_sub(1);
    run.parts
        .iter()
        .enumerate()
        .map(|(k, part)| {
            let base = positioned_part(rid, depth, run, k, part, source_base(rid, run, k, part));
            encode_tree_part(base, part)
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Instance (`PositionedPart.lean`, `TreeMetadata.lean`, `NativeEncodingFacts.lean`)
// ---------------------------------------------------------------------------

/// `TreeRun.splitNibble`.
fn split_nibble(run: &TreeRun) -> u64 {
    match &run.terminal_source {
        PTrie::Leaf(k, ..) | PTrie::Ext(k, ..) => {
            k.get(run.matched as usize).copied().unwrap_or(0) as u64
        }
        _ => 0,
    }
}

/// `positionedInstance recordId base root run v parts` (on `traceInstance base run v`).
fn positioned_instance(
    rid: &RecordId,
    base: UpsInst,
    root: &PTrie,
    run: &TreeRun,
    v: &[u8],
    parts: Vec<UpsPartI>,
) -> UpsInst {
    let td = fdepth(root, &[0, 15]).saturating_sub(1);
    let tp = term_plan_len(run.terminal, run.matched);
    let desc: Vec<(usize, &TreePart)> = run
        .parts
        .iter()
        .enumerate()
        .filter(|(_, p)| descend_kind(p.kind))
        .collect();
    let mut n: Vec<u64> = desc.iter().rev().map(|(_, p)| rid.id(&p.source)).collect();
    n.push(rid.id(&run.terminal_source));
    let mut dep: Vec<u64> = desc
        .iter()
        .rev()
        .map(|(i, _)| plan_depth(td, tp, *i as u64))
        .collect();
    dep.push(td);
    UpsInst {
        // `traceInstance`
        ci: run.terminal as u64,
        ti: run.matched,
        // `splitCursor [0,15] = consumed [0,15] + matched + 1`
        ts: 2u64.saturating_sub(run.terminal_key.len() as u64) + run.matched + 1,
        x: split_nibble(run),
        v: nats(v),
        // `positionedInstance`
        rid: rid.id(root),
        d: descent_count(&run.parts),
        n,
        dep,
        parts,
        ..base
    }
}

/// `signedInstance I`: `withMemorySign I` on every part (`neg := pfx (X1V I Q) 8 < 0`).
fn signed_instance(i: UpsInst) -> UpsInst {
    let parts = i
        .parts
        .iter()
        .map(|q| {
            let x = pfx(&|l| Mem { i: &i, p: q }.x1(l), 8);
            UpsPartI {
                neg: u64::from(x < 0),
                ..q.clone()
            }
        })
        .collect();
    UpsInst { parts, ..i }
}

// ---------------------------------------------------------------------------
// Walk (`NativeWalkConstruction.lean`, `FourWalk.lean`, `NativeWalkPayload.lean`)
// ---------------------------------------------------------------------------

const SYM_START: u64 = 18;
const SYM_END: u64 = 16;
const EK_DOWN: u64 = 0;
const EK_KEY: u64 = 1;
const EK_VAL: u64 = 2;
const EK_LEND: u64 = 3;

/// `wsym t = [SYM_START, 0, 15, SYM_END].getD t 0`.
fn wsym(t: u64) -> u64 {
    [SYM_START, 0, 15, SYM_END]
        .get(t as usize)
        .copied()
        .unwrap_or(0)
}

/// `walkEnter1 I = I.D=2 ∨ (I.D=1 ∧ (I.ts=2 ∨ I.ti=1))`.
fn walk_enter1(i: &UpsInst) -> bool {
    i.d == 2 || (i.d == 1 && (i.ts == 2 || i.ti == 1))
}

/// `nativePathEdgeKind run level`: `EK_DOWN` at a branch of `nativePathNodes run`, else
/// `EK_KEY`.
fn native_path_edge_kind(run: &TreeRun, level: usize) -> u64 {
    let mut nodes: Vec<&PTrie> = run
        .parts
        .iter()
        .filter(|p| descend_kind(p.kind))
        .map(|p| &p.source)
        .collect();
    nodes.reverse();
    nodes.push(&run.terminal_source);
    match nodes.get(level) {
        Some(PTrie::Branch(..)) => EK_DOWN,
        _ => EK_KEY,
    }
}

/// `nativeTerminalTarget valueId resolvedId run self`.
fn native_terminal_target(value_id: u64, rid: &RecordId, run: &TreeRun, me: u64) -> (u64, u64) {
    let ts = &run.terminal_source;
    if run.terminal == UC_LP || run.terminal == UC_BR {
        match ts {
            PTrie::Leaf(..) | PTrie::Branch(Some(_), ..) => (value_id, 0),
            _ => (0, 0),
        }
    } else if run.terminal == UC_LSA {
        (me, run.matched)
    } else {
        match ts {
            PTrie::Ext(key, child, _) => {
                if run.matched + 1 == key.len() as u64 {
                    match child.as_ref() {
                        PTrie::Hash(_) => (me, key.len() as u64),
                        c => (rid.resolved(c), 0),
                    }
                } else {
                    (me, run.matched + 1)
                }
            }
            _ => (me, run.matched + 1),
        }
    }
}

fn wstep(mode: u64, sym: u64, e: [u64; 6], bm: u64, hv: u64) -> WStep3 {
    WStep3 {
        mode,
        sym,
        e: e.to_vec(),
        u: 0,
        bm,
        hv,
        ub: 0,
    }
}

/// `fourWalk I bm hv ek1 ek2 target targetPos`.
fn four_walk(i: &UpsInst, bm: u64, hv: u64, ek1: u64, ek2: u64, tgt: (u64, u64)) -> Vec<WStep3> {
    let n_at = |k: u64| i.n.get(k as usize).copied().unwrap_or(0);
    let e1 = walk_enter1(i);
    let n0 = n_at(0);
    let n1 = n_at(if e1 { 1 } else { 0 });
    let pos1 = if e1 { 0 } else { 1 };
    let nd = n_at(i.d);
    let start = wstep(0, SYM_START, [0, i.tau, SYM_START, n0, 0, EK_DOWN], 0, 0);
    let tmode = if i.ci <= 1 {
        0
    } else if i.ci <= 3 {
        2
    } else {
        1
    };
    let tsym = if 4 <= i.ci {
        if i.ci == 4 { SYM_END } else { i.x }
    } else {
        wsym(i.ts)
    };
    let ek = if i.ci <= 1 {
        EK_VAL
    } else if i.ci == 4 {
        EK_LEND
    } else {
        EK_KEY
    };
    let terminal = wstep(
        tmode,
        wsym(i.ts),
        [nd, i.ti, tsym, tgt.0, tgt.1, ek],
        bm,
        hv,
    );
    let drain = |t: u64| wstep(3, wsym(t), [0; 6], 0, 0);
    let first = wstep(0, 0, [n0, 0, 0, n1, pos1, ek1], 0, 0);
    let second = wstep(0, 15, [n1, pos1, 15, nd, i.ti, ek2], 0, 0);
    vec![
        start,
        if i.ts == 1 { terminal.clone() } else { first },
        if i.ts == 1 {
            drain(2)
        } else if i.ts == 2 {
            terminal.clone()
        } else {
            second
        },
        if i.ts == 3 { terminal } else { drain(3) },
    ]
}

/// `nativeWalkBase recordId valueId resolvedId baseI root run v`: `baseI` with the four
/// walk rows built from `positionedInstance recordId baseI root run v []`.
fn native_walk_base(
    rid: &RecordId,
    value_id: u64,
    base: UpsInst,
    root: &PTrie,
    run: &TreeRun,
    v: &[u8],
) -> UpsInst {
    let i = positioned_instance(rid, base.clone(), root, run, v, vec![]);
    let tgt = native_terminal_target(value_id, rid, run, rid.id(&run.terminal_source));
    // `terminalBitmap` (`kidBitmap (treeKids kids)`) / `terminalHasVal`
    let (bm, hv) = match &run.terminal_source {
        PTrie::Branch(v, cs, _) => (kids_bitmap(cs) as u64, u64::from(v.is_some())),
        _ => (0, 0),
    };
    let ek1 = native_path_edge_kind(run, 0);
    let ek2 = native_path_edge_kind(run, if walk_enter1(&i) { 1 } else { 0 });
    UpsInst {
        walk: four_walk(&i, bm, hv, ek1, ek2, tgt),
        ..base
    }
}

/// `honestInst us tau u` (`TrieEntriesV3.lean`).
fn honest_inst(pres: &[&PTrie], tau: usize, u: &UpsertW) -> Result<UpsInst, String> {
    let (nid, vid) =
        forest_root_at(pres, tau).ok_or_else(|| format!("ups {tau}: no forest root"))?;
    let root = &u.pre; // `root.tree = pres[tau]`
    let mut ext = vec![];
    path_addresses(true, nid, vid, root, &[0, 15], &mut ext);
    let rid = RecordId(ext);
    let qs = encode_native_parts(&rid, root, &u.run)
        .ok_or_else(|| format!("ups {tau}: encodeNativeParts failed"))?;
    let mut src = vec![];
    path_addresses(false, nid, vid, root, &[0, 15], &mut src);
    let ts = tsize(&u.run.terminal_source);
    let a = src
        .iter()
        .find(|b| b.size == ts)
        .ok_or_else(|| format!("ups {tau}: terminal source address not found"))?;
    // `{nativeRootBase default u.pre u.run with tau}`
    let base0 = UpsInst {
        tau: tau as u64,
        mid: nats(&u.pre.hash_of()),
        post: nats(&u.run.output.hash_of()),
        ..Default::default()
    };
    let b = native_walk_base(&rid, a.vid, base0, root, &u.run, &u.value);
    Ok(signed_instance(positioned_instance(
        &rid, b, root, &u.run, &u.value, qs,
    )))
}

/// `honestInsts us` (one instance per scheduler upsert, `tau` = its index).
pub fn honest_insts(us: &[UpsertW]) -> Result<Vec<UpsInst>, String> {
    let pres: Vec<&PTrie> = us.iter().map(|u| &u.pre).collect();
    us.iter()
        .enumerate()
        .map(|(tau, u)| honest_inst(&pres, tau, u))
        .collect()
}

// ---------------------------------------------------------------------------
// Ranking (`UpsPhysicalPrefix.lean`, `UpsRankPhysical.lean`, `WalkRanks.lean`,
// `WalkRequestInventory.lean`, `UpsCounterSync.lean`)
// ---------------------------------------------------------------------------

/// `UpsGen.step I i = I.walk.getD i default`, `i < 4` (`fourSteps`).
pub(crate) fn four_steps(i: &UpsInst) -> impl Iterator<Item = WStep3> + '_ {
    (0..4).map(|t| i.walk.get(t).cloned().unwrap_or_default())
}

/// The bitmap key `[e.getD 0 0, bm, hv]` of a step.
fn bmap_key(s: &WStep3) -> Vec<u64> {
    vec![s.e.first().copied().unwrap_or(0), s.bm, s.hv]
}

/// The EDGE (`mode ≤ 1`, key `e`) and BMAP (`mode = 2`) multisets of a step prefix:
/// `rankWalkStep previous st` reads the two counts of `st`'s keys in `previous`.
#[derive(Default)]
struct Counters {
    edge: HashMap<Vec<u64>, u64>,
    bmap: HashMap<Vec<u64>, u64>,
}

impl Counters {
    fn add(&mut self, s: &WStep3, d: i64) {
        let m = if s.mode <= 1 {
            self.edge.entry(s.e.clone()).or_default()
        } else if s.mode == 2 {
            self.bmap.entry(bmap_key(s)).or_default()
        } else {
            return;
        };
        *m = (*m as i64 + d) as u64;
    }
    /// `rankWalkStep previous st`.
    fn rank(&self, s: &WStep3) -> WStep3 {
        WStep3 {
            u: self.edge.get(&s.e).copied().unwrap_or(0),
            ub: self.bmap.get(&bmap_key(s)).copied().unwrap_or(0),
            ..s.clone()
        }
    }
    /// `(rankWalk previous w).steps` (each step against `previous ++ w.steps.take i`),
    /// leaving the counters as they were.
    fn rank_walk(&mut self, steps: &[WStep3]) -> Vec<WStep3> {
        let out: Vec<WStep3> = steps
            .iter()
            .map(|s| {
                let r = self.rank(s);
                self.add(s, 1);
                r
            })
            .collect();
        steps.iter().for_each(|s| self.add(s, -1));
        out
    }
}

/// `syncStep st = {st with u := if st.mode=2 then st.ub else st.u}`.
fn sync_step(s: WStep3) -> WStep3 {
    WStep3 {
        u: if s.mode == 2 { s.ub } else { s.u },
        ..s
    }
}

/// `upsRanked ws insts = physicalPrefixUps (ws.flatMap steps) insts
/// = (rankUpsList (ws.flatMap steps) insts).map syncUps`.
pub fn ups_ranked(ws: &[WalkR], insts: &[UpsInst]) -> Vec<UpsInst> {
    let mut c = Counters::default();
    ws.iter().flat_map(|w| &w.steps).for_each(|s| c.add(s, 1));
    insts
        .iter()
        .map(|i| {
            // `rankUps p I`, then `p ++ fourSteps I`
            let walk = c.rank_walk(&i.walk).into_iter().map(sync_step).collect();
            four_steps(i).for_each(|s| c.add(&s, 1));
            UpsInst { walk, ..i.clone() }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Window keys (`PhysicalWindowRequests.lean`, `UpsWindowMessages.lean`, `UpsWindowRanks.lean`)
// ---------------------------------------------------------------------------

/// `UpsV3` columns of `windowFieldKey` (`Tables/Ups.lean`).
const C_SN: usize = 68;
const C_PLEN: usize = 69;
const C_RD: usize = 102;
const C_RB: usize = 103;
const C_SPOS: usize = 104;
const C_PDEP: usize = 182;
const C_RCID: usize = 184;
/// `K_NPOST` (`Near/Ids.lean`).
const K_NPOST: u64 = 8;

/// `PhysicalWindowRequests.keys (upsTraceAligned js) T_UPS`: for every row with `rd = 1`
/// (`physicalWindowRows`), `physicalWindowKey` = `windowFieldKey` as canonical naturals
/// `[K_NPOST + 16·sN, spos, rb, plen, pdep, rcid]`.
pub fn window_keys(js: &[UpsInst]) -> Vec<Vec<u64>> {
    let t = ups_aligned(js);
    let p = P as u64;
    (0..t.height())
        .filter_map(|r| {
            let cell = |c: usize| t.cells[r * t.width + c] as u64;
            (cell(C_RD) == 1).then(|| {
                vec![
                    (K_NPOST + 16 * cell(C_SN)) % p,
                    cell(C_SPOS),
                    cell(C_RB),
                    cell(C_PLEN),
                    cell(C_PDEP),
                    cell(C_RCID),
                ]
            })
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Use requests (`Assembly/TrieUpsNative.lean`, `UpsRequestInventory.lean`)
// ---------------------------------------------------------------------------

/// `useReq ws insts W = ⟨walkEdgeKeys (ws ++ upsWalkInventory insts), walkBmapKeys (…), W⟩`
/// (`upsWalkInventory` = each instance's `fourSteps`).
pub fn use_req(ws: &[WalkR], insts: &[UpsInst], w: Vec<Vec<u64>>) -> UseRequests {
    let steps: Vec<WStep3> = ws
        .iter()
        .flat_map(|w| w.steps.iter().cloned())
        .chain(insts.iter().flat_map(four_steps))
        .collect();
    UseRequests {
        edges: steps
            .iter()
            .filter(|s| s.mode <= 1)
            .map(|s| s.e.clone())
            .collect(),
        bmaps: steps.iter().filter(|s| s.mode == 2).map(bmap_key).collect(),
        windows: w,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf(k: &[u8], v: &[u8]) -> PTrie {
        PTrie::Leaf(k.to_vec(), Slot::Val(v.to_vec()), 7)
    }

    #[test]
    fn sizes_and_addresses() {
        let mut cs = vec![None; 16];
        cs[0] = Some(leaf(&[1], b"a"));
        cs[3] = Some(PTrie::Hash(vec![9; 32]));
        cs[15] = Some(leaf(&[2], b"b"));
        let br = PTrie::Branch(Some(Slot::Val(b"x".to_vec())), cs, 100);
        let root = PTrie::Ext(vec![0], Box::new(br), 200);
        assert_eq!(tsize(&root), 4);
        assert_eq!(vals_len(&root), 3);
        assert_eq!(fdepth(&root, &[0, 15]), 3);
        let mut a = vec![];
        path_addresses(true, 10, 5, &root, &[0, 15], &mut a);
        let got: Vec<(u64, u64, usize)> = a.iter().map(|a| (a.nid, a.vid, a.size)).collect();
        // ext (10), branch (11, value 1), kid 15 after kid 0 (tsize 1, 1 value)
        assert_eq!(got, vec![(10, 5, 4), (11, 5, 3), (13, 7, 1)]);
        // non-prefix extension: `extendedAddresses` follows the resolution chain only for
        // the extended variant
        let x = PTrie::Ext(
            vec![1],
            Box::new(PTrie::Ext(vec![], Box::new(leaf(&[], b"")), 1)),
            2,
        );
        let (mut e, mut s) = (vec![], vec![]);
        path_addresses(true, 0, 0, &x, &[0, 15], &mut e);
        path_addresses(false, 0, 0, &x, &[0, 15], &mut s);
        assert_eq!((e.len(), s.len()), (3, 1));
        assert_eq!(view_target(4, &x.clone()), 4);
        if let PTrie::Ext(_, c, _) = &x {
            assert_eq!(view_target(4, c), 5);
        }
    }

    #[test]
    fn cid_bytes_follow_layout() {
        let mut cs = vec![None; 4];
        cs[1] = Some(leaf(&[1, 2], b"a"));
        cs[2] = Some(PTrie::Hash(vec![0; 32]));
        let br = PTrie::Branch(None, cs, 1);
        let c = source_cid_bytes(5, &br);
        assert_eq!(c.len(), br.node_ser().len());
        assert_eq!(c[3..35], [6; 32]);
        assert!(c[35..].iter().all(|&x| x == 0));
        assert_eq!(shape(&br), vec![(0, 1), (6, 2), (7, 32), (7, 32), (8, 8)]);
        // leaf with an even key: no `KEY` bytes beyond the flag byte (`hplen − 1 = 0`)
        assert_eq!(shape(&leaf(&[], b"")).len(), 6);
    }

    #[test]
    fn plan_arithmetic_truncates() {
        assert_eq!(plan_depth(2, 3, 0), 2);
        assert_eq!(plan_depth(2, 1, 5), 0);
        assert_eq!(term_plan_len(UC_LSA, 0), 2);
        assert_eq!(term_plan_len(UC_LSA, 1), 3);
        assert_eq!(term_plan_len(UC_LP, 1), 1);
    }

    #[test]
    fn ranking_counts_prefix() {
        let s = |mode, e: u64| wstep(mode, 0, [e, 0, 0, 0, 0, 0], 1, 0);
        let ws = vec![WalkR {
            w: 0,
            tau: 0,
            steps: vec![s(0, 1), s(0, 1), s(2, 4)],
        }];
        let i = UpsInst {
            walk: vec![s(0, 1), s(2, 4), s(2, 4), s(3, 0)],
            ..Default::default()
        };
        let r = ups_ranked(&ws, &[i.clone(), i.clone()]);
        let us: Vec<Vec<u64>> = r
            .iter()
            .map(|i| i.walk.iter().map(|s| s.u).collect())
            .collect();
        assert_eq!(us, vec![vec![2, 1, 2, 0], vec![3, 3, 4, 0]]);
        let q = use_req(&ws, &[i], vec![]);
        assert_eq!((q.edges.len(), q.bmaps.len()), (3, 3));
    }
}
