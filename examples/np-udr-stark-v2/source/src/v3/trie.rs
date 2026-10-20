//! The honest trie-side entries of `nearAirV3` from a real claim + witness: tables 2
//! (node + A7 `rpl`), 3 (head), 4 (val + A7 `rpl`), 5 (walk), 6 (uniq), 7 (ups) and 21
//! (size + A7 `yN`).  Rust twin of `conformance/TrieEntriesV3.lean` (`np-lean-trie-v3`),
//! itself the evaluation of the entry lists of `Assembly/TrieSide.lean` `trie_side_exact`:
//!
//! | output | Lean | Rust |
//! |---|---|---|
//! | native objects | `nativeOf` | [`native::native_of`] |
//! | `ws` | `nativeQueryWalks pairs (allLookupQueries …)` | [`walks`] |
//! | `insts`, `Js` | `honestInsts us`, `upsRanked ws insts` | [`upsnat`] |
//! | `q` | `useReq ws insts (PhysicalWindowRequests.keys (upsTraceAligned Js) T_UPS)` | [`upsnat::use_req`] |
//! | node / val / head / uniq | `TrieNative.nodes … q`, `vals`, `heads … q.edges`, `uniqNative` | [`forest`] |
//! | walk | `rankWalks [] ws` | [`walks::rank_walks`] |
//! | A7 `S`, `SV` | `[n] ∈ insts.flatMap upsRplMsgs / upsRplvMsgs` | [`rpl_msgs`], [`rplv_msgs`] |
//! | size | `honestSizeV ns es sizeBlocks`, `ovhNat pub`, `yN` | [`size_entry`] |
//!
//! The output JSON (`npudr v3trie <case_dir>`) has the same shape and values as
//! `np-lean-trie-v3 <case_dir>` (`node`/`val` objects carry `"rpl"`; `size` is
//! `[{x0, x1, x2, ovh, yN}]`; `checks` the same self-checks).

use std::collections::HashSet;

use serde_json::{Value, json};

use super::d0;
use super::hint::{ProofEntry, decode_w};
use super::native::{self, Native};
use super::node::NodeS3;
use super::prep::{Prep, SrcList};
use super::ups::UpsInst;
use super::{ValE, forest, upsnat, walks};
use crate::near::spec::encode_receipts;

/// `UpsGen.part I k` = `parts.getD k default`.
fn part_q_len(i: &UpsInst, k: usize) -> usize {
    i.parts.get(k).map(|p| p.q.len()).unwrap_or(0)
}

/// `TrieA7.nDOf I`.
fn n_d_of(i: &UpsInst) -> u64 {
    match i.d {
        0..=2 => i.n.get(i.d as usize).copied().unwrap_or(0),
        _ => 0,
    }
}

/// `TrieA7.upsRplMsgs I` (singletons; every value is below `P` on honest inputs, the `% P` is
/// kept for fidelity).
pub fn rpl_msgs(i: &UpsInst) -> Vec<u64> {
    const P: u64 = crate::v3::P as u64;
    let mut v = vec![n_d_of(i) % P];
    for (k, p) in i.parts.iter().enumerate() {
        let upper = p.kind == 0 || p.kind == 1 || p.kind == 11;
        if upper && part_q_len(i, k) > 0 {
            v.push(p.s_n % P);
        }
    }
    v
}

/// `TrieA7.upsRplvMsgs I`: `[[e[3]]]` if walk step 3 has mode 0.
pub fn rplv_msgs(i: &UpsInst) -> Vec<u64> {
    let st = i.walk.get(3);
    match st {
        Some(s) if s.mode == 0 => vec![s.e.get(3).copied().unwrap_or(0) % crate::v3::P as u64],
        None => vec![0], // `step I 3 = default`: mode 0, `e = []`
        _ => vec![],
    }
}

/// `TrieA7.upsA7Total`.
pub fn ups_a7_total(js: &[UpsInst]) -> u64 {
    js.iter()
        .map(|i| i.v.len() as u64 + i.parts.iter().map(|p| p.q.len() as u64).sum::<u64>())
        .sum()
}

/// `nodeA7Total ns S`.
pub fn node_a7_total(ns: &[NodeS3], s: &HashSet<u64>) -> u64 {
    ns.iter()
        .enumerate()
        .map(|(n, x)| (if s.contains(&(n as u64)) { 1 } else { 2 }) * x.v.ser_len() as u64)
        .sum()
}

/// `valA7Total es SV`.
pub fn val_a7_total(es: &[ValE], s: &HashSet<u64>) -> u64 {
    es.iter()
        .enumerate()
        .map(|(t, e)| (if s.contains(&(t as u64)) { 1 } else { 2 }) * e.len)
        .sum()
}

/// `Public.sourceDup`.
fn source_dup(lists: &[SrcList], j: usize) -> bool {
    lists[..j].iter().any(|s| s.key == lists[j].key)
}

/// `srcpSize A.sizeBlocks`: `Σ_j L_j + 33 · |path_j|` over `DedupCompile.blocks p.lists
/// w.entries`, duplicate blocks with `path := []`.  `L_j = |u64 toShard ‖ encodeReceipts|`
/// of `entryAt` (`lookupLast` by key; missing → the empty fallback, `L = 8 + 4`).
pub fn srcp_size(lists: &[SrcList], entries: &[ProofEntry]) -> u64 {
    (0..lists.len())
        .map(|j| {
            let e = entries.iter().rev().find(|e| e.key == lists[j].key);
            let (l, path) = match e {
                Some(e) => (8 + encode_receipts(&e.receipts).len(), e.path.len()),
                None => (8 + encode_receipts(&[]).len(), 0),
            };
            let path = if source_dup(lists, j) { 0 } else { path };
            (l + 33 * path) as u64
        })
        .sum()
}

/// `ovhNat (pubOf (preparedBytes p 0))`: the u32 LE at `SizeV3.PH_WOVH = 198`.
pub fn ovh_of(p: &Prep) -> u64 {
    let b = super::public::prepared_bytes(p, 0);
    (0..4)
        .map(|i| (*b.get(198 + i).unwrap_or(&0) as u64) << (8 * i))
        .sum()
}

/// `honestSizeV ns es bs` + the A7 totals as the size entry.
pub fn size_entry(ns: &[NodeS3], es: &[ValE], x2: u64, ovh: u64, y: [u64; 3]) -> Value {
    let x0: u64 = ns
        .iter()
        .filter(|s| !s.dup)
        .map(|s| s.v.ser_len() as u64)
        .sum();
    let x1: u64 = es.iter().filter(|e| !e.vz && !e.dup).map(|e| e.len).sum();
    json!([{ "x0": x0, "x1": x1, "x2": x2, "ovh": ovh, "yN": y }])
}

fn with_rpl<T: serde::Serialize>(xs: &[T], s: &HashSet<u64>) -> Result<Value, String> {
    xs.iter()
        .enumerate()
        .map(|(i, x)| {
            let mut o = serde_json::to_value(x).map_err(|e| e.to_string())?;
            o.as_object_mut()
                .ok_or("entry is not an object")?
                .insert("rpl".into(), Value::Bool(s.contains(&(i as u64))));
            Ok(o)
        })
        .collect::<Result<Vec<_>, String>>()
        .map(Value::Array)
}

/// The honest trie-side entries (and self-checks) from the native objects and the
/// prepared statement / proof entries (size `x2`, `ovh`).
pub fn entries_of(n: &Native, p: &Prep, entries: &[ProofEntry]) -> Result<Value, String> {
    entries_of_u(n, p, entries, &[]).map(|x| x.0)
}

/// [`entries_of`] with the unread-key walks `us` of `walkU` (`nearAirV3D1`, lane v3-d1-a7b):
/// their `EDGE` / `BMAP` steps count in the node and head use requests (one chain per key over
/// `walkV3`, the ups walks and `walkU`).  Also returns `us` ranked (`walks::rank_unread`).
pub fn entries_of_u(
    n: &Native,
    p: &Prep,
    entries: &[ProofEntry],
    us: &[super::WalkR],
) -> Result<(Value, Vec<super::WalkR>), String> {
    let v = walks::main_values(n)?;
    let qs = walks::queries(n, &v)?;
    let ws = walks::query_walks(n, &qs)?;
    let insts = upsnat::honest_insts(&n.us)?;
    let js = upsnat::ups_ranked(&ws, &insts);
    let w = upsnat::window_keys(&js);
    let all: Vec<super::WalkR> = ws.iter().chain(us).cloned().collect();
    let q = upsnat::use_req(&all, &insts, w);
    // `walkU`'s chain ranks come after `walkV3`'s and the ups walks' (`ups_ranked`)
    let mut prior = ws.clone();
    prior.push(super::WalkR {
        w: 0,
        tau: 0,
        steps: insts.iter().flat_map(upsnat::four_steps).collect(),
    });
    let us_ranked = walks::rank_unread(&prior, us);
    let ns = forest::nodes(n, &q)?;
    let es = forest::vals(n)?;
    let hs = forest::heads(n, &q.edges)?;
    let l = forest::uniq(n)?;
    let walk = walks::rank_walks(&ws);
    let rpl: Vec<u64> = insts.iter().flat_map(rpl_msgs).collect();
    let rplv: Vec<u64> = insts.iter().flat_map(rplv_msgs).collect();
    let s: HashSet<u64> = rpl.iter().copied().collect();
    let sv: HashSet<u64> = rplv.iter().copied().collect();
    let y = [
        node_a7_total(&ns, &s),
        val_a7_total(&es, &sv),
        ups_a7_total(&js),
    ];
    let x2 = srcp_size(&p.lists, entries);
    let size = size_entry(&ns, &es, x2, ovh_of(p), y);
    let x01 = size[0]["x0"].as_u64().unwrap_or(0) + size[0]["x1"].as_u64().unwrap_or(0);
    let checks = json!({
        "insts = scheduler calls": insts.len() == n.us.len(),
        "rpl msgs: distinct singletons < |node|": rpl.iter().all(|&x| x < ns.len() as u64) && s.len() == rpl.len(),
        "rplv msgs: distinct singletons < |val|": rplv.iter().all(|&x| x < es.len() as u64) && sv.len() == rplv.len(),
        "A7 total ≤ B0": y.iter().sum::<u64>() <= 2_000_000,
        "base size ≤ B0": x01 <= 2_000_000,
    });
    let ser = |x: &dyn erased::Ser| x.to_value();
    Ok((json!({
        "node": with_rpl(&ns, &s)?,
        "val": with_rpl(&es, &sv)?,
        "head": ser(&hs),
        "walk": ser(&walk),
        "uniq": ser(&l),
        "ups": ser(&js),
        "size": size,
        "checks": checks,
    }), us_ranked))
}

mod erased {
    pub trait Ser {
        fn to_value(&self) -> serde_json::Value;
    }
    impl<T: serde::Serialize> Ser for T {
        fn to_value(&self) -> serde_json::Value {
            serde_json::to_value(self).unwrap_or(serde_json::Value::Null)
        }
    }
}

/// `np-lean-trie-v3 <case>` in Rust: the native execution, `prepD0 cb (hintOf cb w)` (for
/// the size `x2` / `ovh`), then [`entries_of`].
pub fn entries(cb: &[u8], wb: &[u8]) -> Result<Value, String> {
    let n = native::native_of(cb, wb)?;
    let p = d0::prep(cb, &super::hint::hint_of(cb, wb))?;
    let w = decode_w(wb)?;
    entries_of(&n, &p, &w.entries)
}
