//! near-arena-oracle-v3-d1a: nearcore-side measures of the D1a amendments
//! (spec/near-chunk-validation-d1a.md) that nearcore's own types can judge without a node:
//!
//! * T1 `w.tx_count`: `ChunkStateWitness::transactions().len()` after nearcore's borsh decoding
//!   of the state witness (the count NT0 = 4,096 bounds);
//! * A7ᴰ¹ `w.unfolded`: the D0a native measure (unfolded pre tries + unfolded native post tries)
//!   over the D1 run's tries, the main transition's keys being the D0 read keys
//!   (`BufferedReceiptIndices`, `0x0f`, delayed / yield indices, groups data of every buffered
//!   shard, receivers of the source-proof receipts, refund access keys) **plus the signer account
//!   and access key of every transaction** (`TrieKey::Account`, `TrieKey::AccessKey` from
//!   nearcore's `SignedTransaction`);
//! * A10ᴰ¹ `w.path_depth`: the longest `MerklePath` of the witness's source receipt proofs (an
//!   accepted witness holds exactly the used ones).
//!
//! Command:
//!   measure-case --dump FILE
//!          FILE: JSON lines {case, pre_root, blobs, main_keys} (oracle/tools/dump_a7_store_v3_d1a.py:
//!          the claim's B2 own-slot prev_state_root, preimages of the nodes/values the run wrote,
//!          and the Python checker's main read keys). Prints per case {case, verdict: measured |
//!          reject, unfold, tx_count, new_tx_count, max_path_depth, keys_equal}. Exit 1 if any
//!          case's read keys differ from the Python checker's.
//!
//! The counting code (`unfold_pre`, `unfold_native`, `pre_at`, `pre_value`) is a copy of
//! oracle/v3-d0a/src/d0a.rs (2026-10-13; private there, and that crate pulls in the whole node),
//! applied to nearcore's `RawTrieNodeWithSize`. The post nodes come from the dumped preimages,
//! each stored under its own SHA-256; the walk starts at the witness's post-state roots, so a
//! blob cannot steer the count. Independent of the Lean / Python implementations.

use near_primitives::hash::{CryptoHash, hash as nhash};
use near_primitives::receipt::{BufferedReceiptIndices, Receipt, ReceiptEnum};
use near_primitives::state::PartialState;
use near_primitives::stateless_validation::state_witness::ChunkStateWitness;
use near_primitives::trie_key::TrieKey;
use near_store::{PartialStorage, RawTrieNode, RawTrieNodeWithSize, Trie};
use serde_json::json;
use std::collections::HashMap;

fn nibs(b: &[u8]) -> Vec<u8> {
    b.iter().flat_map(|x| [x >> 4, x & 15]).collect()
}

/// hex-prefix decode (`NibbleSlice::from_encoded`)
fn hp(e: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    if e.is_empty() {
        return out;
    }
    if e[0] & 0x10 != 0 {
        out.push(e[0] & 15);
    }
    out.extend(nibs(&e[1..]));
    out
}

struct MapStore(HashMap<CryptoHash, Vec<u8>>);
impl MapStore {
    fn raw(&self, h: &CryptoHash) -> Option<Vec<u8>> {
        self.0.get(h).cloned()
    }
}

fn node(st: &MapStore, h: &CryptoHash) -> Option<(Vec<u8>, RawTrieNode)> {
    let raw = st.raw(h)?;
    let n: RawTrieNodeWithSize = borsh::from_slice(&raw).ok()?;
    Some((raw, n.node))
}

fn value(st: &MapStore, len: u32, h: &CryptoHash, want: bool) -> u64 {
    if !want {
        return 0;
    }
    match st.raw(h) {
        Some(v) if v.len() == len as usize => v.len() as u64,
        _ => 0,
    }
}

fn below(keys: &[Vec<u8>], k: &[u8]) -> Vec<Vec<u8>> {
    keys.iter()
        .filter(|x| x.starts_with(k))
        .map(|x| x[k.len()..].to_vec())
        .collect()
}

fn unfold_pre(st: &MapStore, h: &CryptoHash, keys: &[Vec<u8>]) -> u64 {
    if keys.is_empty() {
        return 0;
    }
    let Some((raw, n)) = node(st, h) else {
        return 0;
    };
    let mut tot = raw.len() as u64;
    match n {
        RawTrieNode::Leaf(k, v) => {
            let k = hp(&k);
            tot += value(st, v.length, &v.hash, keys.iter().any(|x| *x == k));
        }
        RawTrieNode::Extension(k, c) => {
            let k = hp(&k);
            tot += unfold_pre(st, &c, &below(keys, &k));
        }
        RawTrieNode::BranchNoValue(ref cs) | RawTrieNode::BranchWithValue(_, ref cs) => {
            if let RawTrieNode::BranchWithValue(v, _) = &n {
                tot += value(st, v.length, &v.hash, keys.iter().any(|x| x.is_empty()));
            }
            for (i, c) in cs.0.iter().enumerate() {
                if let Some(c) = c {
                    tot += unfold_pre(st, c, &below(keys, &[i as u8]));
                }
            }
        }
    }
    tot
}

/// The pre-trie nodes starting exactly at absolute nibble position `pos` (the node reached
/// there and, below empty-key extensions, their children, which share the position).
fn pre_at(st: &MapStore, root: &CryptoHash, pos: &[u8]) -> Vec<CryptoHash> {
    let (mut h, mut d) = (*root, 0usize);
    while d < pos.len() {
        let Some((_, n)) = node(st, &h) else {
            return vec![];
        };
        match n {
            RawTrieNode::Leaf(..) => return vec![],
            RawTrieNode::Extension(k, c) => {
                let k = hp(&k);
                if !pos[d..].starts_with(&k) {
                    return vec![];
                }
                d += k.len();
                h = c;
            }
            RawTrieNode::BranchNoValue(cs) | RawTrieNode::BranchWithValue(_, cs) => {
                let Some(c) = cs.0[pos[d] as usize] else {
                    return vec![];
                };
                h = c;
                d += 1;
            }
        }
    }
    let mut out = vec![h];
    while let Some((_, RawTrieNode::Extension(k, c))) = node(st, &h) {
        if !hp(&k).is_empty() || out.contains(&c) {
            break;
        }
        out.push(c);
        h = c;
    }
    out
}

/// The value reference `(length, hash)` the pre trie holds at the full nibble key `key`.
fn pre_value(st: &MapStore, root: &CryptoHash, key: &[u8]) -> Option<(u32, CryptoHash)> {
    let (mut h, mut d) = (*root, 0usize);
    loop {
        let (_, n) = node(st, &h)?;
        match n {
            RawTrieNode::Leaf(k, v) => return (hp(&k) == key[d..]).then_some((v.length, v.hash)),
            RawTrieNode::Extension(k, c) => {
                let k = hp(&k);
                if !key[d..].starts_with(&k) {
                    return None;
                }
                d += k.len();
                h = c;
            }
            RawTrieNode::BranchNoValue(cs) => {
                h = (*cs.0.get(*key.get(d)? as usize)?)?;
                d += 1;
            }
            RawTrieNode::BranchWithValue(v, cs) => {
                if d == key.len() {
                    return Some((v.length, v.hash));
                }
                h = (*cs.0.get(key[d] as usize)?)?;
                d += 1;
            }
        }
    }
}

/// Lean `unfoldedBytesT` of the native post trie below post node `h` at position `pos`.
fn unfold_native(
    pre_st: &MapStore,
    pre_root: &CryptoHash,
    post_st: &MapStore,
    h: &CryptoHash,
    pos: &[u8],
    keys: &[Vec<u8>],
) -> u64 {
    let created = !pre_at(pre_st, pre_root, pos).contains(h);
    if !created && keys.is_empty() {
        return 0;
    }
    let st = if created { post_st } else { pre_st };
    let Some((raw, n)) = node(st, h) else {
        return 0;
    };
    let val = |vpos: &[u8], len: u32, vh: &CryptoHash, want: bool| -> u64 {
        if created && pre_value(pre_st, pre_root, vpos) != Some((len, *vh)) {
            value(post_st, len, vh, true)
        } else {
            value(pre_st, len, vh, want)
        }
    };
    let mut tot = raw.len() as u64;
    match n {
        RawTrieNode::Leaf(k, v) => {
            let k = hp(&k);
            let vpos = [pos, &k[..]].concat();
            tot += val(&vpos, v.length, &v.hash, keys.iter().any(|x| *x == k));
        }
        RawTrieNode::Extension(k, c) => {
            let k = hp(&k);
            tot += unfold_native(
                pre_st,
                pre_root,
                post_st,
                &c,
                &[pos, &k[..]].concat(),
                &below(keys, &k),
            );
        }
        RawTrieNode::BranchNoValue(ref cs) | RawTrieNode::BranchWithValue(_, ref cs) => {
            if let RawTrieNode::BranchWithValue(v, _) = &n {
                tot += val(pos, v.length, &v.hash, keys.iter().any(|x| x.is_empty()));
            }
            for (i, c) in cs.0.iter().enumerate() {
                if let Some(c) = c {
                    let sub = below(keys, &[i as u8]);
                    tot += unfold_native(
                        pre_st,
                        pre_root,
                        post_st,
                        c,
                        &[pos, &[i as u8][..]].concat(),
                        &sub,
                    );
                }
            }
        }
    }
    tot
}

/// The main transition's keys of the D1 run: the D0 read keys plus every transaction's
/// signer account and access key.
fn main_keys(
    w: &ChunkStateWitness,
    receipts: &[Receipt],
    bufs: Option<BufferedReceiptIndices>,
) -> Vec<Vec<u8>> {
    let mut keys: Vec<TrieKey> = vec![
        TrieKey::DelayedReceiptIndices,
        TrieKey::BandwidthSchedulerState,
        TrieKey::BufferedReceiptIndices,
        TrieKey::PromiseYieldIndices,
    ];
    for s in bufs
        .map(|b| b.shard_buffers.keys().cloned().collect::<Vec<_>>())
        .unwrap_or_default()
    {
        keys.push(TrieKey::BufferedReceiptGroupsQueueData { receiving_shard: s });
    }
    for r in receipts {
        keys.push(TrieKey::Account {
            account_id: r.receiver_id().clone(),
        });
        if let ReceiptEnum::Action(ar) = r.receipt() {
            if r.predecessor_id().is_system() && &ar.signer_id == r.receiver_id() {
                keys.push(TrieKey::AccessKey {
                    account_id: r.receiver_id().clone(),
                    key_handle: ar.signer_public_key.clone().into(),
                });
            }
        }
    }
    for t in w.transactions() {
        let tx = &t.transaction;
        keys.push(TrieKey::Account {
            account_id: tx.signer_id().clone(),
        });
        keys.push(TrieKey::AccessKey {
            account_id: tx.signer_id().clone(),
            key_handle: tx.public_key().clone().into(),
        });
    }
    keys.iter().map(|k| nibs(&k.to_vec())).collect()
}

struct Measured {
    unfold: u64,
    tx_count: usize,
    new_tx_count: usize,
    max_path_depth: usize,
    keys: Vec<Vec<u8>>,
}

fn measure_offline(
    witness_file: &[u8],
    pre_root: &CryptoHash,
    blobs: &[Vec<u8>],
) -> Result<Measured, String> {
    let mut r = witness_file;
    let mut field = || -> Result<Vec<u8>, String> {
        let n = u32::from_le_bytes(r.get(..4).ok_or("witness file")?.try_into().unwrap()) as usize;
        let v = r.get(4..4 + n).ok_or("witness file")?.to_vec();
        r = &r[4 + n..];
        Ok(v)
    };
    let _tag = field()?;
    let w: ChunkStateWitness = borsh::from_slice(&field()?).map_err(|e| e.to_string())?;
    if *pre_root == CryptoHash::default() {
        return Err("empty main pre-state: MissingTrieValue (BufferedReceiptIndices)".into());
    }
    let ChunkStateWitness::V2(x) = &w;
    let trie = Trie::from_recorded_storage(
        PartialStorage {
            nodes: x.main_state_transition.base_state.clone(),
        },
        *pre_root,
        false,
    );
    let bufs: Option<BufferedReceiptIndices> =
        near_store::get(&trie, &TrieKey::BufferedReceiptIndices).map_err(|e| e.to_string())?;
    let receipts: Vec<_> = x
        .source_receipt_proofs
        .values()
        .flat_map(|p| p.0.iter().cloned())
        .collect();
    let keys = main_keys(&w, &receipts, bufs);
    let mapst = |t: &near_primitives::stateless_validation::state_witness::ChunkStateTransition| {
        let PartialState::TrieValues(vals) = &t.base_state;
        MapStore(vals.iter().map(|v| (nhash(v), v.to_vec())).collect())
    };
    let mut post = HashMap::new();
    for t in std::iter::once(&x.main_state_transition).chain(&x.implicit_transitions) {
        let PartialState::TrieValues(vals) = &t.base_state;
        post.extend(vals.iter().map(|v| (nhash(v), v.to_vec())));
    }
    post.extend(blobs.iter().map(|b| (nhash(b), b.clone())));
    let post = MapStore(post);
    let imp_keys: Vec<Vec<u8>> = [
        TrieKey::DelayedReceiptIndices,
        TrieKey::BandwidthSchedulerState,
    ]
    .iter()
    .map(|k| nibs(&k.to_vec()))
    .collect();
    let mut unfold = 0;
    let s = mapst(&x.main_state_transition);
    unfold += unfold_pre(&s, pre_root, &keys)
        + unfold_native(
            &s,
            pre_root,
            &post,
            &x.main_state_transition.post_state_root,
            &[],
            &keys,
        );
    let mut root = x.main_state_transition.post_state_root;
    for t in &x.implicit_transitions {
        let s = mapst(t);
        unfold += unfold_pre(&s, &root, &imp_keys)
            + unfold_native(&s, &root, &post, &t.post_state_root, &[], &imp_keys);
        root = t.post_state_root;
    }
    Ok(Measured {
        unfold,
        tx_count: w.transactions().len(),
        new_tx_count: w.new_transactions().len(),
        max_path_depth: x
            .source_receipt_proofs
            .values()
            .map(|p| p.1.proof.len())
            .max()
            .unwrap_or(0),
        keys,
    })
}

fn arg(args: &[String], name: &str) -> Option<String> {
    args.iter()
        .position(|a| a == name)
        .and_then(|i| args.get(i + 1).cloned())
}

fn cmd_measure_case(args: &[String]) -> i32 {
    let dump = std::fs::read_to_string(arg(args, "--dump").expect("--dump")).unwrap();
    let mut bad = 0;
    for line in dump.lines().filter(|l| !l.trim().is_empty()) {
        let j: serde_json::Value = serde_json::from_str(line).unwrap();
        let case = j["case"].as_str().unwrap().to_string();
        let hexb = |x: &serde_json::Value| hex::decode(x.as_str().unwrap()).unwrap();
        let root = CryptoHash(hexb(&j["pre_root"]).try_into().unwrap());
        let blobs: Vec<Vec<u8>> = j["blobs"].as_array().unwrap().iter().map(hexb).collect();
        let wf = std::fs::read(std::path::Path::new(&case).join("witness.bin")).unwrap();
        let out = match measure_offline(&wf, &root, &blobs) {
            Ok(m) => {
                let mut ours: Vec<String> = m
                    .keys
                    .iter()
                    .map(|k| {
                        hex::encode(k.chunks(2).map(|p| p[0] << 4 | p[1]).collect::<Vec<u8>>())
                    })
                    .collect();
                ours.sort();
                ours.dedup();
                let mut theirs: Vec<String> = j["main_keys"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|x| x.as_str().unwrap().to_string())
                    .collect();
                theirs.sort();
                theirs.dedup();
                bad += (ours != theirs) as i32;
                json!({"case": case, "verdict": "measured", "unfold": m.unfold, "tx_count": m.tx_count,
                       "new_tx_count": m.new_tx_count, "max_path_depth": m.max_path_depth,
                       "keys_equal": ours == theirs, "n_keys": ours.len()})
            }
            Err(e) => json!({"case": case, "verdict": "reject", "reason": e}),
        };
        println!("{out}");
    }
    if bad > 0 { 1 } else { 0 }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let code = match args.get(1).map(String::as_str) {
        Some("measure-case") => cmd_measure_case(&args),
        _ => {
            eprintln!("usage: near-arena-oracle-v3-d1a measure-case --dump FILE (see src/main.rs)");
            2
        }
    };
    std::process::exit(code);
}
