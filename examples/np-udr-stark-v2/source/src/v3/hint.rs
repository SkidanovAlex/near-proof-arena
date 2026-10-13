//! The proof-carried hint: the Rust twin of `NearSpecV3.hintOf`
//! (`spec/lean/v3/NearSpecV3/PrepD0.lean`, "`hintOf`").
//!
//! `hintOf cb w = ⟨n, bodyOf refunds⟩` where `n` is the number of applied
//! receipts (`appliedReceipts`, `ChunkValidationV0a.lean`) and `refunds` are the
//! gas refunds the main (B2) transition generates.  Ported here, byte for byte:
//!
//! | Rust | Lean |
//! |---|---|
//! | [`decode_w`] | `decodeW` = `decodeWitnessFile` + `decodeStateWitness` (`WitnessV3.lean`) |
//! | `p_receipt` | `pReceipt` (`Wire.lean`, D0 receipt shape) |
//! | [`applied_receipts`] | `appliedReceipts` (`lookupLast`, `shuffleWithSeed … |>.getD`) |
//! | [`partial_trie`] | `partialTrie` = `buildFor (mkStore values) trieFuel` (`TrieBuild.lean`) |
//! | [`find`] / [`get`] / `set_in_place` | `PTrie.find` (`TrieUpsert.lean`), `PTrie.get` / `PTrie.set` (`Trie.lean`) |
//! | [`buffered_shards`] / [`main_keys`] | `bufferedShards` / `mainKeys` (`RuntimeD0.lean`) |
//! | `apply_receipt` | `TransferV1.applyReceipt` (only `trie`, `refunds`, `tokensBurnt` are kept) |
//! | `apply_system_receipt` | `RuntimeD0.applySystemReceipt` (`.ok`/`.error` and the trie) |
//! | [`refunds_up_to`] | `refundsUpTo` |
//! | [`hint_of_e`] / [`hint_of`] | `hintOfE` / `hintOf` |
//!
//! **The `applyNewChunk` branch.**  `hintOfE` takes `out.outgoing` when
//! `applyNewChunk prims ctxB2 tMain receipts` succeeds and
//! `refundsUpTo ctxB2 ⟨tMain, …⟩ receipts` otherwise.  Both are the refunds of
//! applying the receipts in order up to the first failing one, with the same
//! per-receipt functions; they differ only in the trie the receipts run on:
//! `applyNewChunk` first upserts the scheduler state at `keyBwState = [0, 15]`.
//! The receipts read and write only `accountKeyPath id = [0, 0, …]` and
//! `keyAccessKey = [0, 2, …]`, never `[0, 15]`; `PTrie.get k = (find k).join`
//! and `set k` succeeds iff `find k = some (some _)` (both by the definitions),
//! and `PTrie.find_upsert_other` (`NearSpec.TrieUpsertProofs`, proved for
//! well-formed tries) says the upsert leaves `find` on every other key
//! unchanged.  So the refund list is `refundsUpTo ctxB2 ⟨tMain, …⟩ receipts` in
//! both branches, and that is what [`hint_of_e`] computes (this avoids running
//! the full bandwidth scheduler `runCore`, which only decides the branch).  The
//! argument is not mechanised; the differential (`conformance/run-v2.sh`,
//! `np-lean-prep-v3`) compares the hint bytes with Lean's `hintOf`.

use std::collections::HashMap;

use crate::near::reexec::sha256;
use crate::near::reexec::spec::is_named;
use crate::near::reexec::wire::Reader;
use crate::near::spec::{
    self as ns, Account, Bytes, PTrie, Receipt, Slot, account_key_path, gas_refund_receipt,
    nibbles, params, u64b,
};
use crate::v3::d0::{
    ChunkInner, Walk, block_ctx, chunk_hash, d_tag, mapw, p_account_id, p_chunk_inner,
    p_public_key, p_signature, shuffle_with_seed, walk_d0,
};
use crate::v3::prep::{Hint, body_of};

fn err<T>(m: impl Into<String>) -> Result<T, String> {
    Err(m.into())
}

// ---------------------------------------------------------------------------
// `witness.bin` (`WitnessV3.lean`)
// ---------------------------------------------------------------------------

/// `"near-arena-witness-v3"` (`ClaimV3.witnessTag`).
const WITNESS_TAG: &[u8] = b"near-arena-witness-v3";
/// `MAX_WITNESS` (64 MiB).
const MAX_WITNESS: usize = 67_108_864;

/// `Transition`.
#[derive(Clone, Debug)]
pub struct Transition {
    pub block_hash: Bytes,
    pub values: Vec<Bytes>,
    pub post_state_root: Bytes,
}

/// `ShardProof` + `ProofEntry`.
#[derive(Clone, Debug)]
pub struct ProofEntry {
    pub key: Bytes,
    pub receipts: Vec<Receipt>,
    pub from_shard: u64,
    pub to_shard: u64,
    pub path: Vec<(Bytes, u8)>,
}

/// `StateWitness`.
#[derive(Clone, Debug)]
pub struct StateWitness {
    pub epoch_id: Bytes,
    pub inner_bytes: Bytes,
    pub inner: ChunkInner,
    pub main: Transition,
    pub entries: Vec<ProofEntry>,
    pub applied_receipts_hash: Bytes,
    pub implicit: Vec<Transition>,
}

/// `pReceipt`: nearcore borsh `Receipt` restricted to the D0 shape.
fn p_receipt(r: &mut Reader) -> Result<Receipt, String> {
    let predecessor_id = p_account_id(r, "predecessor_id")?;
    let receiver_id = p_account_id(r, "receiver_id")?;
    let receipt_id = mapw(r.hash("receipt_id"))?.to_vec();
    if mapw(r.u8("ReceiptEnum tag"))? != 0 {
        return err("out of domain (r.shape): ReceiptEnum is not Action(0)");
    }
    let signer_id = p_account_id(r, "signer_id")?;
    let signer_pk = p_public_key(r, "signer_public_key")?;
    if signer_pk.tag == 2 {
        return err("out of domain (r.shape): ML-DSA signer key");
    }
    let gas_price = mapw(r.u128("gas_price"))?;
    if mapw(r.u32("output_data_receivers"))? != 0 {
        return err("out of domain (r.shape): output_data_receivers");
    }
    if mapw(r.u32("input_data_ids"))? != 0 {
        return err("out of domain (r.shape): input_data_ids");
    }
    if mapw(r.u32("actions"))? != 1 {
        return err("out of domain (r.shape): not exactly one action");
    }
    if mapw(r.u8("action tag"))? != 3 {
        return err("out of domain (r.shape): action is not Transfer(3)");
    }
    let deposit = mapw(r.u128("deposit"))?;
    if !is_named(&receiver_id) {
        return err("out of domain (r.shape): receiver is not a named account");
    }
    Ok(Receipt {
        predecessor_id,
        receiver_id,
        receipt_id,
        signer_id,
        signer_pk,
        gas_price,
        deposit,
    })
}

/// `pVec w p`: `u32` count, then `count` items (fails on truncation).
fn p_vec<T>(
    r: &mut Reader,
    what: &'static str,
    mut p: impl FnMut(&mut Reader) -> Result<T, String>,
) -> Result<Vec<T>, String> {
    let n = mapw(r.u32(what))? as usize;
    let mut out = Vec::with_capacity(n.min(1 << 12));
    for _ in 0..n {
        out.push(p(r)?);
    }
    Ok(out)
}

/// `pTransition`.
fn p_transition(r: &mut Reader) -> Result<Transition, String> {
    let block_hash = mapw(r.hash("transition block_hash"))?.to_vec();
    if mapw(r.u8("PartialState tag"))? != 0 {
        return err("decode: PartialState tag");
    }
    let values = p_vec(r, "trie values length", |r| {
        Ok(mapw(r.bytes("trie value"))?.to_vec())
    })?;
    let post_state_root = mapw(r.hash("post_state_root"))?.to_vec();
    Ok(Transition {
        block_hash,
        values,
        post_state_root,
    })
}

/// `pPathItem`.
fn p_path_item(r: &mut Reader) -> Result<(Bytes, u8), String> {
    let h = mapw(r.hash("path hash"))?.to_vec();
    let d = mapw(r.u8("path direction"))?;
    if d > 1 {
        return err("decode: MerklePathItem direction");
    }
    Ok((h, d))
}

/// `pEntry`.
fn p_entry(r: &mut Reader) -> Result<ProofEntry, String> {
    let key = mapw(r.hash("ChunkHash"))?.to_vec();
    let receipts = p_vec(r, "proof receipts length", p_receipt)?;
    let from_shard = mapw(r.u64("from_shard_id"))?;
    let to_shard = mapw(r.u64("to_shard_id"))?;
    let path = p_vec(r, "merkle path length", p_path_item)?;
    Ok(ProofEntry {
        key,
        receipts,
        from_shard,
        to_shard,
        path,
    })
}

/// `decodeStateWitness`.
pub fn decode_state_witness(bs: &[u8]) -> Result<StateWitness, String> {
    if bs.len() > MAX_WITNESS {
        return err("decode: witness larger than 64 MiB");
    }
    let mut r = Reader::new(bs);
    if mapw(r.u8("ChunkStateWitness tag"))? != 1 {
        return err("decode: ChunkStateWitness tag");
    }
    let epoch_id = mapw(r.hash("epoch_id"))?.to_vec();
    // `pChunkHeader`: tag 2 ‖ tagged inner ‖ height_included ‖ signature
    if mapw(r.u8("ShardChunkHeader tag"))? != 2 {
        return err("invalid: ShardChunkHeader is not V3");
    }
    let start = r.pos;
    let inner = p_chunk_inner(&mut r)?;
    let inner_bytes = bs[start..r.pos].to_vec();
    mapw(r.u64("height_included"))?;
    p_signature(&mut r, "chunk signature")?;
    let main = p_transition(&mut r)?;
    let entries = p_vec(&mut r, "source_receipt_proofs length", p_entry)?;
    let applied_receipts_hash = mapw(r.hash("applied_receipts_hash"))?.to_vec();
    if mapw(r.u32("transactions"))? != 0 {
        return err("out of domain (w.no_txs): transactions");
    }
    let implicit = p_vec(&mut r, "implicit_transitions length", p_transition)?;
    if mapw(r.u32("new_transactions"))? != 0 {
        return err("out of domain (w.no_txs): new_transactions");
    }
    if !r.is_empty() {
        return err("decode: Not all bytes read");
    }
    Ok(StateWitness {
        epoch_id,
        inner_bytes,
        inner,
        main,
        entries,
        applied_receipts_hash,
        implicit,
    })
}

/// `decodeWitnessFile`: `witness.bin` → (state witness bytes, contract codes).
pub fn decode_witness_file(bs: &[u8]) -> Result<(Bytes, Vec<Bytes>), String> {
    let mut r = Reader::new(bs);
    d_tag(&mut r, WITNESS_TAG, "witness format")?;
    let sw = mapw(r.bytes("state_witness"))?.to_vec();
    let codes = p_vec(&mut r, "contract_code length", |r| {
        Ok(mapw(r.bytes("code"))?.to_vec())
    })?;
    if !r.is_empty() {
        return err("decode: trailing bytes in witness.bin");
    }
    Ok((sw, codes))
}

/// `decodeW`.
pub fn decode_w(wb: &[u8]) -> Result<StateWitness, String> {
    let (sw, _) = decode_witness_file(wb)?;
    decode_state_witness(&sw)
}

/// `lookupLast k es`: the last entry with key `k` (borsh `HashMap` last-wins).
pub(crate) fn lookup_last<'a>(k: &[u8], es: &'a [ProofEntry]) -> Option<&'a ProofEntry> {
    es.iter().rev().find(|e| e.key == k)
}

/// `appliedReceipts k w`: the applied receipts as `checkD0` builds them
/// (lenient: missing proofs are skipped; a failed shuffle keeps the order).
pub fn applied_receipts(k: &Walk, w: &StateWitness) -> Vec<Receipt> {
    let mut receipts = Vec::new();
    for s_blk in &k.source_blks {
        let proofs: Vec<&ProofEntry> = s_blk
            .slots
            .iter()
            .enumerate()
            .filter(|(_, (hi, _))| *hi == s_blk.hdr.height)
            .filter_map(|(i, (_, ci))| {
                lookup_last(
                    &chunk_hash(&s_blk.slot_inner[i], &ci.encoded_merkle_root),
                    &w.entries,
                )
            })
            .collect();
        let mut shuffled = proofs.clone();
        if !shuffle_with_seed(&mut shuffled, &s_blk.hdr.prev_hash) {
            shuffled = proofs;
        }
        for e in shuffled {
            receipts.extend(
                e.receipts
                    .iter()
                    .filter(|r| k.layout.shard_of(&r.receiver_id) == k.h_chunk.shard_id)
                    .cloned(),
            );
        }
    }
    receipts
}

// ---------------------------------------------------------------------------
// Partial tries from recorded storage (`TrieBuild.lean`)
// ---------------------------------------------------------------------------

/// `trieFuel`.
const TRIE_FUEL: usize = 400;

/// `mkStore` with `storeGet`'s first-match lookup.
struct Store<'a> {
    m: HashMap<[u8; 32], &'a [u8]>,
}

impl<'a> Store<'a> {
    fn new(values: &'a [Bytes]) -> Store<'a> {
        let mut m = HashMap::with_capacity(values.len());
        for v in values {
            m.entry(sha256(v)).or_insert(v.as_slice());
        }
        Store { m }
    }
    /// `storeGet s h` (`h` of any length; only 32-byte keys can match).
    fn get(&self, h: &[u8]) -> Option<&'a [u8]> {
        let k: [u8; 32] = h.try_into().ok()?;
        self.m.get(&k).copied()
    }
}

/// `List.take` (saturating).
fn take(b: &[u8], n: usize) -> &[u8] {
    &b[..n.min(b.len())]
}
/// `List.drop` (saturating).
fn drop(b: &[u8], n: usize) -> &[u8] {
    &b[n.min(b.len())..]
}
/// `leNat` (little-endian; at most 16 significant bytes are used here).
fn le_nat(b: &[u8]) -> u128 {
    ns::le_nat(b)
}

/// `hpDecode`.
fn hp_decode(b: &[u8]) -> Option<(Vec<u8>, bool)> {
    let (&f, rest) = b.split_first()?;
    let hi = f / 16;
    let odd = hi % 2 == 1;
    let leaf = (hi / 2) % 2 == 1;
    if hi > 3 || (!odd && f % 16 != 0) {
        return None;
    }
    let mut k = if odd { vec![f % 16] } else { vec![] };
    k.extend(nibbles(rest));
    Some((k, leaf))
}

/// `mkSlot s len vh want`.
fn mk_slot(s: &Store, len: u128, vh: &[u8], want: bool) -> Slot {
    match if want { s.get(vh) } else { None } {
        Some(v) if v.len() as u128 == len => Slot::Val(v.to_vec()),
        _ => Slot::Ref(len, vh.to_vec()),
    }
}

/// `branchWith (buildFor s fuel) h v rest keys mem`.
fn branch_with(
    s: &Store,
    fuel: usize,
    h: &[u8],
    v: Option<Slot>,
    rest: &[u8],
    keys: &[Vec<u8>],
    mem: u128,
) -> PTrie {
    let bm = le_nat(take(rest, 2));
    // `kidHashes 16 bm (rest.drop 2)`
    let mut hs: Vec<Option<&[u8]>> = Vec::with_capacity(16);
    let mut bs = drop(rest, 2);
    let mut b = bm;
    for _ in 0..16 {
        if b % 2 == 1 {
            hs.push(Some(take(bs, 32)));
            bs = drop(bs, 32);
        } else {
            hs.push(None);
        }
        b /= 2;
    }
    let nkids = hs.iter().filter(|x| x.is_some()).count();
    if rest.len() != 2 + 32 * nkids {
        return PTrie::Hash(h.to_vec());
    }
    // `buildKidsWith f 0 hs keys`
    let kids = hs
        .iter()
        .enumerate()
        .map(|(i, ch)| {
            ch.map(|ch| {
                let ks: Vec<Vec<u8>> = keys
                    .iter()
                    .filter(|k| k.first() == Some(&(i as u8)))
                    .map(|k| k[1..].to_vec())
                    .collect();
                build_for(s, fuel, ch, &ks)
            })
        })
        .collect();
    PTrie::Branch(v, kids, mem)
}

/// `buildFor s fuel h keys`.
fn build_for(s: &Store, fuel: usize, h: &[u8], keys: &[Vec<u8>]) -> PTrie {
    let hash = || PTrie::Hash(h.to_vec());
    if fuel == 0 || keys.is_empty() {
        return hash();
    }
    let fuel = fuel - 1;
    let Some(node) = s.get(h) else {
        return hash();
    };
    if node.len() < 9 {
        return hash();
    }
    let mem = le_nat(&node[node.len() - 8..]);
    let body = &node[..node.len() - 8];
    let rest = &body[1..];
    match body[0] {
        0 => {
            let klen = le_nat(take(rest, 4)) as usize;
            match hp_decode(take(drop(rest, 4), klen)) {
                Some((k, true)) => {
                    let r2 = drop(rest, 4usize.saturating_add(klen));
                    if r2.len() != 36 {
                        return hash();
                    }
                    let want = keys.contains(&k);
                    let slot = mk_slot(s, le_nat(take(r2, 4)), drop(r2, 4), want);
                    PTrie::Leaf(k, slot, mem)
                }
                _ => hash(),
            }
        }
        3 => {
            let klen = le_nat(take(rest, 4)) as usize;
            match hp_decode(take(drop(rest, 4), klen)) {
                Some((k, false)) => {
                    let child = drop(rest, 4usize.saturating_add(klen));
                    if child.len() != 32 {
                        return hash();
                    }
                    let keys2: Vec<Vec<u8>> = keys
                        .iter()
                        .filter(|x| x.starts_with(&k))
                        .map(|x| x[k.len()..].to_vec())
                        .collect();
                    PTrie::Ext(k, Box::new(build_for(s, fuel, child, &keys2)), mem)
                }
                _ => hash(),
            }
        }
        1 => branch_with(s, fuel, h, None, rest, keys, mem),
        2 => {
            if rest.len() < 36 {
                return hash();
            }
            let want = keys.iter().any(|x| x.is_empty());
            let slot = mk_slot(s, le_nat(take(rest, 4)), take(drop(rest, 4), 32), want);
            branch_with(s, fuel, h, Some(slot), drop(rest, 36), keys, mem)
        }
        _ => hash(),
    }
}

/// `partialTrie values root keys`.
pub fn partial_trie(values: &[Bytes], root: &[u8], keys: &[Vec<u8>]) -> PTrie {
    build_for(&Store::new(values), TRIE_FUEL, root, keys)
}

// ---------------------------------------------------------------------------
// Lookup and in-place update (`PTrie.find`, `PTrie.get`, `PTrie.set`)
// ---------------------------------------------------------------------------

/// `PTrie.find`: `None` = undetermined, `Some(None)` = proven absent.
pub fn find(t: &PTrie, key: &[u8]) -> Option<Option<Bytes>> {
    match t {
        PTrie::Hash(_) => None,
        PTrie::Leaf(k, v, _) => {
            if k.as_slice() == key {
                v.get().map(|x| Some(x.clone()))
            } else {
                Some(None)
            }
        }
        PTrie::Ext(k, c, _) => {
            if key.starts_with(k) {
                find(c, &key[k.len()..])
            } else {
                Some(None)
            }
        }
        PTrie::Branch(v, cs, _) => match key.split_first() {
            None => match v {
                None => Some(None),
                Some(s) => s.get().map(|x| Some(x.clone())),
            },
            Some((&n, rest)) => match cs.get(n as usize) {
                None | Some(None) => Some(None),
                Some(Some(c)) => find(c, rest),
            },
        },
    }
}

/// `PTrie.get` (= `(find key).join`).
pub fn get(t: &PTrie, key: &[u8]) -> Option<Bytes> {
    match t {
        PTrie::Hash(_) => None,
        PTrie::Leaf(k, v, _) => {
            if k.as_slice() == key {
                v.get().cloned()
            } else {
                None
            }
        }
        PTrie::Ext(k, c, _) => {
            if key.starts_with(k) {
                get(c, &key[k.len()..])
            } else {
                None
            }
        }
        PTrie::Branch(v, cs, _) => match key.split_first() {
            None => v.as_ref().and_then(|s| s.get().cloned()),
            Some((&n, rest)) => match cs.get(n as usize) {
                Some(Some(c)) => get(c, rest),
                _ => None,
            },
        },
    }
}

/// `PTrie.set t key nv`, in place: `true` iff Lean's `set` is `some t'`, and
/// then `*t = t'`.  On `false` the trie is unchanged (the value slot is only
/// written once the whole path has been matched).
pub(crate) fn set_in_place(t: &mut PTrie, key: &[u8], nv: &[u8]) -> bool {
    match t {
        PTrie::Hash(_) => false,
        PTrie::Leaf(k, v, _) => {
            if k.as_slice() == key && v.get().is_some() {
                *v = Slot::Val(nv.to_vec());
                true
            } else {
                false
            }
        }
        PTrie::Ext(k, c, _) => {
            if key.starts_with(k) {
                let n = k.len();
                set_in_place(c, &key[n..], nv)
            } else {
                false
            }
        }
        PTrie::Branch(v, cs, _) => match key.split_first() {
            None => match v {
                Some(Slot::Val(_)) => {
                    *v = Some(Slot::Val(nv.to_vec()));
                    true
                }
                _ => false,
            },
            Some((&n, rest)) => match cs.get_mut(n as usize) {
                Some(Some(c)) => set_in_place(c, rest, nv),
                _ => false,
            },
        },
    }
}

// ---------------------------------------------------------------------------
// D0 main-transition keys and receipt application (`RuntimeD0.lean`)
// ---------------------------------------------------------------------------

fn key1(b: u8) -> Vec<u8> {
    nibbles(&[b])
}
/// `keyDelayedIdx`.
pub fn key_delayed_idx() -> Vec<u8> {
    key1(7)
}
/// `keyBwState`.
pub fn key_bw_state() -> Vec<u8> {
    key1(15)
}
/// `keyBufferedIdx`.
pub fn key_buffered_idx() -> Vec<u8> {
    key1(13)
}
/// `keyYieldIdx`.
pub fn key_yield_idx() -> Vec<u8> {
    key1(10)
}
/// `keyGroupsData s = nibbles ([16] ++ u64 s)`.
pub fn key_groups_data(s: u64) -> Vec<u8> {
    let mut b = vec![16u8];
    b.extend(u64b(s as u128));
    nibbles(&b)
}
/// `keyAccessKey acct pk = nibbles ([2] ++ acct ++ [2] ++ pk.encode)`.
pub fn key_access_key(acct: &[u8], pk: &ns::PublicKey) -> Vec<u8> {
    let mut b = vec![2u8];
    b.extend_from_slice(acct);
    b.push(2);
    b.extend(pk.encode());
    nibbles(&b)
}

/// `bufferedShards v`: the shard ids of `BufferedReceiptIndices`; every queue
/// must be empty.
pub fn buffered_shards(v: Option<&[u8]>) -> Result<Vec<u64>, String> {
    let Some(b) = v else {
        return Ok(vec![]);
    };
    let mut r = Reader::new(b);
    let es = p_vec(&mut r, "shard_buffers length", |r| {
        let s = mapw(r.u64("shard"))?;
        let f = mapw(r.u64("first"))?;
        let n = mapw(r.u64("next"))?;
        Ok((s, f, n))
    })?;
    if !r.is_empty() {
        return err("invalid: StorageInconsistentState (BufferedReceiptIndices)");
    }
    if es.iter().any(|e| e.1 != e.2) {
        return err("out of domain (e.queues_empty): outgoing buffer not empty");
    }
    Ok(es.into_iter().map(|e| e.0).collect())
}

/// `mainKeys receipts bufferedShardIds`.
pub fn main_keys(receipts: &[Receipt], bshards: &[u64]) -> Vec<Vec<u8>> {
    let mut ks = vec![
        key_delayed_idx(),
        key_bw_state(),
        key_buffered_idx(),
        key_yield_idx(),
    ];
    ks.extend(bshards.iter().map(|&s| key_groups_data(s)));
    ks.extend(receipts.iter().map(|r| account_key_path(&r.receiver_id)));
    ks.extend(
        receipts
            .iter()
            .filter(|r| r.predecessor_id == ns::SYSTEM && r.signer_id == r.receiver_id)
            .map(|r| key_access_key(&r.receiver_id, &r.signer_pk)),
    );
    ks
}

/// The part of `TransferV1.Acc` the refund list depends on.
pub(crate) struct Acc {
    pub(crate) trie: PTrie,
    pub(crate) refunds: Vec<Receipt>,
    pub(crate) tokens_burnt: u128,
}

/// `amount' = a.amount + deposit` with the `action_transfer` and
/// `check_storage_stake` conditions shared by `applyReceipt` and
/// `applySystemReceipt` (`Nat` arithmetic; `None` = the receipt fails).
fn credited(a: &Account, deposit: u128) -> Option<u128> {
    // `amount' ≥ u128Max` (an overflow of `u128` is `≥ 2^128`)
    let amount = a.amount.checked_add(deposit)?;
    // (`u128Max = 2^128 - 1`, so within `u128` this is equality)
    if amount == params::U128_MAX {
        return None;
    }
    // `amount' + locked ≥ 2^128`
    let total = amount.checked_add(a.locked)?;
    // `amount' + locked ≥ storageAmountPerByte · storageUsage ∨ storageUsage ≤ 770`
    let covered = match params::STORAGE_AMOUNT_PER_BYTE.checked_mul(a.storage_usage) {
        Some(need) => total >= need,
        None => false,
    };
    if !(covered || a.storage_usage <= params::ZERO_BALANCE_STORAGE_LIMIT) {
        return None;
    }
    Some(amount)
}

/// `TransferV1.applyReceipt ⟨height, gasPrice⟩ st r` (`false` = `none`).
pub(crate) fn apply_receipt(height: u64, gas_price: u128, st: &mut Acc, r: &Receipt) -> bool {
    let key = account_key_path(&r.receiver_id);
    let Some(raw) = get(&st.trie, &key) else {
        return false;
    };
    let Some(a) = Account::decode(&raw) else {
        return false;
    };
    let Some(amount) = credited(&a, r.deposit) else {
        return false;
    };
    let p = r.gas_price.min(gas_price);
    let (Some(burnt), Some(surplus)) = (
        params::G.checked_mul(p),
        params::G.checked_mul(r.gas_price - p),
    ) else {
        return false;
    };
    let Some(tokens) = st.tokens_burnt.checked_add(burnt) else {
        return false;
    };
    let a2 = Account { amount, ..a };
    if !set_in_place(&mut st.trie, &key, &a2.encode()) {
        return false;
    }
    if surplus != 0 {
        st.refunds
            .push(gas_refund_receipt(r, height as u128, surplus));
    }
    st.tokens_burnt = tokens;
    true
}

/// `RuntimeD0.applySystemReceipt st r` (`false` = `.error _`).
pub(crate) fn apply_system_receipt(st: &mut Acc, r: &Receipt) -> bool {
    let key = account_key_path(&r.receiver_id);
    let raw = match find(&st.trie, &key) {
        Some(Some(v)) => v,
        _ => return false,
    };
    let Some(a) = Account::decode(&raw) else {
        return false;
    };
    let Some(amount) = credited(&a, r.deposit) else {
        return false;
    };
    if r.signer_id == r.receiver_id {
        match find(&st.trie, &key_access_key(&r.receiver_id, &r.signer_pk)) {
            None => return false,
            Some(None) => {}
            Some(Some(ak)) => {
                // `AccessKey { nonce: u64, permission }`; FullAccess = tag 1
                if !(ak.len() == 9 && ak[8] == 1) {
                    return false;
                }
            }
        }
    }
    let a2 = Account { amount, ..a };
    set_in_place(&mut st.trie, &key, &a2.encode())
}

/// `refundsUpTo ctx ⟨t, [], [], 0, 0⟩ rs`: the refunds generated by applying
/// `rs` in order, up to the first failing receipt.
pub fn refunds_up_to(height: u64, gas_price: u128, t: PTrie, rs: &[Receipt]) -> Vec<Receipt> {
    let mut acc = Acc {
        trie: t,
        refunds: vec![],
        tokens_burnt: 0,
    };
    for r in rs {
        let ok = if r.predecessor_id == ns::SYSTEM {
            apply_system_receipt(&mut acc, r)
        } else {
            apply_receipt(height, gas_price, &mut acc, r)
        };
        if !ok {
            break;
        }
    }
    acc.refunds
}

// ---------------------------------------------------------------------------
// `hintOf`
// ---------------------------------------------------------------------------

/// The applied receipts and the refund list of the main transition (the two
/// inputs of the hint).
pub struct MainRun {
    pub receipts: Vec<Receipt>,
    pub refunds: Vec<Receipt>,
}

/// `hintOfE` up to the hint: walk, decode, applied receipts, the partial
/// main pre-trie and the refunds (see the module docs for the
/// `applyNewChunk` branch).
pub fn main_run(cb: &[u8], wb: &[u8]) -> Result<MainRun, String> {
    let k = walk_d0(cb)?;
    let w = decode_w(wb)?;
    let b2 = k.blks.get(k.b2i).ok_or("walk")?;
    let prev_b2 = k.blks.get(k.b2i + 1).ok_or("walk")?;
    let receipts = applied_receipts(&k, &w);
    let ctx_b2 = block_ctx(
        &k.layout,
        k.h_chunk.shard_id,
        k.slot_b2.gas_limit,
        b2,
        prev_b2.hdr.next_gas_price,
    );
    let root = &k.slot_b2.prev_state_root;
    let t0 = partial_trie(&w.main.values, root, &[key_buffered_idx()]);
    let bv = find(&t0, &key_buffered_idx()).flatten();
    let bshards = buffered_shards(bv.as_deref()).unwrap_or_default();
    let t_main = partial_trie(&w.main.values, root, &main_keys(&receipts, &bshards));
    let refunds = refunds_up_to(ctx_b2.height, ctx_b2.gas_price, t_main, &receipts);
    Ok(MainRun { receipts, refunds })
}

/// `hintOfE cb w`.
pub fn hint_of_e(cb: &[u8], wb: &[u8]) -> Result<Hint, String> {
    let m = main_run(cb, wb)?;
    Ok(Hint {
        n: m.receipts.len() as u64,
        body: body_of(&m.refunds),
    })
}

/// `hintOf cb w` (`Hint.empty` if the pair does not decode).
pub fn hint_of(cb: &[u8], wb: &[u8]) -> Hint {
    hint_of_e(cb, wb).unwrap_or_else(|_| Hint::empty())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf_node(key_nibs: &[u8], v: &[u8], mem: u64) -> Bytes {
        let hp = ns::hex_prefix(key_nibs, true);
        let mut b = vec![0u8];
        b.extend(ns::u32b(hp.len() as u128));
        b.extend(&hp);
        b.extend(ns::u32b(v.len() as u128));
        b.extend(sha256(v));
        b.extend(u64b(mem as u128));
        b
    }

    #[test]
    fn leaf_root_find_get_set() {
        let key = account_key_path(b"alice.near");
        let v = vec![7u8; 72];
        let node = leaf_node(&key, &v, 123);
        let root = sha256(&node).to_vec();
        let vals = vec![node.clone(), v.clone()];
        let t = partial_trie(&vals, &root, std::slice::from_ref(&key));
        assert_eq!(t.hash_of(), root);
        assert_eq!(find(&t, &key), Some(Some(v.clone())));
        assert_eq!(get(&t, &key), Some(v.clone()));
        assert_eq!(find(&t, &key_bw_state()), Some(None));
        // unwanted key: the value stays a `ref`, so `find` is undetermined
        let t2 = partial_trie(&vals, &root, &[key_bw_state()]);
        assert_eq!(find(&t2, &key), None);
        // missing node: undetermined
        let t3 = partial_trie(&[], &root, std::slice::from_ref(&key));
        assert_eq!(find(&t3, &key), None);
        let mut t4 = t.clone();
        assert!(set_in_place(&mut t4, &key, &[1u8; 72]));
        assert_eq!(get(&t4, &key), Some(vec![1u8; 72]));
        let mut t5 = t.clone();
        assert!(!set_in_place(&mut t5, &key_bw_state(), &[1u8; 72]));
        assert_eq!(t5, t);
    }

    #[test]
    fn buffered_shards_codec() {
        assert_eq!(buffered_shards(None), Ok(vec![]));
        let mut b = ns::u32b(1);
        b.extend(u64b(3));
        b.extend(u64b(5));
        b.extend(u64b(5));
        assert_eq!(buffered_shards(Some(&b)), Ok(vec![3]));
        let mut nb = b.clone();
        nb.truncate(nb.len() - 8);
        nb.extend(u64b(6));
        assert!(buffered_shards(Some(&nb)).is_err());
        b.push(0);
        assert!(buffered_shards(Some(&b)).is_err());
    }

    #[test]
    fn hint_of_garbage_is_empty() {
        assert_eq!(hint_of(b"", b""), Hint::empty());
    }
}
