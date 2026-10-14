//! The native D1 run of an accepted D1a witness: `checkD1`'s main transition
//! (`applyNewChunkD1`: `processTxs`, local receipts, incoming receipts; RuntimeD1.lean) with
//! everything the D1 tables and the D1 prepared statement need: the `txV3` ops (in time
//! order), the transaction walks, the outcome leaves `0 … M0 − 1`, the local receipt ids,
//! the offsets `M0`, `T0`, `O0`, `TOK0`, the memory timeline, and the trie-side `Native`
//! (AIR pre trie over the *read* keys, writes, scheduler upserts, implicit steps).

use std::collections::HashMap;

use crate::near::reexec::sha256;
use crate::near::reexec::wire::Reader;
use crate::near::spec::{
    self as ns, Account, Bytes, PTrie, PublicKey, Receipt, account_key_path, params,
    receipt_id_from,
};
use crate::v3::d0::{ApplyCtx, Walk, block_ctx, mapw, p_chunk_inner, p_signature, walk_d0};
use crate::v3::hint::{
    Acc, ProofEntry, StateWitness, Transition, applied_receipts, apply_receipt,
    apply_system_receipt, buffered_shards, decode_witness_file, find, get, key_access_key,
    key_buffered_idx, key_bw_state, key_delayed_idx, main_keys, p_entry, p_transition, p_vec,
    partial_trie, set_in_place,
};
use crate::v3::native::{self, Native, Step};
use crate::v3::walks::Query;

use super::tx::{self, Perm, Tx};

/// `W_TX` (`ZkFormal.NearV3.D1.Ids`).
pub const W_TX: u64 = 1 << 20;
/// `W_LOC`.
pub const W_LOC: u64 = 1 << 20;
/// `K_PLF`.
pub const K_PLF: u64 = 15;

fn err<T>(m: impl Into<String>) -> Result<T, String> {
    Err(m.into())
}

/// `StateWitnessD1`.
pub struct StateWitnessD1 {
    pub base: StateWitness,
    pub txs: Vec<Tx>,
    pub new_txs: Vec<Tx>,
}

fn p_txs(r: &mut Reader, bs: &[u8], what: &'static str) -> Result<Vec<Tx>, String> {
    let n = mapw(r.u32(what))? as usize;
    let mut out = Vec::with_capacity(n.min(1 << 12));
    for _ in 0..n {
        out.push(tx::p_tx_d1(r, bs)?);
    }
    Ok(out)
}

/// `decodeStateWitnessD1`.
pub fn decode_state_witness_d1(bs: &[u8]) -> Result<StateWitnessD1, String> {
    if bs.len() > 67_108_864 {
        return err("decode: witness larger than 64 MiB");
    }
    let mut r = Reader::new(bs);
    if mapw(r.u8("ChunkStateWitness tag"))? != 1 {
        return err("decode: ChunkStateWitness tag");
    }
    let epoch_id = mapw(r.hash("epoch_id"))?.to_vec();
    if mapw(r.u8("ShardChunkHeader tag"))? != 2 {
        return err("invalid: ShardChunkHeader is not V3");
    }
    let start = r.pos;
    let inner = p_chunk_inner(&mut r)?;
    let inner_bytes = bs[start..r.pos].to_vec();
    mapw(r.u64("height_included"))?;
    p_signature(&mut r, "chunk signature")?;
    let main = p_transition(&mut r)?;
    let entries: Vec<ProofEntry> = p_vec(&mut r, "source_receipt_proofs length", p_entry)?;
    let applied_receipts_hash = mapw(r.hash("applied_receipts_hash"))?.to_vec();
    let txs = p_txs(&mut r, bs, "transactions")?;
    let implicit: Vec<Transition> = p_vec(&mut r, "implicit_transitions length", p_transition)?;
    let new_txs = p_txs(&mut r, bs, "new_transactions")?;
    if !r.is_empty() {
        return err("decode: Not all bytes read");
    }
    Ok(StateWitnessD1 {
        base: StateWitness {
            epoch_id,
            inner_bytes,
            inner,
            main,
            entries,
            applied_receipts_hash,
            implicit,
        },
        txs,
        new_txs,
    })
}

/// `decodeWD1`.
pub fn decode_w_d1(wb: &[u8]) -> Result<StateWitnessD1, String> {
    let (sw, _) = decode_witness_file(wb)?;
    decode_state_witness_d1(&sw)
}

/// One `txV3` op (public fields and the memory values it reads).
#[derive(Clone, Debug, Default)]
pub struct OpN {
    /// `0` debit, `1` credit
    pub kind: u8,
    pub strict: bool,
    pub ok: bool,
    pub tov: bool,
    pub stage: u8,
    pub cok: bool,
    pub valid: bool,
    pub nonce: u64,
    pub bound: u128,
    pub amount: u128,
    pub signer: Bytes,
    pub pk: PublicKey,
    /// the account read (stage ≥ 1) and its previous access time
    pub acct: Option<Account>,
    pub tp_a: u64,
    /// the access key's nonce and FullAccess flag (stage 2) and its previous access time
    pub kn: u64,
    pub fa: bool,
    pub tp_k: u64,
    /// value record ids in the AIR pre trie (filled after the trie is built)
    pub vid_a: u64,
    pub vid_k: u64,
}

impl OpN {
    /// `gW`: the op has a signer walk.
    pub fn g_w(&self) -> bool {
        self.kind == 1 || (self.valid && self.cok)
    }
    /// `gK`: the op has an access-key walk.
    pub fn g_k(&self) -> bool {
        self.kind == 0 && self.stage >= 1
    }
    /// `wr`: the op writes.
    pub fn wr(&self) -> bool {
        self.kind == 1 || (self.ok && !self.tov)
    }
}

/// An access-key value read by a transaction (an `akmV3` segment).
#[derive(Clone, Debug)]
pub struct AkmSeg {
    pub vid: u64,
    pub key: Vec<u8>,
    pub bytes: Bytes,
    pub tlast: u64,
    /// final nonce bytes (`pb`)
    pub post: Bytes,
    /// gas-refund uses (`AKC` count)
    pub u: u64,
}

/// The native D1 run.
pub struct D1Run {
    pub k: Walk,
    pub ctx: ApplyCtx,
    pub w: StateWitnessD1,
    pub receipts: Vec<Receipt>,
    pub bshards: Vec<u64>,
    pub ops: Vec<OpN>,
    /// transaction walks `(w, trie key as bytes)`
    pub walks: Vec<(u64, Bytes)>,
    /// outcome leaf preimages `0 … M0 − 1`
    pub leaf_pre: Vec<Bytes>,
    /// all outcome leaf preimages (transactions, local, incoming)
    pub all_leaf_pre: Vec<Bytes>,
    pub local_ids: Vec<Bytes>,
    pub locals: Vec<Receipt>,
    pub m0: u64,
    pub t0: u64,
    pub o0: u64,
    pub tok0: u128,
    pub fwd: Vec<Receipt>,
    pub local_refunds: Vec<Receipt>,
    pub refunds: Vec<Receipt>,
    pub gas_used: u128,
    pub tokens: u128,
    /// the AIR pre trie (main keys and the read transaction keys)
    pub pre: PTrie,
    /// the trie after all receipts (no scheduler write)
    pub post_main: PTrie,
    /// receiver account read by each incoming receipt and its previous access time
    pub incoming_accounts: Vec<Account>,
    pub incoming_tprev: Vec<u64>,
    /// account key → last access time (all ops and receipts)
    pub acct_last: HashMap<Vec<u8>, u64>,
    /// account keys in first-touch order with their (time-ordered) touches
    pub acct_order: Vec<Vec<u8>>,
    pub akm: Vec<AkmSeg>,
}

fn borsh(b: &[u8]) -> Bytes {
    ns::borsh_bytes(b)
}

/// `u32 2 ‖ id ‖ sha256 (partial)`.
fn leaf_preimage(id: &[u8], partial: &[u8]) -> Bytes {
    let mut v = ns::u32b(2);
    v.extend_from_slice(id);
    v.extend_from_slice(&sha256(partial));
    v
}

/// `OutD1.partialEncode` of a transaction outcome (`failedOutcome` / success).
fn tx_partial(signer: &[u8], success: Option<(&[u8], u128, u128)>) -> Bytes {
    match success {
        None => {
            let mut v = ns::u32b(0);
            v.extend(ns::u64b(0));
            v.extend(ns::u128b(0));
            v.extend(borsh(signer));
            v.push(1);
            v
        }
        Some((rid, gas, tok)) => {
            let mut v = ns::u32b(1);
            v.extend_from_slice(rid);
            v.extend(ns::u64b(gas));
            v.extend(ns::u128b(tok));
            v.extend(borsh(signer));
            v.push(3);
            v.extend_from_slice(rid);
            v
        }
    }
}

/// `decodeSigner`.
fn decode_signer(raw: &[u8]) -> Result<Account, String> {
    if raw.len() >= 16 && ns::le_nat(&raw[..16]) == params::U128_MAX {
        return err("out of domain (t.signer_v1)");
    }
    Account::decode(raw).ok_or_else(|| "invalid: StorageInconsistentState (signer account)".into())
}

fn read(t: &PTrie, key: &[u8], what: &str) -> Result<Option<Bytes>, String> {
    find(t, key).ok_or_else(|| format!("invalid: MissingTrieValue ({what})"))
}

/// `valueIndex t key` (the value record id of `key` in the τ = 0 trie).
fn vid_of(t: &PTrie, key: &[u8]) -> Result<u64, String> {
    crate::v3::rcptfam::value_index(t, key)
        .map(|i| i as u64)
        .ok_or_else(|| "D1: value record of a read key".into())
}

fn unnib(n: &[u8]) -> Bytes {
    n.chunks(2)
        .map(|p| p[0] * 16 + p.get(1).copied().unwrap_or(0))
        .collect()
}

/// Run the D1 main transition natively.
pub fn d1_run(cb: &[u8], wb: &[u8]) -> Result<D1Run, String> {
    let k = walk_d0(cb)?;
    let w = decode_w_d1(wb)?;
    let b2 = k.blks.get(k.b2i).ok_or("walk: B2")?;
    let prev_b2 = k.blks.get(k.b2i + 1).ok_or("walk: prev B2")?;
    let ctx = block_ctx(
        &k.layout,
        k.h_chunk.shard_id,
        k.slot_b2.gas_limit,
        b2,
        prev_b2.hdr.next_gas_price,
    );
    let receipts = applied_receipts(&k, &w.base);
    let root = k.slot_b2.prev_state_root.clone();
    let t0 = partial_trie(&w.base.main.values, &root, &[key_buffered_idx()]);
    let bshards = match find(&t0, &key_buffered_idx()) {
        Some(v) => buffered_shards(v.as_deref())?,
        None => return err("invalid: MissingTrieValue (BufferedReceiptIndices)"),
    };
    let flags: Vec<bool> = k.c.tx_valid.iter().map(|&b| b != 0).collect();
    if flags.len() != w.txs.len() {
        return err("invalid: tx_valid length");
    }
    // the relation's trie (all transaction keys)
    let mut keys = main_keys(&receipts, &bshards);
    for t in &w.txs {
        keys.push(account_key_path(&t.signer_id));
        keys.push(key_access_key(&t.signer_id, &t.pk_key()));
    }
    let t_rel = partial_trie(&w.base.main.values, &root, &keys);
    if t_rel.hash_of() != root {
        return err("invalid: main base_state does not hash to prev_state_root");
    }
    let height = ctx.height;
    let gp = ctx.gas_price;
    // ---- processTxs
    let mut trie = t_rel.clone();
    let mut seen: Vec<Bytes> = vec![];
    let mut ops: Vec<OpN> = vec![];
    let mut walks: Vec<(u64, Bytes)> = vec![];
    let mut leaf_pre: Vec<Bytes> = vec![];
    let mut locals: Vec<Receipt> = vec![];
    let mut fwd: Vec<Receipt> = vec![];
    let mut gas: u128 = 0;
    let mut tokens: u128 = 0;
    let mut acct_last: HashMap<Vec<u8>, u64> = HashMap::new();
    let mut ak_last: HashMap<Vec<u8>, u64> = HashMap::new();
    let mut acct_order: Vec<Vec<u8>> = vec![];
    let mut read_keys: Vec<Vec<u8>> = vec![];
    let mut ak_keys: Vec<Vec<u8>> = vec![];
    let mut writes: Vec<Vec<u8>> = vec![];
    for (t, &flag) in w.txs.iter().zip(&flags) {
        let h = t.hash();
        if seen.contains(&h) {
            continue;
        }
        seen.push(h.clone());
        if !flag {
            leaf_pre.push(leaf_preimage(&h, &tx_partial(&t.signer_id, None)));
            continue;
        }
        let o = ops.len() as u64;
        let time = o + 1;
        let valid = t.valid();
        let cost = tx::tx_cost(t, gp);
        let mut op = OpN {
            kind: 0,
            strict: t.strict,
            valid,
            cok: cost.is_some(),
            nonce: t.nonce,
            bound: tx::nonce_bound(height),
            amount: cost.map_or(0, |c| c.total_cost),
            signer: t.signer_id.clone(),
            pk: t.pk_key(),
            ..OpN::default()
        };
        let mut outcome: Option<(Bytes, u128, u128)> = None;
        if let (true, Some(c)) = (valid, cost) {
            let akey = account_key_path(&t.signer_id);
            walks.push((W_TX + 2 * o, unnib(&akey)));
            if let Some(araw) = read(&trie, &akey, "signer account")? {
                let a = decode_signer(&araw)?;
                op.stage = 1;
                op.acct = Some(a.clone());
                op.tp_a = acct_last.get(&akey).copied().unwrap_or(0);
                if !acct_order.contains(&akey) {
                    acct_order.push(akey.clone());
                }
                acct_last.insert(akey.clone(), time);
                read_keys.push(akey.clone());
                writes.push(akey.clone());
                let kkey = key_access_key(&t.signer_id, &t.pk_key());
                walks.push((W_TX + 2 * o + 1, unnib(&kkey)));
                if let Some(kraw) = read(&trie, &kkey, "access key")? {
                    let kv = tx::decode_access_key(&kraw)
                        .ok_or("invalid: StorageInconsistentState (access key)")?;
                    op.stage = 2;
                    op.kn = kv.0;
                    op.fa = kv.1 == Perm::FullAccess;
                    op.tp_k = ak_last.get(&kkey).copied().unwrap_or(0);
                    ak_last.insert(kkey.clone(), time);
                    read_keys.push(kkey.clone());
                    if !ak_keys.contains(&kkey) {
                        ak_keys.push(kkey.clone());
                    }
                    if op.fa {
                        writes.push(kkey.clone());
                    }
                    if let Some(new_amount) = tx::verify_and_charge(&a, kv, t, &c, height) {
                        op.ok = true;
                        let rid = receipt_id_from(&h, height as u128, 0);
                        let r = Receipt {
                            predecessor_id: t.signer_id.clone(),
                            receiver_id: t.receiver_id.clone(),
                            receipt_id: rid.clone(),
                            signer_id: t.signer_id.clone(),
                            signer_pk: t.pk_key(),
                            gas_price: c.receipt_gas_price,
                            deposit: t.deposit,
                        };
                        if t.receiver_id == t.signer_id {
                            locals.push(r);
                        } else {
                            fwd.push(r);
                        }
                        match tokens.checked_add(c.burnt_amount) {
                            None => op.tov = true,
                            Some(tk) => {
                                gas += c.gas_burnt;
                                if gas >= 1 << 64 {
                                    return err("invalid: chunk gas overflow");
                                }
                                tokens = tk;
                                let a2 = Account {
                                    amount: new_amount,
                                    ..a.clone()
                                };
                                if !set_in_place(&mut trie, &akey, &a2.encode()) {
                                    return err("invalid: signer account path not revealed");
                                }
                                if !set_in_place(
                                    &mut trie,
                                    &kkey,
                                    &tx::encode_full_access_key(t.nonce),
                                ) {
                                    return err("invalid: access key path not revealed");
                                }
                                outcome = Some((rid, c.gas_burnt, c.burnt_amount));
                            }
                        }
                    }
                }
            }
        }
        // a transaction whose tokens overflow gets no outcome
        if !op.tov {
            let s = outcome.as_ref().map(|(r, g, tk)| (r.as_slice(), *g, *tk));
            leaf_pre.push(leaf_preimage(&h, &tx_partial(&t.signer_id, s)));
        }
        ops.push(op);
    }
    if locals
        .iter()
        .any(|r| !crate::near::reexec::spec::is_named(&r.receiver_id))
    {
        return err("out of domain (r.shape): local receipt to a non-named account");
    }
    // ---- local receipts (credit ops), then incoming receipts
    let mut acc = Acc {
        trie,
        refunds: vec![],
        tokens_burnt: tokens,
    };
    let mut local_ids = vec![];
    for r in &locals {
        let o = ops.len() as u64;
        let time = o + 1;
        let akey = account_key_path(&r.receiver_id);
        let a = get(&acc.trie, &akey)
            .and_then(|b| Account::decode(&b))
            .ok_or("D1: local receipt account")?;
        walks.push((W_TX + 2 * o, unnib(&akey)));
        let tp = acct_last.get(&akey).copied().unwrap_or(0);
        acct_last.insert(akey.clone(), time);
        if !acct_order.contains(&akey) {
            acct_order.push(akey.clone());
        }
        writes.push(akey.clone());
        ops.push(OpN {
            kind: 1,
            stage: 1,
            cok: true,
            valid: true,
            amount: r.deposit,
            signer: r.receiver_id.clone(),
            pk: r.signer_pk.clone(),
            acct: Some(a),
            tp_a: tp,
            ..OpN::default()
        });
        if !apply_receipt(height, gp, &mut acc, r) {
            return err("out of domain (r.success): local receipt fails");
        }
        let o = crate::v3::rcptfam::native_outcome(height, gp, r);
        leaf_pre.push(leaf_preimage(&o.id, &o.partial_encode()));
        local_ids.push(r.receipt_id.clone());
    }
    let local_refunds = acc.refunds.clone();
    let tok0 = acc.tokens_burnt;
    let t0n = ops.len() as u64;
    let m0 = leaf_pre.len() as u64;
    let mut incoming_accounts = vec![];
    let mut incoming_tprev = vec![];
    let mut all_leaf_pre = leaf_pre.clone();
    for (i, r) in receipts.iter().enumerate() {
        let akey = account_key_path(&r.receiver_id);
        let a = get(&acc.trie, &akey)
            .and_then(|b| Account::decode(&b))
            .ok_or_else(|| format!("D1: receipt {i}: receiver account unreadable"))?;
        incoming_accounts.push(a);
        incoming_tprev.push(acct_last.get(&akey).copied().unwrap_or(0));
        acct_last.insert(akey.clone(), i as u64 + 1 + t0n);
        if !acct_order.contains(&akey) {
            acct_order.push(akey.clone());
        }
        writes.push(akey.clone());
        let ok = if r.predecessor_id == ns::SYSTEM {
            apply_system_receipt(&mut acc, r)
        } else {
            apply_receipt(height, gp, &mut acc, r)
        };
        if !ok {
            return err(format!("D1: receipt {i}: native application failed"));
        }
        let o = crate::v3::rcptfam::native_outcome(height, gp, r);
        all_leaf_pre.push(leaf_preimage(&o.id, &o.partial_encode()));
    }
    let refunds: Vec<Receipt> = acc.refunds[local_refunds.len()..].to_vec();
    let n_rcpt = (locals.len() + receipts.len()) as u128;
    let gas_used = gas + n_rcpt * params::G;
    let tokens_total = acc.tokens_burnt;
    let post_main = acc.trie;
    // sanity: outcome root, gas, tokens
    let leaves: Vec<Bytes> = all_leaf_pre.iter().map(|b| sha256(b).to_vec()).collect();
    if ns::merkle_root(&leaves) != k.h_chunk.prev_outcome_root {
        return err("D1 native: outcome root differs from the header");
    }
    if k.h_chunk.prev_gas_used as u128 != gas_used {
        return err("D1 native: gas used differs from the header");
    }
    if k.h_chunk.prev_balance_burnt != tokens_total {
        return err("D1 native: balance burnt differs from the header");
    }
    // the AIR pre trie: main keys and the read transaction keys
    let mut air_keys = main_keys(&receipts, &bshards);
    air_keys.extend(read_keys.iter().cloned());
    let pre = partial_trie(&w.base.main.values, &root, &air_keys);
    for op in ops.iter_mut() {
        if op.stage >= 1 {
            op.vid_a = vid_of(&pre, &account_key_path(&op.signer))?;
        }
        if op.stage == 2 {
            op.vid_k = vid_of(&pre, &key_access_key(&op.signer, &op.pk))?;
        }
    }
    // access-key segments
    let mut akm = vec![];
    for key in &ak_keys {
        let vid = vid_of(&pre, key)?;
        let bytes = get(&pre, key).ok_or("D1: access key bytes")?;
        let post = get(&post_main, key).ok_or("D1: access key post")?;
        let u = receipts
            .iter()
            .filter(|r| {
                r.predecessor_id == ns::SYSTEM
                    && r.signer_id == r.receiver_id
                    && &key_access_key(&r.receiver_id, &r.signer_pk) == key
            })
            .count() as u64;
        akm.push(AkmSeg {
            vid,
            key: key.clone(),
            bytes,
            tlast: ak_last.get(key).copied().unwrap_or(0),
            post: post[..8.min(post.len())].to_vec(),
            u,
        });
    }
    let lr_len: usize = local_refunds.iter().map(|r| r.encode().len()).sum();
    let fwd_len: usize = fwd.iter().map(|r| r.encode().len()).sum();
    let ntx_len: usize = w.new_txs.iter().map(|t| t.raw.len()).sum();
    let o0 = (4 + ntx_len + 4 + fwd_len + lr_len) as u64;
    let _ = writes;
    Ok(D1Run {
        k,
        ctx,
        w,
        receipts,
        bshards,
        ops,
        walks,
        leaf_pre,
        all_leaf_pre,
        local_ids,
        locals,
        m0,
        t0: t0n,
        o0,
        tok0,
        fwd,
        local_refunds,
        refunds,
        gas_used,
        tokens: tokens_total,
        pre,
        post_main,
        incoming_accounts,
        incoming_tprev,
        acct_last,
        acct_order,
        akm,
    })
}

impl D1Run {
    /// The written keys (accounts and FullAccess keys), each once.
    pub fn written_keys(&self) -> Vec<Vec<u8>> {
        let mut ks: Vec<Vec<u8>> = self.acct_order.clone();
        for s in &self.akm {
            if s.bytes.len() == 9 && s.bytes[8] == 1 {
                ks.push(s.key.clone());
            }
        }
        ks
    }

    /// The trie-side native objects (`Native`) of the D1 run: `pre` = the AIR pre trie,
    /// `old_post` = `pre` with the written keys' final values, `post` = the scheduler upsert
    /// of `old_post` (checked against the witness), the implicit steps and the scheduler
    /// upsert runs (as `native_of`), and the transaction walks as extra queries.
    pub fn native(&self) -> Result<Native, String> {
        let mut old_post = self.pre.clone();
        let mut writes = vec![];
        for key in self.written_keys() {
            let v = get(&self.post_main, &key).ok_or("D1: written value")?;
            if !set_in_place(&mut old_post, &key, &v) {
                return err("D1: replay: set failed");
            }
            writes.push((key, v));
        }
        let (_, state) = native::sched_step(&self.ctx, &self.pre)?;
        let post = native::trace::upsert(&old_post, &key_bw_state(), &state)
            .ok_or("D1: scheduler upsert failed")?;
        if post.hash_of() != self.w.base.main.post_state_root {
            return err("D1: main transition post state root");
        }
        let k = &self.k;
        let mut steps = Vec::new();
        let mut ictxs = Vec::new();
        let mut root = post.hash_of();
        for (b, t) in k.implicit_blks.iter().zip(&self.w.base.implicit) {
            let pre = partial_trie(&t.values, &root, &[key_delayed_idx(), key_bw_state()]);
            let ictx = block_ctx(
                &k.layout,
                k.h_chunk.shard_id,
                k.slot_b2.gas_limit,
                b,
                b.hdr.next_gas_price,
            );
            let ipost = native::apply_missing_chunk(&ictx, &pre)?;
            root = ipost.hash_of();
            if root != t.post_state_root {
                return err("invalid: implicit transition post state root");
            }
            steps.push(Step { pre, post: ipost });
            ictxs.push(ictx);
        }
        let mut us = vec![native::scheduler_upsert_witness(&self.ctx, &old_post)?];
        for (e, ictx) in steps.iter().zip(&ictxs) {
            us.push(native::scheduler_upsert_witness(ictx, &e.pre)?);
        }
        let mut extra = vec![];
        for (wid, key) in &self.walks {
            extra.push(Query {
                wid: *wid,
                tau: 0,
                key: ns::nibbles(key),
            });
        }
        Ok(Native {
            pre: self.pre.clone(),
            post,
            buffered_shards: self.bshards.clone(),
            old_post,
            writes,
            steps,
            us,
            receipts: self.receipts.clone(),
            extra_queries: extra,
        })
    }
}
