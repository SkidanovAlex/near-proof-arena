//! Native objects of an accepted D0a witness — the inputs of the trie-side entry
//! derivation (`v3::trie`).  Rust twin of `conformance/TrieEntriesV3.lean`'s
//! `TrieNat` (`nativeOf`) plus the scheduler upsert runs (`Render/Ups/TreeTrace.lean`).
//!
//! The JSON form ([`Native::to_json`] / [`Native::from_json`]) is exactly the
//! `np-lean-trie-v3 <case> native` dump (tries as `{h}` / `{l,v,m}` / `{e,c,m}` /
//! `{b,k,m}`, bytes as lowercase hex, `UKind`/`UCase` as their `.all` indices), so
//! every stage can be differential-tested on its own: the native execution
//! ([`native_of`]) against the dump, and the later stages from a parsed dump.
//!
//! | Rust | Lean |
//! |---|---|
//! | [`native_of`] | `TrieEntriesV3.nativeOf` (`conformance/TrieEntriesV3.lean`) |
//! | `apply_new_chunk` / `apply_missing_chunk` / `sched_step` / `read_key` / `queue_empty` | `applyNewChunk` / `applyMissingChunk` / `schedStep` / `readKey` / `queueEmpty` (`NearSpecV3/RuntimeD0.lean`) |
//! | `sched::run_core_state` | `Scheduler.runCore` (`NearSpecV3/PrepD0.lean`; `prims.sched`, `ChunkValidationV0.lean`) |
//! | `trace::upsert` | `PTrie.upsert` (`NearSpec/TrieUpsert.lean`) |
//! | `trace::trace_upsert` | `traceUpsert` / `traceKids` (`Render/Ups/TreeTrace.lean`) |
//! | `scheduler_upsert_witness` | `schedulerUpsertWitness` (`Assembly/SchedulerUpsertCost.lean`) |
//! | the implicit loop in [`native_of`] | `traceImplicit` (`Assembly/ImplicitTrace.lean`), ctx `implicitCtx` (`SchedulerSanityPin.lean`) |

use serde_json::{Value, json};

use crate::near::spec::{self as ns, Bytes, PTrie, Receipt, Slot, account_key_path};
use crate::v3::d0::{ApplyCtx, block_ctx, sched_pub, walk_d0};
use crate::v3::hint::{
    Acc, applied_receipts, apply_receipt, apply_system_receipt, buffered_shards, decode_w, find,
    get as trie_get, key_buffered_idx, key_bw_state, key_delayed_idx, key_groups_data,
    key_yield_idx, main_keys, partial_trie, set_in_place,
};

pub(crate) mod sched;
mod trace;

/// `UKind` (`Extract/Ups/PlanDefs.lean`), `UKind.all` order.
pub const UK_RDB: u8 = 0;
pub const UK_RDE: u8 = 1;
pub const UK_RLP: u8 = 2;
pub const UK_RBR: u8 = 3;
pub const UK_RBV: u8 = 4;
pub const UK_RBI: u8 = 5;
pub const UK_MVL: u8 = 6;
pub const UK_MVE: u8 = 7;
pub const UK_NLF: u8 = 8;
pub const UK_WEX: u8 = 9;
pub const UK_SPB: u8 = 10;
pub const UK_PT: u8 = 11;

/// `UCase`, `UCase.all` order.
pub const UC_LP: u8 = 0;
pub const UC_BR: u8 = 1;
pub const UC_BV: u8 = 2;
pub const UC_BI: u8 = 3;
pub const UC_LSA: u8 = 4;
pub const UC_LSB: u8 = 5;
pub const UC_LSC: u8 = 6;
pub const UC_ESL0: u8 = 7;
pub const UC_ESL1: u8 = 8;
pub const UC_ESN0: u8 = 9;
pub const UC_ESN1: u8 = 10;

/// `TreePart` (`Render/Ups/TreeTrace.lean`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreePart {
    pub kind: u8,
    pub source: PTrie,
    pub output: PTrie,
    /// branch slot for RDB/RBI, otherwise 0.
    pub slot: u64,
}

/// `TreeRun`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeRun {
    pub output: PTrie,
    pub parts: Vec<TreePart>,
    pub terminal: u8,
    pub matched: u64,
    pub terminal_source: PTrie,
    pub terminal_key: Vec<u8>,
}

/// `SchedulerUpsertWitness` without `ctx`: `traceUpsert pre keyBwState value = some run`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UpsertW {
    pub pre: PTrie,
    pub value: Bytes,
    pub run: TreeRun,
}

/// `ImplicitStepV3` (pre/post tries only).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    pub pre: PTrie,
    pub post: PTrie,
}

/// `Qv.MainValues`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MainValues {
    pub delayed: Option<Bytes>,
    pub buffered: Option<Bytes>,
    pub shards: Vec<u64>,
    pub yielded: Option<Bytes>,
}

/// The native objects (`TrieNat`): main pre/post tries, buffered shards, the
/// account-write replay (`writes`, `old_post`), the implicit steps and the scheduler
/// upserts `us` (main call on `old_post`, then one per implicit step), plus the applied
/// receipts (not part of the JSON dump).
#[derive(Clone, Debug, Default)]
pub struct Native {
    pub pre: PTrie,
    pub post: PTrie,
    pub buffered_shards: Vec<u64>,
    pub old_post: PTrie,
    pub writes: Vec<(Vec<u8>, Bytes)>,
    pub steps: Vec<Step>,
    pub us: Vec<UpsertW>,
    pub receipts: Vec<Receipt>,
}

impl Default for PTrie {
    fn default() -> Self {
        PTrie::Hash(vec![])
    }
}

// ---------------------------------------------------------------------------
// JSON (the `np-lean-trie-v3 native` format)
// ---------------------------------------------------------------------------

pub fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

pub fn unhex(s: &str) -> Result<Bytes, String> {
    if !s.len().is_multiple_of(2) {
        return Err(format!("odd hex length {}", s.len()));
    }
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).map_err(|e| e.to_string()))
        .collect()
}

fn nats(v: &Value) -> Result<Vec<u8>, String> {
    v.as_array()
        .ok_or("expected array")?
        .iter()
        .map(|x| {
            x.as_u64()
                .map(|n| n as u8)
                .ok_or_else(|| "expected nat".to_string())
        })
        .collect()
}

fn hexv(v: &Value) -> Result<Bytes, String> {
    unhex(v.as_str().ok_or("expected hex string")?)
}

fn optb(v: &Value) -> Result<Option<Bytes>, String> {
    if v.is_null() {
        Ok(None)
    } else {
        hexv(v).map(Some)
    }
}

fn u(v: &Value) -> Result<u64, String> {
    v.as_u64().ok_or_else(|| format!("expected nat, got {v}"))
}

fn get<'a>(v: &'a Value, k: &str) -> Result<&'a Value, String> {
    v.get(k).ok_or_else(|| format!("missing field {k}"))
}

pub fn slot_json(s: &Slot) -> Value {
    match s {
        Slot::Val(v) => json!({ "val": hex(v) }),
        Slot::Ref(n, h) => json!({ "ref": [*n as u64, hex(h)] }),
    }
}

pub fn slot_from(v: &Value) -> Result<Slot, String> {
    if let Some(x) = v.get("val") {
        return Ok(Slot::Val(hexv(x)?));
    }
    let r = get(v, "ref")?.as_array().ok_or("ref: expected pair")?;
    if r.len() != 2 {
        return Err("ref: expected pair".into());
    }
    Ok(Slot::Ref(u(&r[0])? as u128, hexv(&r[1])?))
}

pub fn pt_json(t: &PTrie) -> Value {
    match t {
        PTrie::Hash(h) => json!({ "h": hex(h) }),
        PTrie::Leaf(k, v, m) => json!({ "l": k, "v": slot_json(v), "m": *m as u64 }),
        PTrie::Ext(k, c, m) => json!({ "e": k, "c": pt_json(c), "m": *m as u64 }),
        PTrie::Branch(v, cs, m) => json!({
            "b": v.as_ref().map(slot_json).unwrap_or(Value::Null),
            "k": cs.iter().map(|c| c.as_ref().map(pt_json).unwrap_or(Value::Null)).collect::<Vec<_>>(),
            "m": *m as u64,
        }),
    }
}

pub fn pt_from(v: &Value) -> Result<PTrie, String> {
    if let Some(h) = v.get("h") {
        return Ok(PTrie::Hash(hexv(h)?));
    }
    let m = u(get(v, "m")?)? as u128;
    if let Some(k) = v.get("l") {
        return Ok(PTrie::Leaf(nats(k)?, slot_from(get(v, "v")?)?, m));
    }
    if let Some(k) = v.get("e") {
        return Ok(PTrie::Ext(nats(k)?, Box::new(pt_from(get(v, "c")?)?), m));
    }
    let b = get(v, "b")?;
    let b = if b.is_null() {
        None
    } else {
        Some(slot_from(b)?)
    };
    let ks = get(v, "k")?.as_array().ok_or("k: expected array")?;
    let cs = ks
        .iter()
        .map(|c| {
            if c.is_null() {
                Ok(None)
            } else {
                pt_from(c).map(Some)
            }
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(PTrie::Branch(b, cs, m))
}

pub fn run_json(r: &TreeRun) -> Value {
    json!({
        "output": pt_json(&r.output),
        "parts": r.parts.iter().map(|p| json!({
            "kind": p.kind, "source": pt_json(&p.source), "output": pt_json(&p.output), "slot": p.slot,
        })).collect::<Vec<_>>(),
        "terminal": r.terminal,
        "matched": r.matched,
        "terminalSource": pt_json(&r.terminal_source),
        "terminalKey": r.terminal_key,
    })
}

pub fn run_from(v: &Value) -> Result<TreeRun, String> {
    let parts = get(v, "parts")?
        .as_array()
        .ok_or("parts: expected array")?
        .iter()
        .map(|p| {
            Ok(TreePart {
                kind: u(get(p, "kind")?)? as u8,
                source: pt_from(get(p, "source")?)?,
                output: pt_from(get(p, "output")?)?,
                slot: u(get(p, "slot")?)?,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(TreeRun {
        output: pt_from(get(v, "output")?)?,
        parts,
        terminal: u(get(v, "terminal")?)? as u8,
        matched: u(get(v, "matched")?)?,
        terminal_source: pt_from(get(v, "terminalSource")?)?,
        terminal_key: nats(get(v, "terminalKey")?)?,
    })
}

impl MainValues {
    pub fn to_json(&self) -> Value {
        let o = |b: &Option<Bytes>| {
            b.as_ref()
                .map(|x| Value::String(hex(x)))
                .unwrap_or(Value::Null)
        };
        json!({ "delayed": o(&self.delayed), "buffered": o(&self.buffered), "shards": self.shards,
                "yielded": o(&self.yielded) })
    }
    pub fn from_json(v: &Value) -> Result<MainValues, String> {
        Ok(MainValues {
            delayed: optb(get(v, "delayed")?)?,
            buffered: optb(get(v, "buffered")?)?,
            shards: get(v, "shards")?
                .as_array()
                .ok_or("shards")?
                .iter()
                .map(u)
                .collect::<Result<_, _>>()?,
            yielded: optb(get(v, "yielded")?)?,
        })
    }
}

impl Native {
    /// The native part of the dump (`pre post bufferedShards oldPost writes steps us`).
    pub fn to_json(&self) -> Value {
        json!({
            "pre": pt_json(&self.pre),
            "post": pt_json(&self.post),
            "bufferedShards": self.buffered_shards,
            "oldPost": pt_json(&self.old_post),
            "writes": self.writes.iter().map(|(k, b)| json!([k, hex(b)])).collect::<Vec<_>>(),
            "steps": self.steps.iter().map(|s| json!({"pre": pt_json(&s.pre), "post": pt_json(&s.post)})).collect::<Vec<_>>(),
            "us": self.us.iter().map(|w| json!({"pre": pt_json(&w.pre), "value": hex(&w.value), "run": run_json(&w.run)})).collect::<Vec<_>>(),
        })
    }

    /// Parse a `np-lean-trie-v3 native` dump (`receipts` left empty).
    pub fn from_json(v: &Value) -> Result<Native, String> {
        let arr = |k: &str| -> Result<&Vec<Value>, String> {
            get(v, k)?
                .as_array()
                .ok_or_else(|| format!("{k}: expected array"))
        };
        Ok(Native {
            pre: pt_from(get(v, "pre")?)?,
            post: pt_from(get(v, "post")?)?,
            buffered_shards: arr("bufferedShards")?
                .iter()
                .map(u)
                .collect::<Result<_, _>>()?,
            old_post: pt_from(get(v, "oldPost")?)?,
            writes: arr("writes")?
                .iter()
                .map(|w| Ok((nats(&w[0])?, hexv(&w[1])?)))
                .collect::<Result<_, String>>()?,
            steps: arr("steps")?
                .iter()
                .map(|s| {
                    Ok(Step {
                        pre: pt_from(get(s, "pre")?)?,
                        post: pt_from(get(s, "post")?)?,
                    })
                })
                .collect::<Result<_, String>>()?,
            us: arr("us")?
                .iter()
                .map(|w| {
                    Ok(UpsertW {
                        pre: pt_from(get(w, "pre")?)?,
                        value: hexv(get(w, "value")?)?,
                        run: run_from(get(w, "run")?)?,
                    })
                })
                .collect::<Result<_, String>>()?,
            receipts: vec![],
        })
    }
}

// ---------------------------------------------------------------------------
// Native execution (`TrieEntriesV3.nativeOf`)
// ---------------------------------------------------------------------------

/// `readKey t k what` (`RuntimeD0.lean`): `find`, undetermined = `MissingTrieValue`.
fn read_key(t: &PTrie, k: &[u8], what: &str) -> Result<Option<Bytes>, String> {
    find(t, k).ok_or_else(|| format!("invalid: MissingTrieValue ({what})"))
}

/// `queueEmpty v what` (`RuntimeD0.lean`).
fn queue_empty(v: Option<Bytes>, what: &str) -> Result<(), String> {
    match v {
        None => Ok(()),
        Some(b) if b.len() != 16 => Err(format!("invalid: StorageInconsistentState ({what})")),
        Some(b) if ns::le_nat(&b[..8]) == ns::le_nat(&b[8..]) => Ok(()),
        Some(_) => Err(format!("out of domain (e.queues_empty): {what} not empty")),
    }
}

/// `schedStep prims ctx t` (`RuntimeD0.lean`), keeping `out.state` only:
/// read `keyBwState`, `prims.sched` (= `(Scheduler.pubOf …).bind (runCore · prev)`,
/// `ChunkValidationV0.prims`, `PrepD0.run_eq_core`), upsert the new state.
fn sched_step(ctx: &ApplyCtx, t: &PTrie) -> Result<(PTrie, Bytes), String> {
    let prev = read_key(t, &key_bw_state(), "bandwidth scheduler state")?;
    let state = sched_pub(
        &ctx.layout.shard_ids,
        &ctx.statuses,
        &ctx.requests,
        &ctx.prev_block_hash,
    )
    .and_then(|p| sched::run_core_state(&p, prev.as_deref()))
    .ok_or("invalid: bandwidth scheduler aborted (StorageInconsistentState)")?;
    let t2 = trace::upsert(t, &key_bw_state(), &state)
        .ok_or("invalid: MissingTrieValue (bandwidth scheduler state path)")?;
    Ok((t2, state))
}

/// `applyNewChunk prims ctx t receipts` (`RuntimeD0.lean`), returning `out.trie`.
///
/// The receipts are applied with `hint::apply_receipt` / `hint::apply_system_receipt`
/// (`TransferV1.applyReceipt` / `applySystemReceipt`, trie effects).  Not checked here:
/// `tryForward` of the generated refunds (it needs the scheduler grants of
/// `distribute`); it only decides `out of domain (e.forwarded)` and never changes the
/// trie, and the inputs are accepted witnesses.
fn apply_new_chunk(ctx: &ApplyCtx, t: &PTrie, receipts: &[Receipt]) -> Result<PTrie, String> {
    queue_empty(
        read_key(t, &key_delayed_idx(), "DelayedReceiptIndices")?,
        "delayed receipt queue",
    )?;
    let (t, _) = sched_step(ctx, t)?;
    let shards =
        buffered_shards(read_key(&t, &key_buffered_idx(), "BufferedReceiptIndices")?.as_deref())?;
    for s in shards {
        read_key(&t, &key_groups_data(s), "BufferedReceiptGroupsQueueData")?;
    }
    let mut acc = Acc {
        trie: t,
        refunds: vec![],
        tokens_burnt: 0,
    };
    for (i, r) in receipts.iter().enumerate() {
        if i as u128 * ns::params::G >= ctx.gas_limit as u128 {
            return Err("out of domain (e.compute): receipt delayed by the compute limit".into());
        }
        let ok = if r.predecessor_id == ns::SYSTEM {
            apply_system_receipt(&mut acc, r)
        } else {
            apply_receipt(ctx.height, ctx.gas_price, &mut acc, r)
        };
        if !ok {
            return Err(match find(&acc.trie, &account_key_path(&r.receiver_id)) {
                None => "invalid: MissingTrieValue (account)".into(),
                Some(_) => "out of domain (r.success): receipt fails".into(),
            });
        }
    }
    queue_empty(
        read_key(&acc.trie, &key_yield_idx(), "PromiseYieldIndices")?,
        "promise yield queue",
    )?;
    Ok(acc.trie)
}

/// `applyMissingChunk prims ctx t` (`RuntimeD0.lean`).
fn apply_missing_chunk(ctx: &ApplyCtx, t: &PTrie) -> Result<PTrie, String> {
    read_key(t, &key_delayed_idx(), "DelayedReceiptIndices")?;
    Ok(sched_step(ctx, t)?.0)
}

/// `schedulerUpsertWitness ctx pre` (`Assembly/SchedulerUpsertCost.lean`).
fn scheduler_upsert_witness(ctx: &ApplyCtx, pre: &PTrie) -> Result<UpsertW, String> {
    let (_, value) = sched_step(ctx, pre)?;
    let run =
        trace::trace_upsert(pre, &key_bw_state(), &value).ok_or("scheduler upsert trace failed")?;
    Ok(UpsertW {
        pre: pre.clone(),
        value,
        run,
    })
}

/// The native execution of an accepted witness (`TrieEntriesV3.nativeOf`): walk, decode,
/// applied receipts, the partial main pre-trie, `applyNewChunk` (scheduler step then the
/// receipts), the implicit steps (`traceImplicit`: `applyMissingChunk` per implicit
/// block), the account-write replay and the scheduler upserts (`schedulerUpsertWitness`).
/// (`prepD0`, part of Lean's `TrieNat`, is not computed here.)
pub fn native_of(cb: &[u8], wb: &[u8]) -> Result<Native, String> {
    let k = walk_d0(cb)?;
    let w = decode_w(wb)?;
    let b2 = k.blks.get(k.b2i).ok_or("walk: B2")?;
    let prev_b2 = k.blks.get(k.b2i + 1).ok_or("walk: prev B2")?;
    let receipts = applied_receipts(&k, &w);
    let root = &k.slot_b2.prev_state_root;
    let t0 = partial_trie(&w.main.values, root, &[key_buffered_idx()]);
    let bshards = match find(&t0, &key_buffered_idx()) {
        Some(v) => buffered_shards(v.as_deref())?,
        None => return Err("missing buffered index".into()),
    };
    let t_main = partial_trie(&w.main.values, root, &main_keys(&receipts, &bshards));
    // `m.ctx k` = `blockCtx k.L k.H.shardId k.slotB2.gasLimit B2 prevB2.hdr.nextGasPrice`
    let ctx = block_ctx(
        &k.layout,
        k.h_chunk.shard_id,
        k.slot_b2.gas_limit,
        b2,
        prev_b2.hdr.next_gas_price,
    );
    let post = apply_new_chunk(&ctx, &t_main, &receipts)?;

    // `traceImplicit k out.trie.hashOf (k.implicitBlks.zip w.implicit)`
    let mut steps = Vec::new();
    let mut ictxs = Vec::new();
    let mut root = post.hash_of();
    for (b, t) in k.implicit_blks.iter().zip(&w.implicit) {
        let pre = partial_trie(&t.values, &root, &[key_delayed_idx(), key_bw_state()]);
        // `implicitCtx k e`
        let ictx = block_ctx(
            &k.layout,
            k.h_chunk.shard_id,
            k.slot_b2.gas_limit,
            b,
            b.hdr.next_gas_price,
        );
        let ipost = apply_missing_chunk(&ictx, &pre)?;
        root = ipost.hash_of();
        if root != t.post_state_root {
            return Err("invalid: implicit transition post state root".into());
        }
        steps.push(Step { pre, post: ipost });
        ictxs.push(ictx);
    }

    // account-write replay
    let writes: Vec<(Vec<u8>, Bytes)> = receipts
        .iter()
        .map(|r| {
            let key = account_key_path(&r.receiver_id);
            let v = trie_get(&post, &key).unwrap_or_default();
            (key, v)
        })
        .collect();
    let mut old_post = t_main.clone();
    for (key, v) in &writes {
        if !set_in_place(&mut old_post, key, v) {
            return Err("account replay: set failed".into());
        }
    }
    let (_, so_state) = sched_step(&ctx, &t_main)?;
    match trace::upsert(&old_post, &key_bw_state(), &so_state) {
        Some(t) if t.hash_of() == post.hash_of() => {}
        Some(_) => return Err("account replay: post root mismatch".into()),
        None => return Err("account replay: scheduler upsert failed".into()),
    }

    let mut us = vec![scheduler_upsert_witness(&ctx, &old_post)?];
    for (e, ictx) in steps.iter().zip(&ictxs) {
        us.push(scheduler_upsert_witness(ictx, &e.pre)?);
    }
    Ok(Native {
        pre: t_main,
        post,
        buffered_shards: bshards,
        old_post,
        writes,
        steps,
        us,
        receipts,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trie_json_round_trip() {
        let t = PTrie::Branch(
            Some(Slot::Ref(3, vec![1, 2])),
            vec![
                None,
                Some(PTrie::Leaf(vec![1, 2, 3], Slot::Val(vec![9]), 77)),
                Some(PTrie::Ext(
                    vec![4],
                    Box::new(PTrie::Hash(vec![0xab; 32])),
                    5,
                )),
            ],
            123,
        );
        assert_eq!(pt_from(&pt_json(&t)).unwrap(), t);
        assert_eq!(unhex(&hex(&[0, 255, 16])).unwrap(), vec![0, 255, 16]);
    }
}
