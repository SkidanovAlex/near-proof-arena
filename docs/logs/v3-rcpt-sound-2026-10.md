# Lane `lane/v3-rcpt-sound` — receipt-side soundness (`executions`: the receipt core of `m.Valid.run`), log

Worktree `/data/illia/nearproof-wt/v3-rcpt-sound`, branch `lane/v3-rcpt-sound`, from main `c87a7cae`.
Modules: `zk-formal/ZkFormal/NearV3/Rcpt/Link/{RunSplit,ForwardSound,MemBal,Mem3,MemOf,RunModel,
NewChunk,RecChain,RecModel,PrepFwd,RcptCore,AcctSlots,GasPub,RcptHolds,ValBytes,PeoBytes,RfBody,RfEnc,
RcptHoldsB,FwdLinks,AkeyAkc,SrecLink,QvPre,QvBal}.lean` (namespace
`ZkFormal.NearV3.RcptLink`).
Audit `zk-formal/test/AuditRcptSound.lean` (all `[propext, Classical.choice, Quot.sound]` or less).
No `sorry`/`axiom`; no edits outside these files; `make pin-check` passes.

## 2026-10-11 — survey

* Existing soundness pieces for receipts: the view `RcptV3Wf` + exact `rcptTraffic3`
  (`rcptV3_view_nearAir`), acct (`AcctV3WfE 19`), `Rcpt/Link/*` (routing `RouteOk`, `Srec`, `Body`,
  `Keynib`, source-proof chain), `LinkRids`/`LinkRidBytes` (`encBytes`, `receiptIds_of`).
  **Nothing** concluded `applyReceipts`/`applyNewChunk … = .ok` from records: every existing
  `applyNewChunk` lemma (`Assembly/Forward`, `Compute`, `Qv/Reads`, `RcptTokenLedger`, …) goes the
  completeness direction (from a successful run).  v1 had the full chain (`Near/Link/Mem*`,
  `Run*`, `Spec/SoundRun`); this lane ports it to v3 (system receipts, access keys, abstract trie,
  forwarding/compute split).
* The class split (V3-D0-DESIGN §1): compute guard and forwarding are native in `prepBody`
  (class H); per-receipt ledger is W (rcpt/acct/akey/walk); queue reads are W (qv) on public
  keys; the scheduler step is W (scheduler tables, link lane).

## What is proved (all pushed)

| file | theorem | content |
|---|---|---|
| `RunSplit` | `applyReceipts_of_ledger` | `ledgerAll ctx acc rs = some acc'` (ledger alone) + compute guard for the indices + `forwardRun ctx ls (new refunds) = .ok ls'` ⇒ `applyReceipts ctx i (acc, ls) rs = .ok (acc', ls')` |
| `ForwardSound` | `forwardRun_of_split` | **soundness of `prepBody`'s forwarding split** (PrepD0 doc: "tested, not proved"): every refund routes to a status shard ∧ `fwdGasOk` ∧ `∀ s ∈ statusShards, demand ctx rs s ≤ grant own s` ⇒ `∃ ls', forwardRun ctx (limits0 ctx grant) rs = .ok ls'` (`limits0` = `applyNewChunk`'s initial limits) |
| `MemBal` | `mem_bal` | `MEM` bus (users rcpt 16, acct 17, no public) from `HoldsP` + `V3RecordsTraffic`: `memW3 ~ memR3` as `Fp` images |
| `Mem3` | `tprev_eq`, `tlast_eq`, `mem_read`, `mem_final` | v1 offline memory checking over `MemHyp rs as` (Nat perm, distinct acct slots, `tprev ≤ r`) |
| `MemOf` | `memHyp_of` | `MemHyp (rv r.lists) r.accts` from `HoldsP`, traffic, `V3RecordsWf` and **`hknd : (r.accts.map (·.k)).Nodup`** |
| `RunModel` | `RunModel.step`, `ledgerAll_eq` | record-free ledger on a slot-valued trie family `T`: `TrieOk` (get/find/set of account keys for all assignments, access-key find on the run's assignment) + `RcptOk3` (v1 arithmetic; burn/surplus/token bounds for non-system only) ⇒ `ledgerAll ctx (accAt 0) rs = some (accAt n)`; system receipts (no burn, no refund, access key absent/FullAccess) handled |
| `NewChunk` | `applyNewChunk_of_parts` | queue reads (`Qv.MainValues` valid, read pre/mid/final) + `schedStep prims ctx pre = .ok (mid, so)` + `T (valsAt 0) = mid` + `TrieOk` + `RcptOk3 ∀r` + compute guard + `forwardRun` ⇒ `applyNewChunk prims ctx pre M.rs = .ok (M.mainOut ctx)` |
| `RecChain` | `slot_acct`, `lanes`, `arith_at`, `bef_val` | along the `MEM` chain: every receipt slot has an acct record, `lk`/`st` are its pre lanes, `bef` is the last write; `RcptE.Wf.arith` with all byte hypotheses discharged (from `RecHyp`) |
| `RecModel` | `recModel`, `amt_inv`, `tok_inv`, `rcptOk_all` | the ledger model of the records (receipts `(rv ls).map toReceipt` = `x.applied`, slot = `kslot`, `acc0 k = accOf` of the acct record) and `RcptOk3` for every receipt |
| `PrepFwd` | `prepD0_fwd` | `prepD0 = .ok p` ⇒ `decodeBody h.body = .ok refunds`, status / `fwdGasOk` / demand `< 2^24` / compute guard on `pc.ctxB2`, `p.fwd = fwdLinks ctx refunds`, `p.hdr.n = h.n` |
| `RcptCore` | **`mainRun_of_records`**, `applied_eq` | the receipt core of `m.Valid.run` (statement below) |
| `AcctSlots` | `acct_k_nodup`, `memHyp_of'` | account slots distinct (`VSLOT` balance + `Link3.val_unique`); `MemHyp` from `HoldsP` + views alone |
| `GasPub` | `gasPrice_pub` | `pc.ctxB2.gasPrice = leN' (pubBytes pub PH_GP 16)` (closes `hgp`) |
| `ValBytes` | `Link3.val_bytes8`, `acct_written'`, `acct_pre_byte`, **`preB_of`** | value records referenced by a node slot have byte-valued bytes (`sha_core`, first conclusion of `val_sha`); `VBYTES` (users val, codec, acct, akey, qv; only val receives): acct pre byte `j` = byte `j` of a value record with `vid = k`; hence `RecBytes.preB` from the trie link's `ShaHyp r.nodes r.heads r.values others shaS shaR` (lane v3-link's `shaHyp_holds`) |
| `PeoBytes` | `located_flat`, `peo_isolate`, `othersRC_kind`, `peoBytes`, **`burntBytes`** | `PEO` stream isolation in `rcptSends3`; other `BYTES` senders never use kinds `K_PEO`/`K_RF`/`K_RID`; `sha_core` against the rcpt `DIGEST` receive `digMsg (msgId K_PEO q) |peo| peoh` (provided by the SHA union, `digest_provided`) ⇒ `peo` bytes ⇒ **`burntB`** |
| `RfBody` | `rf_isolate`, `rfStream_at`, `body_len_pub`, **`rfStream_body`**, **`ramtBytes`** | the refund stream `rfStream ls = flatR.flatMap (if hr then encRefund)` **is** `(p.body.drop 8).map toNat` (every public `(K_RF, 8+k, B[8+k])` receive is a send; only rcpt `RF` streams have kind 2; total `bOffs n = |B|` from `RcptV3Wf.body` + header `u32 |B|`) ⇒ **`ramtB`** |
| `RfEnc` | `rid_isolate`, `flat_index`, `flat_located`, **`rfid_sha`**, `height_pub`, `toBytes_encRefund3`, `toReceipt_wf3`, **`rfS_refundOf`** | `rfid = sha256(rid ‖ height ‖ 0^8)` (`sha_core`, K_RID); public height = `u64 pc.ctxB2.height`; per receipt, `toBytes (rfS x_q) = concatAll (refundOf q).map encode` and model refunds have `refundShape` (under `RecHyp`) |
| `RcptHoldsB` | `rfStream_refunds`, `pMany_refunds`, `decodeBody_tail`, **`refunds_of`**, **`mainRun_of_holdsP_sha`**, **`mainRun_of_holdsP_fwd`** | **`hrf`** closed (`decodeBody h.body = .ok refunds` + `h.body.drop 8 = concat(model refunds)` ⇒ `refunds` = model refunds; `pRefund` prefix-free on refund-shaped receipts); `RecBytes` closed given the trie link's `ShaHyp`; `hsz` replaced by the AIR's link-indexed check |
| `FwdLinks` | `shardOf_mem`, `fwdDemand_fwdLinks`, **`hsz_of_links`**, `prepClaim_layout_wf` | `hsz` from `∀ k < n, fwdDemand (fwdLinks ctx refunds) (o·n + k) ≤ grant own ids[k]` + A12 + `indexOf ids own = some o` (status shards outside the layout get no refund: `shardOf ∈ shardIds` under A12) |
| `AkeyAkc` | `rcpt_akc_sends/recvs`, `akc_count`, **`akc_akey`**, `akey_byte`, **`akey_value`** | `AKC` counting argument (weights = 2nd component; `P·w = c`, `0 < c ≤ 2^22`): an `ee ∧ akf = 0` receipt's `akk` is an akey record's vid; `VBYTES`: that akey's 9 bytes (FullAccess, last byte 1) are the value record `vid = akk`'s bytes 0..8 |
| `SrecLink` | `rSends_srec`, `rRecvs_srec`, **`srecBal_of`**, **`ee_of_self`** | `SrecBal q x` from the `SREC` balance (rcpt-only bus; canonical ids force same receipt / row / value); with `Srec.srec_neq`: a system receipt with `toBytes s = toBytes v` has `ee = true` |
| `RcptHolds` | **`mainRun_of_holdsP`** | `mainRun_of_records` from the `LinkCoreV3Stmt` hypotheses: chain, `encB`, `bgpB`, `hgp`, `PrepFwd` discharged; remaining premises explicit (below) |

### The deliverable statement (`RcptCore.mainRun_of_records`)

```
(H : RecHyp pub ls as) (hgp : ctx.gasPrice = leN' (pubBytes pub PH_GP 16))
(L : MainTrieLink ls as base T ctx pre mid so)            -- from lane v3-link
(hv : v.Valid) (hR : v.Reads pre mid (T ((recModel ls as base T).valsAt |flatR ls|)))
(F : PrepFwd ctx h p refunds) (hn : h.n = |flatR ls|)
(hrf : ((recModel ls as base T).accAt ctx |flatR ls|).refunds = refunds)
(hsz : ∀ s ∈ statusShards ctx, demand ctx refunds s ≤ so.grant ctx.own s) :
applyNewChunk prims ctx pre ((rv ls).map RcptV.toReceipt) = .ok ((recModel ls as base T).mainOut ctx)
```
with `applied_eq : x.applied = (rv x.receipts).map RcptV.toReceipt`.  `m.result :=
(recModel …).mainOut ctx` (trie `T (valsAt n)`, outcomes / refunds / `n·G` / `tokAt n` all
functions of the records).

## Interface requested from lane v3-link (exact)

`MainTrieLink ls as base T ctx pre mid so` (`RcptCore.lean`), for the main instance τ = 0 with
`ctx = m.ctx k`, `pre = m.pre`:

1. `sched : schedStep prims ctx pre = .ok (mid, so)` — the scheduler step (their lane).
2. a trie family `T : (Nat → Bytes) → PTrie` (main trie after the scheduler step, value record
   `k` holding `v k`) and the raw pre bytes `base` of every value record, with
   `init : T ((recModel ls as base T).valsAt 0) = mid`.  Note `valsAt 0 k = Account.encode (accOf a)`
   for account slots (`= toBytes a.pre` by `encode_decode`/`decode_pre`, needs `preB`) and
   `base k` otherwise.
3. `trie : (recModel ls as base T).TrieOk`, i.e. for every receipt `r` (slot `kslot_r`, the
   `FINAL` target of its account walk `keySyms`):
   * `get`/`find`: `(T v).get (accountKeyPath recv_r) = some (v kslot_r)` and
     `(T v).find … = some (some (v kslot_r))` for **all** `v`;
   * `set`: `(T v).set (accountKeyPath recv_r) b = some (T (upd v kslot_r b))` for all `v b`;
   * `ak`: for a system receipt with `signer = receiver`:
     `∃ o, (T (valsAt r)).find (keyAccessKey recv pk) = some o ∧ (o = none ∨ FullAccess o)`
     (the walk `W_AK + r` ends at `FINAL (akf, akk)`; with the akey table / `AKC` the value of
     `akk` is FullAccess — the akey part is receipt-side, to be closed here once the walk part
     is stated: "akf = 0 ⇒ find = some (some (base akk)), akf = 1 ⇒ some none, akk not an
     account slot").
4. the queue reads `hR` on `pre`, `mid` and the final trie `T (valsAt n)` (qv walks + the fact
   that the receipt sets do not touch `[10]`), and `m.Valid.buffered` on
   `partialTrie (x.store 0) root [keyBufferedIdx]` (store side).

### The trace-level form (`RcptHolds.mainRun_of_holdsP`)

```
prepD0 cb h = .ok p → |preparedBytes p oh| < P → HoldsP nearAirV3 pub tr →
V3RecordsTraffic pub tr r → V3RecordsWf pub r → h.n = |flatR r.lists| →
RecBytes r.lists r.accts →                                   -- preB, burntB, ramtB
∃ pc refunds, prepClaim cb = .ok pc ∧ decodeBody h.body = .ok refunds ∧
  ∀ base Tf pre mid so v,
    MainTrieLink r.lists r.accts base Tf pc.ctxB2 pre mid so →     -- lane v3-link
    v.Valid → v.Reads pre mid (Tf (valsAt n)) →                    -- qv reads
    (accAt pc.ctxB2 n).refunds = refunds →                         -- refund identity
    (∀ s ∈ statusShards pc.ctxB2, demand pc.ctxB2 refunds s ≤ so.grant own s) →  -- AIR fwd check
    applyNewChunk prims pc.ctxB2 pre ((rv r.lists).map toReceipt) = .ok (mainOut pc.ctxB2)
```
(`pc.ctxB2 = m.ctx k` and `x.applied = (rv r.lists).map toReceipt` for `x.receipts = r.lists`
by `applied_eq`.)

## Remaining hypotheses of `mainRun_of_records` (exact, with sources)

**Closed since:** `hknd` (`AcctSlots.acct_k_nodup`), `hgp` (`GasPub.gasPrice_pub`), `encB`,
`bgpB`, `F` (all inside `mainRun_of_holdsP`).

* `RecHyp` fields: `mem` ← `memHyp_of` needs **`hknd`** (acct slots distinct; `VSLOT` balance
  `LinkShaKinds.vslot_bal` + node `VSLOT` receives nodup via `Vals3.val_unique`); `wf`, `acct`
  ← `V3RecordsWf`; `encB` ← `LinkRidBytes.encBytes`; `bgpB` ← `LinkFields.pubNat_pubOf_lt`;
  **`preB`** (acct pre bytes ← `VBYTES` = value-record bytes, SHA glue `Link3.rec_bytes`);
  **`burntB`** (← hashed `PEO` bytes, `K_PEO` digest); **`ramtB`** (← refund body = public `B`,
  `Rcpt/Link/Body`).
* `hgp` ← `RcptSkeleton.prepared_gasPrice_byte` + `prepClaim_gasPrice` + a `gasPrice < 2^128`
  bound (u128 decode of `nextGasPrice`).
* `F` ← `prepD0_fwd` (with `ctx = pc.ctxB2 = m.ctx k`, `PrepContext.prepClaim_native_context`
  pattern); `hn` ← `LinkFields.receiptCount_of_records`.
* **`hrf`** — the run's refunds (`gasRefundReceipt (rc r) height surplus` for non-system receipts
  with surplus) are `decodeBody h.body`'s: needs the refund encoding identity
  `encode (gasRefundReceipt …) = toBytes x.encRefund` (record side) + `Body` (bytes = public `B`)
  + `decodeBody (bodyOf rs) = .ok rs` (`V3.RefundCodec`).
* **`hsz`** — `Prep.fwd` demands ≤ grants: the AIR's `fwd` check against the scheduler's
  `grant(own, s)` at link index `own·n + idx(s)` (scheduler tables, lane v3-link) and
  `fwdLinks` covering every status shard (status shards are layout shards).

Nothing false found.  Note for the lead: the forwarding split's soundness direction is now
**proved** (`forwardRun_of_split`), modulo the `fwdLinks`/link-index ↔ `grant own s` identification.

## Resume here

Done: (1) `hknd`, (3) `hgp`, `preB` (`ValBytes.preB_of`, given `ShaHyp`; reused nothing from
`LinkVBytes` — that module is about the codec's `VBYTES`; `acct_pre_byte` follows the pattern of
v3-link's `LinkVPost.vbytes_len`, which is not on main).  Next, in order: (2) `RecBytes` — `burntB`
(`K_PEO` digest bytes: needs a `K_PEO` analogue of `ListByteIsolation.list_bytes_isolate` /
`ListSha.list_sha_digest` — the rcpt `BYTES` sends with id `msgId K_PEO r` are exactly
`emitAt (msgId K_PEO r) 0 x.peo` — then `sha_core` with the rcpt `DIGEST` receive
`digMsg (msgId K_PEO r) |peo| peoh`), `ramtB` (refund body, `Rcpt/Link/Body`); (4) `hrf` (refund encoding identity); (5) the akey
half of `TrieOk.ak`; (6) `m.Valid.buffered` / qv reads (with the link lane); (7) `hsz`
(`Prep.fwd` vs scheduler grants, with the link lane).  Build: `HEAVY_MEM=12G taskset -c 8-15,24-31
/data/illia/nearproof-deps/bin/heavy lake build ZkFormal.NearV3.Rcpt.Link.RcptHolds`; audit
`lake env lean test/AuditRcptSound.lean`.

## 2026-10-11 (session 2) — RecBytes, hrf, hsz reduction, akey half

Commits (all pushed, branch `lane/v3-rcpt-sound`): `e9206997` PeoBytes, `37d372b1` RfBody,
`8399f29a` RfEnc, `fbe2b9d4` RcptHoldsB, `0ed642b3` FwdLinks + `mainRun_of_holdsP_fwd`,
`76d038a6` AkeyAkc, `962ee8b8` merge origin/main (rebuilt clean after merge), SrecLink (next commit) (A7 native post trie, A11 retired).  Audit
`test/AuditRcptSound.lean` extended (all `[propext, Classical.choice, Quot.sound]`;
`prepClaim_layout_wf` `[propext, Quot.sound]`).  `make pin-check` passes.  Nothing false found.

### Current top statement (`RcptHoldsB.mainRun_of_holdsP_fwd`)

```
prepD0 cb h = .ok p → |preparedBytes p oh| < P → HoldsP nearAirV3 pub tr →
V3RecordsTraffic pub tr r → V3RecordsWf pub r → h.n = |flatR r.lists| →
ShaHyp r.nodes r.heads r.values others shaS shaR →             -- lane v3-link: shaHyp_holds
∃ pc, prepClaim cb = .ok pc ∧
  ∀ base Tf pre mid so v o,
    MainTrieLink r.lists r.accts base Tf pc.ctxB2 pre mid so →  -- lane v3-link
    v.Valid → v.Reads pre mid (Tf (valsAt n)) →                  -- qv reads
    indexOf pc.ctxB2.layout.shardIds pc.ctxB2.own = some o →     -- own is a layout shard
    (∀ k (hk : k < n_L), fwdDemand p.fwd (o·n_L + k) ≤ so.grant pc.ctxB2.own ids[k]) →  -- AIR fwd check
    applyNewChunk prims pc.ctxB2 pre ((rv r.lists).map toReceipt) = .ok (mainOut pc.ctxB2)
```
(`mainRun_of_holdsP_sha`: same with the per-shard `hsz` instead of the last two premises.)
`RecBytes` (preB / burntB / ramtB) and `hrf` are gone.

### Remaining premises (exact) and where they come from

1. `ShaHyp …` — `Assembly.LinkChain.shaHyp_holds` (lane v3-link, not yet on main).
2. `MainTrieLink` (`sched`, `init`, `trie : TrieOk`) — lane v3-link; for `TrieOk.ak` the
   receipt side is now **`akey_value`**: for `x ∈ flatR` with `ee ∧ akf = 0`, `∃ e ∈ r.akeys`,
   `e.vid = akk`, `|e.bytes| = 9`, `e.bytes[8] = 1`, and `∃ t, values[t].vid = akk ∧ ∀ j < 9,
   values[t].bytes[j] = e.bytes[j]`.  Still needed to finish `ak` (walk + link side):
   (a) **done** (`SrecLink.ee_of_self`: system receipt with `toBytes s = toBytes v` ⇒ `ee`);
   (b) the walk `W_AK + r` (`FINAL (akf, akk)`): `akf = 0 ⇒ find = some (some (valsAt r akk))`,
   `akf = 1 ⇒ some none`; (c) `valsAt r akk = base akk` (akk not an acct slot) and
   `toBytes (value record akk) = base akk` with `|value bytes| = 9` (`VBYTES` exactness —
   `LinkVBytes` on lane v3-link; `akey_value` only fixes bytes 0..8).
3. Queue reads `v.Reads …` and `v.Valid` (incl. `buffered`) — qv side, not started this session.
4. `indexOf ids own = some o` — own shard in the layout (`L.index H.shardId` in `prepClaim` uses
   `idToIndex`; consistency with `shardIds` is decoder-level, `decodeShardLayoutV2` checks it —
   not yet linked); and the link grant identification `fwdDemand p.fwd l ≤ granted[l] + g[l]`
   (`Sched.codec_fwd` / `LinkSchedCore` τ = 0, lane v3-link) with `so.grant own ids[k]` at
   `l = o·n + k`.

### Resume here

(a) `ee` for self-refunds is done (`SrecLink`).  Next: (b) the qv
reads / `m.Valid.buffered` (raw `qvV3` table; see lane v3-link `LinkVBytes`: `stream_isolate`,
`physical_records_closed`, `byte_all_physical`); then wire `mainRun_of_holdsP_fwd` to
`shaHyp_holds` and the scheduler grant once lane v3-link lands them on main.  Build:
`lake build ZkFormal.NearV3.Rcpt.Link.RcptHoldsB ZkFormal.NearV3.Rcpt.Link.AkeyAkc`.

## 2026-10-11 (session 2, cont.) — own ∈ shardIds, queue reads to pre-state form

Commits: `c2271505` (`RcptHoldsB`: `recHyp_of`, `own_index_of_route`, **`mainRun_of_holdsP_route`**),
`8ba61514` (`QvPre`: `ledgerAll_find_other`, **`reads_of_pre`**, **`mainRun_of_holdsP_pre`**).

* **`own ∈ shardIds`.** `decodeLayout` does **not** check `idToIndex` against `shardIds`
  (`decodeShardLayoutV2`'s consistency check is only used by the scheduler's own decoder, not by
  `prepClaim`), so `L.index own = some idx` alone does not give `own ∈ shardIds`.  It is not needed:
  with no refund `hsz` is trivial; a refund comes from a receipt, which routing puts in the own
  shard (`shardOf recv = own`), and under A12 `shardOf ∈ shardIds` (`own_index_of_route`).  So the
  premise `indexOf ids own = some o` is replaced by the routing fact
  `∀ x ∈ flatR, ctx.layout.shardOf (toBytes x.v) = ctx.own` (available as
  `RcptLink.bounded_prepared_native_routing`, given the BND balance premises `hb`/`hp`) and the
  link-indexed check is only required for every `o` with `indexOf ids own = some o`.
  (Side note for the lead: if `own ∉ shardIds` *and* a refund existed, `prepBody` would check no
  forwarding demand while the run fails `e.forwarded`; routing rules this out — no receipt can be
  applied then.)
* **Queue reads.** The qv AIR authenticates the three main reads on one tree
  (`Qv.Extract.assemble_native_queue_reads`: `v.Valid ∧ v.Reads t t t`, `t = queueTree … 0`).
  `reads_of_pre`: with `pre.wf`, `v.Reads pre pre pre ⇒ v.Reads pre mid (T (valsAt n))` (scheduler
  write touches only `keyBwState`; the ledger only account keys).

### Current top statement (`QvPre.mainRun_of_holdsP_pre`)

Hypotheses as `mainRun_of_holdsP_fwd` up to `ShaHyp`; then `∃ pc, prepClaim cb = .ok pc ∧ ∀ base Tf
pre mid so v, MainTrieLink … → pre.wf = true → v.Valid → v.Reads pre pre pre →
(∀ x ∈ flatR r.lists, shardOf (toBytes x.v) = own) → (∀ o, indexOf ids own = some o → ∀ k < n_L,
fwdDemand p.fwd (o·n_L + k) ≤ so.grant own ids[k]) → applyNewChunk … = .ok (mainOut …)`.

### qv from `HoldsP` — what is missing (found, not done)

`assemble_native_queue_reads` (instantiate at `tt = T_QV`, `KeyTrafficRepair.table` local by
`tableLocal_of_holdsP`; chains by `walk_chain_exists`, `parser_chain_exists` as in v3-link's
`LinkVBytes`) needs:
1. `C : RootChain`, `G : Walk3.WalkHyp …` — lane v3-link (`rootChain_of`, the trie link), and
   `pre = queueTree r.nodes r.values r.heads 0`, `pre.wf` (trie link).
2. `he`/`hb`/`ha` (empty / buffered values) — from `physical_empty_read` /
   `physical_buffered_read`.  **Mismatch:** their `hbalance` is a 4-sender `VBYTES` balance
   (qv + acct + akey = val), but in `nearAirV3` the codec also sends on `VBYTES`
   (`bal_users … [T_VAL, T_CODEC, T_ACCT, T_AKEY, T_QV]`).  The hypothesis as stated is not
   derivable; the lemmas need a codec-inclusive variant (codec streams are start-closed:
   v3-link `LinkVBytes.Codec.vrow_msg`, `codec_value`).  Not an AIR change — a proof-statement gap
   in `Qv/Extract/Physical*Read` (`physical_empty_native`, `physical_buffered_*`).
3. `hkey` / `hfinal` (KEYNIB / FINAL permutations with rcpt and walk), `hrequests`/`hc` (shard list
   `ss` from the parser chain), `hK` (`kPublic < 64`).

### Resume here

(1) codec-inclusive `physical_empty_read` / `physical_buffered_read` (new modules, reuse
`stream_isolate`, `physical_records_closed`, `byte_all_physical`, and v3-link's codec
start-closedness once on main); (2) the `hkey`/`hfinal`/`hrequests` balances from `HoldsP`;
(3) compose with `assemble_native_queue_reads` and `mainRun_of_holdsP_pre` once v3-link's
`RootChain`/`WalkHyp`/`shaHyp_holds` land on main.

## 2026-10-11 (session 2, round 3) — qv balances, TrieOk.set restriction, routing q-bound

* **`QvBal`** (new): `qv_hkey` / `qv_hfinal` — the `hkey` / `hfinal` permutations of
  `Qv.Extract.assemble_native_queue_reads` from `HoldsP` (KEYNIB and FINAL are used by walk (5),
  rcpt (16), qv (22) only; `qvRows tr pub b s` = the raw qv rows' traffic; `others` =
  `(rcptRecvs3 r.lists B_FINAL).map toFp`).  `qv_hK` — `kPublic < 64`
  (`Candidates.ProcessRepairQueuePublic.queue_count`).  The `hn : |flatR| ≤ W_AK = 8192` premise
  follows from `h.n = |flatR|` and `p.hdr.n ≤ 8192` (same module, first theorem) — not yet
  packaged.  `hrequests` / `hc` (QSH shard list) not done.
* **`TrieOk.set` restricted (lead / lane v3-link request, session 9 of their log):** now
  `∀ r < n, ∀ v, M.LenPres v → ∀ b, b.length = (v (M.slot r)).length → (T v).set key b = some (T (upd v slot b))`,
  `LenPres v := ∀ k, (v k).length = (M.valsAt 0 k).length`.  `RunModel.valsAt_lenPres`: every
  `valsAt r` is length-preserving (written slots are `Account.encode` of the same account up to
  `amount`, a `u128`).  `step` adapted; nothing else used `set`.  `get`/`find` unchanged.
* **Routing BND premises (item 3): blocked by an AIR decision.**  `bounded_prepared_native_routing`'s
  `hp : ∀ r ∈ boundaryRequests ls, ∃ e ∈ es, e.rec4 = r.1` comes from `bnd_lookup_provider`, which
  needs canonical requests (`boundaryRequests_canonical`, requiring `x.q < 128`).  The active
  `nearAirV3` receipt table is `RcptV3.tableR` (arithmetic repairs only); the `q < 128` bound is
  the **unadopted** `RoutingQCandidate` (`docs/zk-formal/ROUTING-Q-CANDIDATE.md`):
  `Rcpt/Link/RoutingAlias.lean` shows `q = 1796452668` aliases boundary address 2 (`65·q ≡ 2`).
  Without the candidate constraint, routing soundness (hence the routing fact replacing
  `own ∈ shardIds`, and receipt routing itself) is not derivable.  Counterexample sketch: the
  fixture `RoutingAlias.layout` (`[[122,122]]`, shards `[0,1]`, own `1`): receiver `[97,97]`
  routes natively to shard 0 but its lookups at address `65·aliasQ + 0 ≡ 2` read boundary row 2
  of the own interval — a receipt not owned by shard 1 passes the local routing constraints
  (`route_constraints_pass`).  **Lead decision needed**: adopt `RoutingQCandidate`.
* **Codec-inclusive physical reads (item 1): not started** (context).  Plan unchanged:
  `physical_empty_native` / `physical_buffered_*` with the 5-sender VBYTES balance; codec streams
  start-closed via v3-link's `LinkVBytes.Codec.vrow_msg` (merge `origin/lane/v3-link` when needed).
