# Lane `lane/v3-rcpt-sound` — receipt-side soundness (`executions`: the receipt core of `m.Valid.run`), log

Worktree `/data/illia/nearproof-wt/v3-rcpt-sound`, branch `lane/v3-rcpt-sound`, from main `c87a7cae`.
Modules: `zk-formal/ZkFormal/NearV3/Rcpt/Link/{RunSplit,ForwardSound,MemBal,Mem3,MemOf,RunModel,
NewChunk,RecChain,RecModel,PrepFwd,RcptCore,AcctSlots,GasPub,RcptHolds}.lean` (namespace
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

Done: (1) `hknd`, (3) `hgp`.  Next, in order: (2) `RecBytes` — `preB` (needs a value-record
byte lemma, the `Sha3.rec_bytes` argument for `valSends` + `VBYTES` balance acct→val), `burntB`
(`K_PEO` digest bytes), `ramtB` (refund body); (4) `hrf` (refund encoding identity); (5) the akey
half of `TrieOk.ak`; (6) `m.Valid.buffered` / qv reads (with the link lane); (7) `hsz`
(`Prep.fwd` vs scheduler grants, with the link lane).  Build: `HEAVY_MEM=12G taskset -c 8-15,24-31
/data/illia/nearproof-deps/bin/heavy lake build ZkFormal.NearV3.Rcpt.Link.RcptHolds`; audit
`lake env lean test/AuditRcptSound.lean`.
