# lane/historical-v3 — authentic exact-chunk v3 fixtures — 2026-10-16/17

Goal (user): fixtures from REAL mainnet blocks with different workloads and
gas, to test succinct provers beyond synthetic corpora. Approach: harvest a
sync-prev shard trie over P2P state-sync, replay the shard's chunk under the
pinned nearcore 2.13.4 `Runtime::apply`, anchor against the chain, and emit a
`historical-exact-*` fixture.

## Working (verified against the chain)

* **Tooling**: `oracle/historical` extended with three commands
  (`exec-chunk`, `chunk-of-header HEADER SHARD`, `get-key ROOT KEY PARTS...`,
  `config-view PV`); Python driver `tools/historical-v3/build_chunk.py`
  (resumable, missing-region harvest loop driven by trie-read failures, part
  bisection + widening).
* **P2P state-sync works for the live epoch**: sync point found
  (`harvest.py sync-point`; epoch start 220290734, sync_prev 220290737),
  header + parts fetched from peers (shard 13: 420 parts).
* **Classification of the sync chunk set** (tools/mainnet-replay classifier):
  that epoch gave d0-quiet ×2, d0-transfers, d3-calls, d3-maxgas ×6 — natural
  workload variety at one sync point.
* **Execution matches the chain exactly, per receipt** (shard 13 chunk
  8v6p4WK…, 4 incoming receipts, executed on 15 harvested parts ≈ 150 MB):
  * `GwX5…`-group: our gas **2,053,157,944,857** == chain 2,053,157,944,857
  * `3DGm…`: ours **1,828,989,654,482** == chain 1,828,989,654,482
  * `7ZyL…` (system refund): ours **223,182,562,500** == chain, SuccessValue('')
  * postponement reproduced (4 in → 3 outcomes + postponed state writes cols
    04/05/06 for xrp.omft.near).
* **Two root-caused pitfalls, fixed and documented**:
  1. neardata `chunk.receipts` is the shard's **outgoing** list (receipts the
     shard SENT, mostly to other shards); the true incoming set is the sync
     header's `incoming_receipts_proofs`, grouped by sending block. Routing
     sanity: shard 13 = V3-layout band ["wallet.ka", ∞) — receivers must be
     in-band (wrap.near/xrp.omft.near/zinzinmar2.tg ✓; intents.near is shard
     7 — the earlier "account doesn't exist" failure was this).
  2. Trie-node gas accounting: with `flat_storage_used = false` the replay
     charged per-node trie access the chain does not charge for flat-storage
     served reads (excess was exact multiples of `read_cached_trie_node`
     760 GGas: +132 and +276). `Trie::from_recorded_storage(..., true)`
     simulates flat-storage costs; per-receipt gases then match exactly.
  * Runtime parameters verified identical to mainnet
    (`config-view 86` vs `EXPERIMENTAL_protocol_config.runtime_config`:
    223 leaves, **0 diffs**).

## Open (next session, one focused item)

**Receipt-set ↔ gas-header semantics of the state-sync header.** The header
groups incoming receipts by sending block ("for B_sync and B_prev_chunk" —
here: FYkg39… = sync block 738, Lcv5TeRD… = sync_prev 737). Our replay of all
4 receipts costs Σ 4,105,330,161,839 gas, and each per-receipt gas equals an
on-chain outcome — but chunk-737's header says `gas_used` 1,825,297,923,553
and chunk-738's says 223,182,562,500, so the 4 receipts evidently split
across the chunks of 737 and 738 (the header carries receipts for BOTH
because a state-syncing node catches up through both). Decode needed:
nearcore `chain/chain/src/state_sync.rs` + `get_incoming_receipts_for_shard`
— which consuming chunk each `ReceiptProofResponse` group belongs to
(likely: receipts for the chunk included in block X come from chunks included
in blocks (prev_chunk.height_included, X]); then per-chunk Σ gas must equal
that chunk's header `gas_used`, and the post-state-root anchor follows.
The measured gases suggest: chunk-737 gas 1,825,297,923,553 = ?

## Artifacts (this session, untracked cache regenerable)

* `/tmp` harvest caches (parts-s13 ≈ 21 parts, spblocks) — regenerable.
* `cases/exact-s13-h220290737/` (in /tmp): context.json, chunk_exec.json,
  apply_witness.bin (93–144 recorded nodes, hash-linked to
  `CyMSdP6iiyegr3PXgQaCoBLav9i1TPvhxPXrMW6qX5Cv`).

## Rules kept

oracle/v3*, oracle/fixtures, signed challenges, pinned files: untouched.
`make pin-check` still passes on the lane base. The vendored nearcore is a
read-only symlink to `/data/illia/nearproof-deps/nearcore` (exact pin
44f7ae6c), recreated per worktree (`oracle/vendor/nearcore`).
