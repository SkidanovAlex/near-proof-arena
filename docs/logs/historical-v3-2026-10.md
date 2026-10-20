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

**Receipt-set ↔ gas attribution across the state-sync catch-up window.** All
machinery works and per-receipt gases match the chain exactly; what remains
is pinning WHICH receipt groups (and resumed postponed receipts) belong to
WHICH consuming chunk. Evidence collected 2026-10-17:

* nearcore `set_state_finalize` (chain_update.rs:430-530) applies, with the
  chunk, only receipt groups whose block height ≤ chunk.height_included()
  (`collect_receipts_from_response`), and runs with
  `RuntimeStorageConfig::new(root, /*record=*/true)` — the state-sync apply
  records the witness; block timestamp/gas price/random seed come from the
  chunk's own block (our replay must, and now does, match these fields).
* `ShardChunkHeaderInner` carries ONLY `prev_gas_used` — but RPC `chunk`
  header `gas_used` matches each chunk's OWN application gas in the verified
  cases below (937: 2,739,107,435,531 == receipt 8mjs… alone; 938:
  1,360,942,840,432 == receipt 8At5… alone), so RPC `gas_used` = OWN gas.
* Group→consumer evidence (new epoch, shard 13, sync_prev 220333936):
  * group `ASuMf19r` = {87jJG(223.18G ✓chain), BXfwnR(2,678.6G ✓chain),
    6SLwo(223.18G ✓chain), AZsePc(never executed 936–939 → postponed)} —
    our replay of exactly these four reproduced all three executed gases
    EXACTLY and postponed the fourth — yet chunk-936's header gas_used =
    669,547,687,500 = exactly 3 × 223,182,562,500 (three flat executions),
    which EXCLUDES BXfwnR's 2.679T whose outcome neardata lists under block
    936. So neardata's outcome↔block attribution and/or the header gas
    semantics still disagree by one notch somewhere.
  * group `4BvXAtnr` = {8mjs(→ executed at 937, gas == chunk-937 gas_used),
    8At5(→ executed at 938, gas == chunk-938 gas_used)} — one group's
    receipts spread over TWO consuming chunks via postponement.
* Next concrete steps: (1) read `get_incoming_receipts_for_shard` +
  `set_state_finalize_on_height` in full and instrument ONE chunk end-to-end
  against nearcore's own catch-up order; (2) treat RESUMED postponed
  receipts (state cols 04/05/06 + DELAYED col 07) as part of a chunk's
  execution set — chunk gas includes them without any incoming group;
  (3) re-check whether RPC `gas_used` is own-gas or prev-chunk gas per case
  (the two verified 937/938 cases say own-gas; the 936 case says otherwise —
  likely OUR receipt-set was the 937-set, shifted one group early).

The execution core is UNAFFECTED: given the correct receipt set + pre-state,
per-receipt outcomes (status + gas + postponement) reproduce the chain
exactly, which is the property succinct-prover fixtures need.

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
