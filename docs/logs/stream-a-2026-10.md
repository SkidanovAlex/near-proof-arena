# Stream A leftovers: succinct badge + measured mainnet mix — 2026-10-16

Lane `lane/stream-a` (worktree `/data/illia/nearproof-wt/stream-a`), based on
origin/main `f025caf62`. Closes the two HANDOVER §8 follow-ups that were not
owned by another lane:

1. **Succinct badge** (BENCHMARK_SPEC §17, CONTRACTS §11): designed, "not
   implemented" — now implemented additively end to end.
2. **Measured mainnet class weights + measured G_α rows** (STATUS-V3-D3 §4):
   "class weights ASSUMED until a mainnet replay measures them" — measured
   over a mainnet window with explicit, decidable observable predicates.

Neither touches a signed challenge, the frozen oracle, or any pinned file.
Signed ids are unchanged (`make pin-check`; `coverage.succinct` is serialized
only when present, and no draft on main defines it yet).

## 1. Succinct badge (contracts v1.8, additive)

* **Types** (`common/arena-types/src/coverage.rs`): `SuccinctSpec
  { max_proof_bytes, max_verify_ns, exponent_bound_ppm?, ucb_bound_ppm? }` on
  `CoverageSpec.succinct` (skip-if-none: ids unchanged); bounds default to
  §17's 0.1 / 0.25 (ppm). `SuccinctBadge` records the evaluation "per run".
* **Slope test**: OLS of `ln y` against `ln x` over per-run batch sums
  (x = Σ case gas, y = Σ proof bytes / Σ verify wall ns), 95% upper bound
  from Student-t (n−2 dof) via the inverse regularized incomplete beta
  (continued fraction; quantiles checked against the t table in tests).
* **Fail-closed**: thresholds violated, exponent > 0.1, UCB > 0.25, fewer
  than 4 gas-bearing runs, or gas spread under one doubling all deny the
  badge; every failed criterion is recorded in `denied`. Abstained classes
  are excluded (§17).
* **Measurement plumbing**: `Case.gas` (worker oracle) reads
  `meta.json` `features.fc_gas_burnt_for_function_call` — the chunk-v3
  oracle's own per-case function-call gas, the size axis of the `d3-maxgas`
  predicate. Nothing else is trusted as a gas axis. Per measured run the
  worker records `BatchSample.gas_total` → `ClassSession.measured_gas_runs`
  → `ClassMeasurement.gas_runs` (additive, default empty).
* **Control plane**: `normalize_benchmark` recomputes the badge from the
  measurements and the challenge thresholds (worker-sent evaluations are not
  trusted) into `BenchmarkResult.succinct`, which flows into the signed run
  report. `LeaderboardEntry.succinct` (recomputed on read for pre-v1.8 rows)
  feeds the board's SUCCINCT badge and the "succinct only" filter — server
  (`GET /v1/leaderboards/{id}?succinct_only=true`) and web UI checkbox.
* **Regenerated artifacts**: `common/schemas/*` (gen-schemas),
  `server/openapi.json` (UPDATE_OPENAPI=1), SDK types (python + ts), web
  generated types. `web/tests/drafts.test.tsx` had a stale tier-list
  expectation (`D0a`/`D1a` re-freeze) that failed on the base commit too;
  fixed to the current draft's tiers.
* **Tests**: arena-types (badge grant/deny/threshold/no-gas/abstained +
  additive serialization + t quantiles), worker, orchestrator, db, server,
  web (65 vitest incl. the filter interaction) — all pass; `cargo fmt`,
  `clippy -D warnings`, `make pin-check` clean (see §4).

Known limits, deliberately: thresholds are recorded but NO signed draft on
main sets `coverage.succinct` yet — that is a versioned-successor decision
(BENCHMARK_SPEC §17 keeps the badge display-only). Verify-time is judged on
the per-run batch sum (the quantity `cost_v1` pays; ≥ any single proof's
wall), a conservative reading of "max verify time". The gas axis exists only
where the oracle records function-call gas (chunk-v3 D3-family fixtures);
a fit over the other classes is impossible and denies the badge rather than
guessing an axis.

## 2. Measured mainnet mix (class weights + G_α rows)

Tool: `tools/mainnet-replay/replay.py` (stdlib only; neardata.xyz per-block
documents, throttled ≥ 0.3 s with 429 back-off, resumable `state.json`,
per-block disk cache). This is a **measurement, not an execution replay**:
classification needs only public observables; no trie nodes, no witness, no
oracle. CONTRACTS §11 keeps adoption for "a versioned successor with
MEASURED"; nothing on main changes the signed drafts.

* **Predicates** (documented analogues of `oracle/v3-d1/src/arena.rs
  class_of`, one record per chunk in `samples.jsonl`): transactions and tx
  outcomes (`receipt_execution_outcomes[tx_hash]`), applied receipts and
  their effective action kinds (Delegate unwrapped to the signed inner
  action — Delegate(FunctionCall) executes WASM), callbacks/yields
  (`output_data_receivers`, `is_promise_yield`, Data receipts), epoch
  boundaries (`epoch_id` change), validator updates (`validator_proposals`),
  delayed/buffered queues (`congestion_info.*_receipts_gas > 0`), implicit
  account creation (`state_changes` account_update on a 64-hex account id),
  and per-case function-call gas = Σ of the whole `metadata.gas_profile` of
  FunctionCall-receipt outcomes (the VM burnt gas wasm_gas + actions + ext —
  the quantity `oracle/v3-d3/src/d3.rs` sums into
  `fc_gas_burnt_for_function_call`; verified against that source), falling
  back to `outcome.gas_burnt` (overestimate) when a profile is absent.
* **Two honest views** in `weights.json` because the class predicates
  overlap across tiers (D0 ⊂ D1 ⊂ D2 ⊂ D3a) while weights partition:
  `predicate_frequencies` measures every class's predicate independently
  (Wilson 95% intervals); `weights_ppm` is the partition with precedence
  lowest tier first — receipts-only chunks without transactions are
  `d0-transfers` (they also satisfy `d1-receipts`, whose standalone
  frequency is in the predicate view), and a successor may re-split them by
  its own rule.
* **G_α rows** (`gas.json`): percentiles of per-chunk function-call gas
  against `NearSpecV3.D3.gAlpha` = 2²² · 822,756 = 3,450,888,781,824,
  feeding the STATUS-V3-D3 §4 checkpoint decision (re-fixing the value stays
  with the operator).

Results (`docs/e2e-results/mainnet-replay-2026-10/{weights,gas}.json`,
window heights 220,185,437–220,186,815 = 1,378 consecutive blocks, 13,770
chunks, 10 shards, PV 86, sampled 2026-10-16 with ~1 request/s):

* **Measured partition weights (ppm).** d0-quiet 248,366; d0-transfers
  78,649; d0-missing 15,541; d1-transfers 23,457; d1-mixed 31,373;
  d1-receipts 0 (receipts-only chunks are the same real chunks as
  d0-transfers; predicate frequency 1,173/13,770 = 85,186 ppm);
  d2-actions 1,670; d2-queues 145; d2-epoch 0; d3-calls 192,665;
  d3-callbacks 94,844; d3-nonwasm 4,212; d3-maxgas 309,078.
  Versus the ASSUMED weights (`spec/challenge-inputs/
  near-chunk-v3-weights.json`): the D3a family carries ≈ 60 % (assumed
  65 %), the quiet-chunk share is ≈ 25 % (assumed 2 %), plain-transfer
  traffic ≈ 5.5 % (assumed 10 %), D2 structural features ≈ 0.2 %
  (assumed 17 % — epoch boundaries are rare on a 13-block-minute window
  and queues nearly empty). Every count carries a Wilson 95% interval in
  the artifact; the successor's author re-splits overlapping predicates by
  its own rule.
* **Measured G_α rows.** Per-chunk function-call gas (5567 chunks with an
  exact profile sum, 652 with the gas_burnt overestimate, 7551 without
  function calls): median 0 (all chunks) / 2.45 Tgas (chunks with function
  calls) = 0.71 × G_α; p90 7.0 Tgas = 2.03 × G_α (FC chunks 13.4 Tgas =
  3.9 ×); p99 529 Tgas = 153 × G_α; max 541.6 Tgas = 156.9 × G_α.
  **30.9 % of all mainnet chunks have function-call gas ≥ G_α/2** (the
  `d3-maxgas` predicate). Today's `G_α = 3.45 Tgas` is far below busy-shard
  traffic — relevant for the D3a/1-Pgas scoping (`docs/zk-formal/
  V3-D3A-STUDY.md`) and for any successor's domain bounds; re-fixing the
  checkpoint stays with the operator (STATUS-V3-D3 §4).

Tool checks: `python3 tools/mainnet-replay/test_replay.py` (predicate/
partition/weights/percentile units + an end-to-end synthetic block with a
null-chunk shard, a Delegate(FunctionCall) receipt and profile gas).

## 3. What this does NOT do

* No challenge freeze/sign/register; no draft regeneration; no oracle or
  spec change; no measurement-rule change anywhere.
* The badge criteria bind nobody until a challenge sets `coverage.succinct`.
* The measured mix is a research artifact for the successor's author; class
  predicates remain generator-domain-relative (e.g. receipts-only chunks
  satisfy both `d0-transfers` and `d1-receipts`).

## 4. Verification

* `cargo fmt --all -- --check`; `cargo clippy --workspace --all-targets --
  -D warnings`; `cargo test -p arena-types -p arena-measure -p arena-worker
  -p arena-orchestrator -p arena-db -p arena-server`; `make pin-check`;
  web `pnpm typecheck`, 65 vitest, `pnpm build` (check-dist ok).
