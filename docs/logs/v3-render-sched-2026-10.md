# Lane v3-render-sched — scheduler/crypto-side aligned generators (2026-10)

Branch `lane/v3-render-sched`.  Goal: array-backed aligned trace generators with
completeness (`TableLocal` at the exact `nearAirV3` table + `TableTraffic` with the
soundness-side traffic + `log % 3 = 1`) for tables 0,1 (sha), 7 (ups), 8–10
(chacha/rng/shuf), 11–15 (scheduler), 23 (mrk), 24 (sort).

## 2026-10-11

* **sha (tables 0, 1)** — `ZkFormal/NearV3/Render/PaddedSha.lean`:
  `shaTraceAligned msgs` (`rowsTrace` of `mkTab` at `padLog22 (logOf rows)`) equals
  `ShaHeight.fixedTrace msgs log`; `sha_aligned_complete : Sha.MsgsOk msgs →
  TableLocal shaTable … ∧ TableTraffic shaTable.interactions … (shaBinTraffic msgs) ∧
  log % 3 = 1`.  Generic helpers `rowsTrace_mkTab_eq`, `mkTab_get_row_ge/col_ge`.
  Audit `test/AuditPaddedSha.lean`.
* **chacha/rng/shuf (tables 8–10)** — `ZkFormal/NearV3/Render/PaddedChacha.lean` (+ generic
  row-bounded congruence `Render/PaddedCongr.lean`: `tableLocal_congr_rows`,
  `tableTraffic_congr_rows`, `rowsTrace_cells`, `tableBusCount_off_bus`, `natMsgs`).
  The lane-`v3-chacha` completeness proofs were generalised in place to an explicit height:
  `Gen.traceAt entries L` (`honestTrace := traceAt _ honestLog`, all original statements kept),
  new `chacha_completeL`, `gen_completeL`, `shuffle_completeL`, `shuffle_trafficL`
  (`step_H`/`step_atL`, `count_*` with an `hL : rows ≤ 2^L` premise; shuffle also `L ≤ 20`).
  Theorems: `chacha_aligned_complete` (cap 21, rows ≤ 2^19), `chacha_aligned_complete22`
  (`maxLog := 22`, rows ≤ 2^22), `rng_aligned_complete` (cap 20, rows ≤ 2^19),
  `rng_aligned_complete22`, `shuf_aligned_complete` (cap 20, rows ≤ 2^19).
  **Cap finding:** under A9 (`W0`) the honest rows exceed `2^19` (lane_W0: chacha < 2^22,
  gen < 2^20, shuf < 2^22), so the aligned height is 22 for all three; the current caps
  21/20/20 cannot hold them. chacha/rng are ready at 22; shuffle completeness *and* soundness
  (`Shuffle.Contract`, `hH : height ≤ 2^20`) are 20-bit and need generalising first.
  Audit `test/AuditPaddedChacha.lean`.
