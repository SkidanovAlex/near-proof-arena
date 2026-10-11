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
