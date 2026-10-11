# v3-render-rcpt lane log (receipt-side completeness)

Branch `lane/v3-render-rcpt` from main `fb3dec71`.  Goal: honest aligned trace generators
(`*TraceAligned`, `*_aligned_complete`) for the receipt-side tables of `nearAirV3`
(16 rcpt, 17 acct, 20 srcp, 21 size, 22 qv), pattern `Render/Padded.lean`.

## 2026-10-11

* **acct (17), size (21): aligned renders done** — `NearV3/Render/PaddedRcpt.lean`:
  `acct_aligned_complete` (cap 19), `size_aligned_complete` (cap 4), `acctV3Ok_wf`.
  Audit `test/AuditPaddedRcpt.lean`.
* Both honest heights exceed the natural caps (acct: 16·4481 = 71,696 rows > 2^16, so
  logOf = 17 → padLog22 = 19; size: 4 rows, 2 → 4).  Views generalized to a cap:
  `AcctV3Proof.*` take `TableLocal {AcctV3.table with maxLog := cap}` (+ `hcap : cap ≤ 22`
  where `height < P` is needed); `acctV3_view_at cap` with `AcctV3WfAt cap`;
  `size_view_at cap` (rows ≥ 3 are padding at any height ≥ 4: `padF`, `runF`).
  The old `acctV3_view`/`size_view` are the cap-17/cap-2 instances.
* Renders: `acctV3_render_local_at`/`_traffic_at`, `size_render_local_at`/`_traffic_at`
  (any height ≥ rows); old statements derived.
* **CAP CHANGE (separate commit):** `nearAirV3` table 17 `acctV3` → `maxLog 19`, table 21
  `sizeV3` → `maxLog 4` (`NearAir.lean`, `ExtractV3.lean` literal/lookups/locals,
  `ViewsV3.acctView` now `AcctV3WfAt 19`, `sizeView` via `size_view_at 4`).
  `nearAirV3_wf`, `nearAirV3_npOkPg` re-checked by kernel (NearAirCheck rebuilds).
  **Aligned size bound `nearV3_size`: 6,276,897 → 6,315,201 B** (+38,304) at auxGroup 2;
  margin under 8 MiB after the 1,295,017 B hint: 778,390 B.  `v3MaxInner` updated
  (`4 + 2,000,000 + 6,315,201 ≤ 8 MiB` still holds).  Full `ZkFormal.V3.Integration` builds.
* **srcp (20): aligned render done** — `NearV3/Render/PaddedSrcp.lean`:
  `srcp_aligned_complete` (hypothesis = the view's `SrcpWf bs`; cap 22 unchanged),
  `srcp_proofs_aligned_complete` (from the used source proofs, `ProofInputsOk`),
  `SrcpGen.table_local_at`, `SrcpGen.cell_high`.  `Srcp/ProofComplete` now reaches
  Integration through it.  Audit `test/AuditPaddedSrcp.lean`.
* **qv (22): aligned render done** — `NearV3/Render/PaddedQv.lean`:
  `qv_aligned_complete` for `KeyTrafficRepair.table` (the actual `nearAirV3` table 22, cap 22)
  on the existing honest mixed queue rows (`mixedTrace (plan pre v pres resolve) vs`), at
  `padLog22 (logOf qvRows)`.  New: the repaired-`KEYNIB` row/word traffic
  (`Walk.repairedKeyMessages`, `Walk.repairedKeyWordMessages`: zero-based nibbles, no START,
  END at `2·len` — the shape of `Qv.Extract.repairedKeyTraffic`), `repairedTraffic`,
  `mixedTrace_repaired_traffic`, `placed_words_traffic_is` (any interaction list), and
  table-index reindexing (`tableLocal_reindex`, `tableTraffic_reindex`).
  Hypothesis `QvOk`: `v.Valid`, records valid, `qvRows ≤ 2^22`, and the public implicit
  count (`kPublic`, pub 26..29) = `pres.length`.
  **Caveat:** there is no `qvV3` soundness view statement yet (not among the eleven views), so
  `repairedTraffic` is the honest-side record format; the view lane must target it (or a
  bridge must be proved).
