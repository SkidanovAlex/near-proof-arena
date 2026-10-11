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
