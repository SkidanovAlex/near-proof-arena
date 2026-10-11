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
* **mrk (table 23)** — `Render/PaddedMrk.lean`: `mrkTraceAligned os` (array-backed physical
  Merkle renderer over the native outcome levels, height `2^19`, cap 19 ≡ 1);
  `mrk_aligned_complete : 1 ≤ |os| ≤ 4481 → public count bytes → TableLocal MerklePublic.table …
  T_MRK ∧ TableTraffic … (mrkTraffic (aliasPublic pub) (generatedView …)) ∧ 19 % 3 = 1`.
  **Finding:** `os = []` is not covered — `nearAirV3` uses `MerklePublic.table` (nonempty
  tree); `MerkleEmpty.table` (width 60) is the repaired variant but is not in `nearAirV3`.
* **sort (table 24)** — `Render/PaddedSort.lean`: `sortTraceAligned S` at
  `padLog22 (logOf (32·|S|))`; `sort_aligned_complete` (cap 18, ≤ 2048 ids, height ≤ 16),
  `sort_aligned_complete19` (`maxLog := 19`, ≤ 8192 ids), receipt-level
  `sort_receipts_aligned_complete19` with traffic `sortTraffic (input rs)`.
  **Findings:** cap 18 must become 19 for the receipt bound; empty receipts are impossible
  for the old `Sort.constraints` in `nearAirV3` (`SortEmpty.old_empty_impossible`).
  Audit `test/AuditPaddedMrkSort.lean`.
* **scheduler cmp/mem (tables 15, 14)** — `Render/PaddedSched.lean`: `schedTraceAligned rows pad`
  (`rowsTrace 22` of the `natRow` arrays; the scheduler's shared physical clock `2^22`, cap 22
  ≡ 1) agrees with `Candidates/SchedHeight.trace`; `cmp_aligned_complete` (`CmpOk`, ≤ 2^22,
  traffic `Gen.Cmp.expected` on `B_SCMP`), `mem_aligned_complete` (`SegOk`, rows+1 ≤ 2^22,
  traffic `sopList`/`finList`/`cmpList`). Audit `test/AuditPaddedSched.lean`.
  **Open (codec 11, ssd 12, proc 13):** no completeness for the frozen tables:
  codec — local legality is only proved for the *repaired* candidate
  `ProcPriorCodecActual.table` (different constraints/interactions), not `Sched.Codec.table`;
  proc — `ProcComplete.proc_local` covers one run with `tau = 0` and no traffic theorem;
  ssd — `ProcScanDistPhases` has rows/counts but no `TableLocal ScanDist.table`.
* **ups (table 7)** — `Render/PaddedUps.lean`: `upsTraceAligned insts` at
  `padLog22 (logOf (R + 1))`; `ups_groupOk` assembles all ten constraint groups into
  `GroupOk … UpsV3.constraints`; `ups_render_local_at` / `ups_render_traffic_at` generalise
  M7d's natural-height lemmas to any height; `ups_aligned_complete : UpsRenderOk insts →
  TableLocal UpsV3.table … ∧ TableTraffic … (upsTraffic (viewOf … (segsOf insts))) ∧ log % 3 = 1`.
  `UpsRenderOk` = `UpsOk` + per-part `PartOk`/`FieldsOk`/`WindowOk`/`ByteInput`/`MemOk` (the
  explicit inputs of the group lemmas). **Open:** discharging those per-part inputs from native
  execution (`Ups/Native*`). Audit `test/AuditPaddedUps.lean`.
* **Verification:** `lake build ZkFormal.V3.Integration` passes (2190 jobs) with the in-place
  ChaCha generalisation and all new modules; `make pin-check` OK; audits
  `test/AuditPadded{Sha,Chacha,MrkSort,Sched,Ups}.lean` pass (axioms ⊆ {propext, Classical.choice,
  Quot.sound}). No sorry/axiom/native_decide.
* **Believed problems with frozen tables (not changed):** `Sched.Proc.table`'s key-rotation
  constraints (`Proc.cKey`) across an instance boundary (see `Candidates/ProcBoundaryRepair`,
  `ProcBoundaryLocal.away_key`) — only one run with `tau = 0` is proved complete;
  `Sched.Codec.table` — the only codec completeness is for the repaired
  `ProcPriorCodecActual.table`, which retires some `cKind`/`cRec` constraints.

## 2026-10-11 (package 2, from the lead: make 7–15, 23, 24 completable without weakening soundness)

* Merged `origin/integration/v3-20261011b` (fast-forward to 9bb1a295).
* **Task 1 — empty receipts.** D0a does not exclude zero receipts (`RelD0a` = RelD0 ∧ A1 A2
  canon0f A7–A11, none bounds the receipt count below), so the repaired tables are adopted:
  * `Assembly/NearAir.lean`: table 23 `MerkleEmpty.table` (width 60, maxLog 19), table 24
    `sortTableV3 := {SortEmpty.table with maxLog := 19}` (≤ 8192 ids need the aligned height 19).
  * Soundness: `LinkV3.mrkView` now gives `MrkWfE pub e v` (empty: public count 0 and zero root
    bytes, no traffic; else v1 `MrkWf`) with traffic `mrkTrafficE` on `MerkleEmpty.table`
    (`MerkleEmpty.empty_view` / `nonempty_view`); `V3Records` gains `mrkE : Bool`.
    `Candidates/SortEmptyCap.lean`: `sortV3_empty_or_old` (silent, or v1 `Sort.table` at cap 19),
    `v3_old_local`. `rawTables`/`busCount` sums updated.
  * Renders: `mrk_v3_aligned_complete` (`PaddedMrk.lean`, any `|os| ≤ 4481`, incl. empty; via the
    generic `arrTrace`/`arrTrace_transfer` in `PaddedCongr.lean`), `SortV3.sort_v3_aligned_complete`
    (`PaddedSort.lean`, any well-formed distinct receipts ≤ 8192, incl. none).
  * `nearAirV3_wf`, `nearAirV3_npOkPg` re-proved (kernel). **New size bound
    `nearV3_sizeMaxAligned = 6,330,945` B** at g = 2 (was 6,315,201); margin under 8 MiB after the
    1,295,017 B hint: 762,646 B. `v3MaxInner` updated (4 + 2,000,000 + 6,330,945 ≤ 8 MiB holds).
  * `fpBoundP nearAirV3` = 29,781,666,075 ≤ 2^36 = 68,719,476,736.
  * `lake build ZkFormal.V3.Integration` passes (2198 jobs).
* **Task 3 — ChaCha/rng/shuf at cap 22.** Budget first: `fpBoundP` of `nearAirV3` (`AirP.wf`,
  `busBudget = 2^36 = 68,719,476,736`): frozen 29,593,577,335; after task 1 29,781,666,075;
  with the three ChaCha caps at 22 **31,176,272,155** (with the candidate codec/proc repairs
  also swapped in, measured 31,290,959,735) — well under budget (the STATUS-V3-AIR §5 overflow
  concerned four *candidate families*, not `nearAirV3`). Done:
  * `Chacha.Table.table22`, `Rng.Table.table22`, `Shuffle.Table.table22` (`maxLog := 22`; the
    shared `maxLog` defs are unchanged so candidate families keep their budgets).
  * Soundness generalised: `Sound.ChLocal.log_le : log ≤ 22`; `Chacha/Link`, `Shuffle/Link`,
    `Statements.shuffle_sound` take the `table22` tables (`hlog : log ≤ 22`); shuffle soundness
    (`Shuffle/{Basic,Walk,Sound,Contract}`: row counter, `walkStart`, `shuffle_contract`) now for
    heights `≤ 2^22` (the bound only keeps the row counter below `p`); `ShufOwn` uses `table22`.
  * Completeness: shuffle `shuffle_completeL`/`trafficL` for `L ≤ 22`;
    `chacha_v3_aligned_complete`, `rng_v3_aligned_complete`, `shuf_aligned_complete22`.
  * `nearAirV3` tables 8–10 → `table22`; wf/npOkPg re-proved; size unchanged **6,330,945 B**
    (the aligned model already padded ChaCha to 2^22). Integration builds (2198 jobs);
    sched soundness modules (`Sound`, `GridLink`, `GrantSound`, `SoundFin`) rebuilt.
