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
* **Task 4 — ups from native execution.** `Render/PaddedUpsNative.lean`:
  `UpsGen.upsRenderOk_of_native` / `ups_native_aligned_complete`: for native instance data
  (`UpsNativeData`: forest root at τ, native `traceUpsert` run along `[0,15]`, native part
  encoding) all per-part inputs come from `nativeInstance_partInputs` and `InstOk` from
  `nativeInstance_semantic_ok`. Remaining explicit premises (`UpsNativeOk`): root lookup and
  upsert success, `wf` tree, `1 ≤ |v| < 2^24`, path depth ≤ 400, encoding success, per-part
  `qhk`/`phk < 2^22`, the authenticated walk `WalkOkU`; table: ≥ 1 instance, `R + 1 ≤ 2^22`.
* **Task 2 — codec/proc/ssd: NOT adopted (would weaken soundness).** Survey: the most complete
  repair, `Candidates/ProcPriorProcessRepairedFamily` (codec `ProcPriorCodecActual`, ssd with
  4-field `B_SDG`, proc `ProcBoundaryRepair`, comparator routed to bus 40), has **no** soundness
  theorem comparable to `schedCore_sound''`: only the shared comparator
  (`ProcPriorProcessRepairedSound.sound`), `ProcessRepairInterface.repaired` (projected locals),
  `ProcSound/Bridge.physical_instance` (Proc.Inst from the repaired proc table) and row-level
  codec lemmas (`ProcPriorCodecSound*`). The progress log (v3-progress-log, l. 258) records that
  legacy `schedCore_sound` cannot be reused for the repaired codec (retired prebit decomposition,
  new `hasC`, prior canonicalisation, `CodecValOwn`). Completeness exists for repaired codec
  (`ProcCodecNativeConcatLocal`, `ProcCodecConcatTraffic`), repaired proc (`prior_process_table`,
  B_SCMP traffic only), and ssd only B_SCMP traffic (no `TableLocal ScanDist.table`).

## 2026-10-11 (package 3: Task 2 in full)

* Merged `origin/lane/v3-a11` (A7 measure, f65d9ece) and integration b; **real rebuild** after
  the lead's build-cache cleanup: `ZkFormal.V3.Integration` 2199 jobs OK; all audits re-run OK.
* **Analysis (scheduler repairs).** Only the process table needs a change for completeness:
  the frozen key rotation ties consecutive instances' seeds when a key block is followed by the
  next instance's key block (an instance with no rounds; `ProcEmptyBoundaryRegression`). The
  codec repair family (`ProcPriorCodecActual`, SDG cut, bus 69→40) targets non-canonical priors,
  which `checkD0a` rejects (`canon0f`; frozen `SoundPre.codec_prevCanon`), so codec and ssd stay
  frozen (completeness there is proof work, not a table change).
* **Proc repair adopted with soundness re-proved.** `Sched/Tables/Proc.lean`: `rotationB`,
  `cKeyB`, `constraintsB`, `tableB` (= `ProcBoundaryRepair.table`). The process view chain
  (`Sched/View/Proc*.lean`, `Sched/Link/ProcRows.lean`) now states `PLocal` over `constraintsB`
  (bodies from the kernel-checked `Candidates/ProcSound` copy; `key_reg`/`proc_keys` carry the
  boundary hypothesis); the Link layer's `SchedOwn.tp_tab` and all `htab` premises name
  `Proc.tableB`. `schedCore_sound`/`'`/`''` and `SoundFin` rebuild unchanged in conclusion.
  `nearAirV3` table 13 = `Proc.tableB` (`Sched.Budget.schedTables` too); `nearAirV3_wf`/`npOkPg`
  and `nearV3_size` (6,330,945 B, shapes identical) re-checked. All 22 reverse dependents of
  `Sched/View`/`Sched/Link` (candidates included) build. Audit `test/AuditSchedProcRepair.lean`.
* **Proc completeness over all runs** — `Render/RowTraffic.lean` (generic: for current-row-only
  interactions the exact traffic of a row-function table is the trace-free `rowsTraffic is cell L t
  pub`; `rowFn_traffic`) and `Render/PaddedProc.lean`: `proc_v3_aligned_complete` —
  `TableLocal Proc.tableB` + `TableTraffic` (all buses) + `22 % 3 = 1` for the concatenated native
  runs (`ActualRun.run I τ = .ok R`, τ consecutive from 0, capacity), via
  `ProcActualNativeComplete.list_local` (`ProcBoundaryRepair.table = Proc.tableB` by `rfl`).
* **Open:** codec (frozen `Codec.table`, 239 constraints, width 91) and ssd (`ScanDist.table`,
  251 constraints, width 119) `TableLocal` over all runs — no existing proof for the frozen tables
  (the repaired-codec proofs `ProcCodecNativeConcatLocal` are for `ProcPriorCodecActual`); once
  local legality exists, their traffic follows from `rowFn_traffic` if their interactions are
  current-row-only. Task 3 (bus balance) not started.

## 2026-10-11 (package 4)

* Merged integration b (rcpt `tableR`, srcp `tableD`); conflict in the `NearAir` header comment only.
  Integration builds (2845 jobs).
* **RIDS coordination:** `SortV3.sort_v3_accepted` (`PaddedSort.lean`): for an accepted witness
  (`walkD0`, `decodeW`, `decodeStateWitness`, `checkD0a B0`, `NativeValid`) and receipt lists with
  `lists.flatten.map Input.receipt = appliedReceipts k w`, the sort render's honest input is exactly
  `lists.flatten.map Input.receipt` and it emits `sortTraffic (NativeSortIds.input (that list))` —
  no mismatch; well-formedness, distinct ids and `≤ 8192` come from acceptance.
* **`TableRenderV3` packaging** — `Render/BundleSched.lean`: `shaRenderV3` (0, 1), `upsRenderV3` (7,
  native data), `chachaRenderV3` (8), `rngRenderV3` (9), `shufRenderV3` (10), `procRenderV3` (13,
  native runs), `memRenderV3` (14), `cmpRenderV3` (15), `mrkRenderV3` (23, empty tree included),
  `sortRenderV3` (24, from `checkD0a B0` acceptance, RIDS = receipt lane's list). Each takes the
  render's explicit honest-input premises. Audit `test/AuditBundleSched.lean`.
* **Proc from acceptance:** `procRender_accepted` — `checkD0a B0` acceptance (`prepD0`, `walkD0`,
  `decodeW`) gives the native blocks of `accepted_prior_core`, whose runs discharge every premise of
  `procRenderV3` (native `ActualRun.run`, `τ = index`, capacity `prior_run_capacities`).

## 2026-10-11 (package 5, fresh session)

* **ssd (table 12, frozen `ScanDist.table`) — DONE over all runs.** `TableLocal` + exact traffic +
  `22 % 3 = 1` for the honest merged table of an accepted witness, and the `TableRenderV3` instance:
  * `Render/SsdShardLocal.lean`: `SsdShard.physical` — the missing shard-row local lemma (kind frame,
    `e1` index test, `kp`/side/grid transitions; `Next` = next-row facts), on top of the existing
    `ProcDistShard{Average,Output,Grid,Range,Bools}` pieces.
  * `Render/SsdDesc.lean`: row descriptors `Ssd.Desc` (param / request row / shard / header / cell),
    `Desc.Valid` (the row lemma's premises), `Desc.Adj` (admissible successors), `FirstOk`, `Final`;
    `local_at`: every constraint on a descriptor row with an admissible successor (dispatches to
    `ProcScanParamPhysical`, `ProcScanRequestNativeLocal`, `SsdShard.physical`,
    `ProcDistHeaderPhysical`, `ProcDistCellLocal`).
  * `Render/SsdTable.lean`: `bits_of_constraints` (multiplicities are bits wherever the constraints
    hold: one-hot kinds, `fQ`/`re` gated by `kS`); `table_local` (descriptor chain, `< 2^22` rows →
    `TableLocal ScanDist.table (SchedHeight.trace … distPad)`).
  * `Render/SsdChain.lean` (chain append/flatten/range), `Render/SsdScanGen.lean` (`scan_block`:
    `Gen.Scan.rows R` = descriptors; `conv_indexed`: native converted requests are numbered
    `cid = 0,1,…`), `Render/SsdDistGen.lean` (`dist_block`: `distRows I R` = descriptors via loop
    invariants on the generator's sender/receiver endpoints; the allowed-cell check gives `0 < n1,n2`).
  * `Render/PaddedSsd.lean`: `ssd_descs`, `ssd_v3_aligned_complete hp bs hc` (for `PriorCore p B bs`;
    trace `ProcScanDistPhases.trace bs`, traffic `rowsTraffic ScanDist.table.interactions (ssdCell bs)
    22 t pub`, interactions current-row-only by `decide +kernel`).
  * `Render/BundleSched.lean`: `ssdRenderV3`, `ssdRender_accepted` (from `checkD0a B0` acceptance via
    `accepted_prior_core`). Audit `test/AuditPaddedSsd.lean` (axioms ⊆ {propext, Classical.choice,
    Quot.sound}). `ZkFormal.V3.Integration` builds; `make pin-check` OK. Commits bb7c21f3, 4bd67ffa,
    11fe0d18.
* **Tables 12–15 from acceptance on one block list** — `Render/SchedAccepted.lean`:
  `sched_renders_accepted`: `checkD0a B0` acceptance gives one `bs` (`PriorCore p B0 bs` with the
  codec-output comparator facts, from `accepted_run_codec_comparisons`) and renders R12 (ssd), R13 (proc,
  all runs), R14 (`memAllRenderV3`: `Mem.table` over all runs, `prior_memory_table` + row traffic of
  `MemConcatCells.trace`), R15 (`cmpRenderV3` over `ProcNativeOldComparisonCapacity.requests bs` = every
  run's memory/process comparisons ++ codec-output comparisons ++ distribute comparisons, all `CmpOk`,
  ≤ 2,936,832), with traces/traffics named for the balances. Audit `test/AuditSchedAccepted.lean`.
  Commit 2a9b8a3b.
* **Table 23 from acceptance** — `Render/MrkAccepted.lean`: `mrk_premises_accepted` (native outcomes
  `m.result.outcomes`, hint `nativeHint k w m`: ≤ 4481 outcomes via A1, public count bytes = outcome
  count via `p.hdr.n = |appliedReceipts|` and `applyNewChunk_outcomes`, public root bytes =
  `outcomeRoot` via `prepD0_native_outcomeRoot`), `mrkRender_accepted`. Audit
  `test/AuditMrkAccepted.lean`. Commit 35c3c530.
* Verification: `ZkFormal.V3.Integration` builds (3761 jobs); lane audits AuditPaddedSsd,
  AuditSchedAccepted, AuditMrkAccepted, AuditBundleSched, AuditPaddedSched, AuditSchedProcRepair pass;
  `make pin-check` OK; no sorry/axiom/native_decide/implemented_by.

### Codec (table 11, frozen `Sched.Codec.table`) — open; analysis and plan

* **No obstruction found** for honest D0a witnesses: canon0f fixes the prior links to the layout
  (`layoutLinks k.L`, one layout for every run, so all instances share the ids the SDL chain carries);
  `State.decode` rejects trailing bytes, so the pre bytes are exactly `State.encode prev`; the allowance
  pass (`a1 = bigR ? MA : (cb ? MA : apR + fair)`, `a2 = a1 − al·base`) matches `newAllowance`
  (`fair ≥ base` for every `n ≥ 1` under PV86, so the subtraction is exact); post allowances
  `afin ≤ MA < 2^24` fit the three low bytes.
* **Size of the job.** Nothing proves frozen-codec row legality. The repaired family's proofs
  (`ProcPriorCodecActual`, ~276 modules) cover rows that agree with the frozen ones on header, hash and
  `sha256(all_shards)` rows (`ProcPriorCodecAssignments.headerRow/hashRow/ashRow` are the frozen rows,
  and the frozen-only constraints there are the retired pre-bit ones, which hold), but **record rows
  differ** (repaired: prior allowance bytes 0, `prbit` = id-byte register, `srcC/hasC/useC` = sender /
  receiver indices, `nzb/ig2/ib` start extras; frozen: real prior bytes, pre bits, source map).
* **Plan for the successor** (mirrors the ssd work, which is the template):
  1. `Render/CodecRows.lean`: frozen record row `recRow` (copy of `Gen.codecRows`' record row:
     `inst ++ [kR, pos, bpost, bpre, vbg, kidx, klo, khi, fS/fR/fA, g, ig7, e7, ikl, ekl] ++ pb bpo ++
     qb bpr ++ extra`) with explicit accumulators (`ap = a0 % 256^min(gg,3)`, `apost`, `big`, `cb`).
  2. Row lemmas: header/hash/ash rows reuse `ProcPriorCodecHeaderFullKind`, `ProcPriorCodecHeaderFlow`,
     `ProcPriorCodecSideRecord`, `ProcCodecGeneratedTrailer` plus the retired constraints; record rows:
     24 kinds `(f, gg)`, most constraints integer-exact (`zev = 0`, big `simp` as in
     `ProcScanParamLocal.constraints`); the **modular** ones need `Fp`: the six `isZ` inverse tests
     (`ig7, ig2, ikl, ihp, isj, itz`), `nzb = bpre·ib`, and `wt` (`256^gg mod P` for `gg ≥ 4`).
  3. Descriptors + `table_local` exactly as `Ssd.Desc`/`Ssd.table_local` (codec trace
     `SchedHeight.trace … codecPad`, row 0 = instance-0 header with `kF`).
  4. From acceptance: per `NativeBlock` (`b.prior.isSome`, `b.vid`, `b.grants`, `b.forwarded`,
     `ProcPreparedSequence.input b.pub b.old`); the generator checks (`a2 == R.a2[kk]`,
     `ft ≤ gfin + gb`) are the repaired generator's too (it succeeds: `NativeBlock.Valid`), modulo
     `a0Canon[srcOf kk] = ProcActualInput.allowances[kk]` for canonical priors (to prove).
  5. Note for the balances: R15 currently takes the repaired codec's comparisons (`b.output.cmps`); the
     frozen codec sends `(apR + fair, MA, cb)` and `(gfin + gb, ft, 1)` — the same values once (4) holds.

### Open (this lane), in order
1. Codec (table 11): `TableLocal Sched.Codec.table` + traffic over all runs (plan above).
2. Bus balances (scheduler 40–62, SCMP, ChaCha lane) on the named traffics of R12–R15 (+ codec, ChaCha).
3. Premises from acceptance still explicit: sha (0, 1; message list shared with the trie lane), ups (7;
   `UpsNativeOk` per scheduler upsert — needs the trie forest root at τ), ChaCha/rng/shuffle (8–10;
   honest inputs `Lane.chachaReqs/genCalls/shufInsts` of the native runs: key/positions from the run,
   draws from `replayShuffle` success (`ProcShuffleReplay`), row bounds need A9 ↔ `Σ R.kfin`).
