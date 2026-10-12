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

* **`B_SCMP` reduced to the codec** — `Render/SchedScmp.lean`: `scmp_balance_core`: on the renders of
  `sched_renders_accepted`, mem (14) + proc (13) + ssd (12) comparison sends + the codec outputs'
  comparisons `(bs.flatMap (·.output.cmps)).map cmpMsg` = the comparator's (15) receives. Remaining for
  SCMP: the codec table's sends equal that list. Audit `test/AuditSchedScmp.lean`. Commit 76a9c6c7.

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

## 2026-10-11 (package 6, codec under way)

* Merged `origin/integration/v3-20261012`; table 7 is now `upsA7` (trie lane), so the pre-A7
  `upsRenderV3` was dropped from `Render/BundleSched.lean` (commit 23c49506).
* **Codec (table 11, frozen `Sched.Codec.table`) — row layer in progress.** Approach = the ssd template,
  but the honest rows are defined directly as assignment lists (no generator equality needed):
  * `Render/CodecDefs.lean`: `Inst` (τ, n, N, pres, vid, base, fair), `Rec` (per link: srcS, hasC, useC,
    al, a0s, gb, afin, gfin, ft, iklv), row assignments `hdrA`, `recA` (bytes `bpo/bpr` and the
    allowance accumulators `apv/apostv/bigv` as parameters), `hashA`, `ashA`; `modE` (the 8 constraints
    that hold only mod P); the `codec_int` macro (integer pass: every other constraint, `zev = 0`).
  * **Performance lessons (important for whoever continues):** (1) never let `simp` see a field inverse
    of a symbolic value — inverse cells are `inv` (`@[irreducible]` wrapper of `finv`), and the link
    inverse is a `Rec` field (`iklv`), otherwise simp/whnf blows memory (OOM at 14 G); (2) the full
    `simp` set on record rows also explodes — `codec_int` uses a curated `simp only` list with explicit
    `Nat.reduce*` simprocs and `reg_i` literal lemmas, then small closers; (3) keep `apRv/bigRv/cbv/a1v/MA`
    folded (their decidability instances do not rewrite), with `cbv_le`, `bigRv_le`, `a1v_def` facts.
  * **Integer pass done for every row kind (compiled, audited `test/AuditCodecRows.lean`):**
    `CodecHeader.hdr_int` (header p < 4), `CodecRecInt.rec_in_int` (21 record kinds inside a field,
    ~21 min), `CodecEndInt` (`rec_fend_int` field end, `rec_end_int` record end → next record,
    `rec_last_int` last record → hash 0, `hdr_last_int` header 4 → record 0, `hash_int`, `hash_last_int`,
    `ash_int`, `ash_last_int` → next instance header, `ash_pad_int` → padding). The forwarding cells of
    the record end are unconditional, multiplied by `zt0 I = [τ = 0]`.
    Modular constraints over Fp: `CodecMod` (`isZ_mod`, `nzb_mod`, `wt_mod`, `wt_off`, `gate_zero`).
    Each integer lemma states its explicit row premises (byte bounds, `bpr = pres·bpo` on id bytes,
    accumulator recurrences, `apost = afin` and `al·base ≤ a1` at the record end, `ft < 2^24`,
    `hasC = false → apR = bigR = 0`).
  * Next: per-kind modular instantiations; trace-level `local_at` per kind (cells `< P`); codec row
    descriptors + `table_local` (copy of `Ssd.table_local` with `codecPad`); generation from the native
    blocks (`NativeBlock`: τ, `prior.isSome`, `vid`, `grants`, `forwarded`; prior allowances via the
    canonical prior); the traffic facts the trie lane needs (lead, 2026-10-11): S0F receives exactly one
    `[τ, pres, vid]` per τ (pres = old BwState value present; vid = its N_D value id, else 0); SPLEN
    sends `[τ, 37 + 24·n²]` per τ; SPOST sends `[τ, p, u.value[p]]` for every p; sanity SHA jobs (BYTES)
    are the codec's — the honest inputs must be the same native choice as the trie lane's `UpsSha`
    (`TrieUpsSched.lean`, `trie_all_of`).

## 2026-10-12 (package 7, fresh session: codec table 11 assembled)

* Merged `origin/lane/v3-trie-complete` (3834ac8e: `TrieSide.trie_side`). `ZkFormal.V3.Integration` builds
  (4290 jobs, 14m38s); `make pin-check` OK.
* **Performance finding (important):** `simp` with a `rfl`-proved `lookup_cons` (a dsimp lemma) makes the
  *kernel* unfold symbolic field inverses (`inv (fsub p 4)`; `inv` being `@[irreducible]` does not help the
  kernel) → OOM at 14 G even for `lookup [(44, inv (fsub p 4))] 44 0 = inv (fsub p 4)`. Fix: `lookup_cons` /
  `lookup_nil` are proved propositionally (`simp only [lookup, List.foldl_cons]`), never by `rfl`
  (`Render/CodecCells.lean`). With that, cell evaluation of all row kinds is fast. Also: building
  CodecHeader/EndInt/RecInt in one `lake build` exceeds 14 G (parallel); build them one at a time
  (6 min / 12.7 min / 26.5 min).
* **Codec (table 11, frozen `Sched.Codec.table`) — TableLocal + exact traffic over honest blocks: DONE.**
  * `Render/CodecCells.lean`: `lookup_ite/cons/nil/app`, `lookup_bound`, `gd_setAll`, `keys_{hdrA,recA,hashA,ashA}`.
  * `Render/CodecRowMod.lean`: `cdc_cell` (cell evaluation), `modE_cases`, `tz_mod`, **`hdr_mod`, `rec_mod`,
    `hash_mod`, `ash_mod`** (the eight `modE` constraints over `Fp` on each row kind, symbolic `f, gg`),
    `row_local` (integer pass + modular pass ⇒ every constraint).
  * `Render/CodecDesc.lean`: `Desc` (`hdr`/`record`/`hash`/`ash`), `InstOk`, `RecOk`, `Desc.Valid` (cells `< P` +
    the row lemmas' premises), `Desc.Adj` (exactly the integer-pass successor premises), `Final`, `FirstOk`;
    **`local_at`** (all 239 constraints on a descriptor row), **`mult_bits`** (multiplicities are bits).
  * `Render/CodecTable.lean`: `codecTrace ds`, `cur_desc`, **`table_local`** (descriptor chain, `< 2^22` rows ⇒
    `TableLocal Sched.Codec.table`; padding via `CodecPadding.physical_constraints/physical_mult_zero`).
    `Render/CodecChain.lean`: chain append/flatten/range for codec descriptors, `table_local_chain`.
  * `Render/CodecVals.lean`: `hdr_vals`, `rec_vals`, `hash_vals`, `ash_vals` (all cells `< P` from explicit bounds).
  * `Render/CodecGen.lean`: `Blk` (instance constants, ids, prior allowances `a0`, per-link `recs`, digest,
    previous hash, `sha256(all_shards)`), `Blk.descs` (5 + 24·N + 64 rows; bytes and allowance accumulators in
    closed form = frozen `Gen.codecRows`), `Blk.Ok` (explicit premises), `descs_chain`, `descs_valid`,
    `descs_length`, `allDescs`, **`allDescs_local`**.
  * `Render/CodecRender.lean`: `codecCell`, `codec_currentOnly` (`decide +kernel`), **`codec_blocks_complete`**
    (TableLocal + `TableTraffic … (rowsTraffic Codec.table.interactions (codecCell Bs) 22 t pub)` + `22 % 3 = 1`),
    **`codecRenderV3 pub Bs hok hcap : TableRenderV3 pub 11`**.
  * `Render/CodecNative.lean`: `blkOf b` (the frozen block of a `NativeBlock`, same native choice as
    `PriorCore`/proc/ssd/mem/cmp: `a0 := a0Canon`, source map `srcOf`, grants `b.grants`, final link values
    `R.segs`, instance-0 demand `demand b.forwarded`, sanity bytes), `base_le_fair` (PV86, `decide`),
    **`blkOf_ok`** (`Blk.Ok (blkOf b)` from the run, `SchedPubOk`, `n ≤ 64`, τ < 32 and `NatRes b`),
    `blocks_length`, **`codec_accepted`**: `checkD0a B0` acceptance ⇒ `∃ bs, PriorCore p B0 bs ∧ ((∀ b ∈ bs,
    NatRes b) → ∃ R : TableRenderV3 pub 11, R.tr = codecTrace (allDescs (bs.map blkOf)) ∧ R.tf = rowsTraffic …)`.
  * Audit `test/AuditCodecTable.lean` (axioms ⊆ {propext, Classical.choice, Quot.sound}). Commits ac76f86c, 8dcf96b1.
  * `ZkFormal.V3.Integration` builds (4292 jobs) with all codec modules; `make pin-check` OK.

### Open (this lane), exact
1. `NatRes b` for every `b` of `PriorCore p B0 bs` (`Render/CodecNative.lean`): `b.vid < P`;
   `∀ kk < n², b.grants[kk]! < 2^26`; `∀ kk < n², (b.run.segs.getD kk default).wfin < 2^26`;
   `b.run.tau = 0 → ∀ kk < n², demand b.forwarded kk < 2^24`. Sources: `ProcPriorCodecGrantCap.native`
   (`wfin + gd[k] ≤ 4.5M`) and `ProcPriorCodecForwardRange.native` need the block's distribution witness
   (`distributeEv … = .ok (b.grants, …)`) and its process prefix, which `PriorCore` does not export;
   `vid` bound from `priorValueId` (forest size).
2. Codec traffic (task 2) — started: `Render/CodecTraffic.lean`: `pad_rowTraffic` (padding rows carry no
   messages), **`rows_traffic`** (`rowsTrafficFp Codec.table.interactions (codecCell Bs) 22 t pub b s` = the
   descriptor rows' `rowTraffic` on `dRow (allDescs Bs)[r]! r`), and the first per-kind closed form
   **`hdr_s0f`** (`S0F` recv on header row `p`: `[[τ, b2n pres, vid]]` iff `p = 0`) — the template for the
   rest (bus constants: use `Sched.B_*`, which differ syntactically from `ZkFormal.NearV3.B_*`). Remaining:
   per-bus message lists of `rowsTraffic Codec.table.interactions
   (codecCell (bs.map blkOf)) 22 11 pub` (S0F `[τ, pres, vid]` from `hdr _ 0`; SPLEN `[τ, 37 + 24·n²]`; SPOST
   `[τ, pos, bpost]` on header/record/hash rows = `stateBytes ids afin digest`; BYTES `[11+16τ, j, pres·hpre_j]`,
   `[11+16τ, 32+j, ash_j]`; DIGEST `[11+16τ, 64, digest]`). Plan: (a) padding rows have empty `rowTraffic`;
   (b) `rowFn (codecCell Bs) 22 r = rowFn (lookup ds[r].asg) 22 r` (`natCell_desc`); (c) per-kind closed forms by
   `cdc_cell`. Pinning `us`: the natural choice is `us := bs.map NativeBlock.witness` (`native_block_digests`
   already shows the repaired rows' digests = `expectedDigests [schedulerSanityJob τ b.witness]`); equating it
   with the trie lane's `us` needs that both are `schedulerUpsertWitness ctx pre` of the same `(ctx, pre)` list
   (the extractor is a function, so uniqueness reduces to the same per-τ pre-tries/contexts).
   B_SCMP: the frozen codec compares `(apR + fair, MA, cb)` with `apR` from `a0Canon[srcOf kk]`, the repaired
   (R15 today) uses `ProcActualInput.allowances[kk]`; equal for canonical priors with distinct shard ids (to prove;
   `ProcPreviousStateRegression.allowance_mismatch` is the non-canonical counterexample).
3. Scheduler buses 40–62, ChaCha-lane buses, packaging theorem (tasks 3, 4): not started.

### Lead's package 8 (received end of session 7) — findings before stopping (context low)

* **(3) B_SCMP / distinct shard ids — distinctness is NOT needed.** The spec does not enforce distinct
  `shardIds` (A12 is only `|boundaries| + 1 = |shardIds|`; no Nodup check found in `spec/lean/v3`). But
  `Sched/Spec/CanonDup.allow0_src` already proves, for ANY id list (duplicates included), that the native fold
  `links.foldl (allowStep-style indexOf update)` over the layout-canonical links
  `(range n²).map (l ↦ ⟨ids[l/n], ids[l%n], a l⟩)` equals `srcArr ids a` (record `srcOf ids l`, last wins; 0 when
  none). `ProcActualInput.allowStep` is that same update, so for a canon0f prior (`links.map (s,r) = layoutLinks L`,
  hence `|links| = n²` and `a0Canon = links.map allowance`): `ProcActualInput.allowances ids prev = a0Src ids prev`,
  i.e. `allowances[kk] = (match srcOf ids kk with | some k' => a0Canon[k'] | none => 0)` = the frozen codec's `a0s`.
  Remaining proof: `layoutLinks L = (range n²).map (l ↦ (ids[l/n], ids[l%n]))` (flatMap/map index identity) and
  the reshaping of `prev.links` into `allow0_src`'s form. (`ProcPreviousStateRegression.allowance_mismatch` is a
  non-canonical prior, consistent with this.)
* **(1) NatRes — where the witnesses live.** `ProcPriorCodecGrantCap.native` / `ProcPriorCodecForwardRange.native`
  need, per block, `ProcActualPrefix.runPrefix (input sp prev) = .ok (cv,st,rs,ev)` and
  `distributeEv n sp.allowed st.sb st.rb lp.cntS lp.cntR = .ok (gd, sord, rord)` with `gd = b.grants`. The existing
  per-block existence lemmas (`ProcNativeCodecComparisonWitness.native_main` / `missing_chunk`) choose `gd`
  existentially inside; `PriorCore`/`accepted_record_tables` (`Assembly/SchedulerCodecAcceptedRecords.lean`) do
  not export the `gd`↔distribution link. Next step: add a `PriorCore` variant (new structure, existing statements
  kept) with `∀ b ∈ bs, ∃ cv st rs ev sord rord, runPrefix … ∧ distributeEv … = .ok (b.grants, sord, rord)`, proved
  where `accepted_record_tables` builds the blocks. For τ ≠ 0 the codec's `ft` is defined as 0 in `blkOf`, so only
  instance 0 needs the forwarding range. `vid < P`: `priorValueId before tree = forestLookupVid before + i` —
  bound by the forest value count (≤ B0) still to be shown.
* (2) and (4): not started this session beyond `rows_traffic`/`hdr_s0f` (see above).

## 2026-10-12 (package 9, fresh session: NatRes, codec SHA/S0F/SPLEN traffic, allowances)

* Merged origin/main (69b9839b). `ZkFormal.V3.Integration` builds (4577 jobs); `make pin-check` OK.
  Audits: `test/AuditCodecNatRes.lean` (axioms ⊆ {propext, Classical.choice, Quot.sound}).
* **Task 1 — NatRes from acceptance: DONE** (commit 8412c7cb).
  * `Render/CodecGrantCore.lean`: `GrantWit b` (the block's grants are `distributeEv` of its own
    `runPrefix`); re-run of the block construction with the witness exported (existing statements
    untouched): `main_block`, `missing_block`, `implicit_blocks`, `ordered_blocks`, `allocated_blocks`,
    **`accepted_prior_core_grants`**: `checkD0a B` ⇒ `∃ bs, PriorCore p B bs ∧ ∀ b ∈ bs, GrantWit b`.
  * `Render/CodecNatRes.lean`: `vid_lt` (`priorValueId < P` from the forest budget via
    `forest_lookup_offsets` + `valueIndex_bound`), **`natRes_block`** (gb/gfin from
    `ProcPriorCodecGrantCap.native`; instance-0 `ft` from the block's own codec generator: its terminal
    record step at `(kk,2,7)` (`ProcCodecCarryPosition.core`) passed the forward check
    (`ProcPriorCodecForwardSuccess.bound`), so `demand ≤ wfin + gb ≤ 4.5M < 2^24`),
    **`codec_accepted_full`**: table 11 from acceptance with no residual premise.
* **Task 2 — codec traffic closed forms: BYTES, DIGEST, S0F, SPLEN DONE; SPOST not done** (85ca1d3d).
  * `Render/CodecBus.lean`: generic per-bus row traffic (`bus_bytes/digest/s0f/splen/spost`, any
    descriptor, via `cv d col`) and per-kind closed forms (`bytes_*`, `digest_*`, `s0f_*`, `splen_*`,
    `spost_*` for hdr/record/hash/ash). Cheap (whole file < 10 s).
  * `Render/CodecSanity.lean`: `codec_bus` (table traffic = `Bs.flatMap (descs.flatMap G)`), `blk_*`,
    `blkOf_bytes/digest` (via `prepared_sanity_input/job`), and over the `PriorCore` list:
    **`codec_bytes_native`** (`rowsTrafficFp … B_BYTES true = (expectedBytes (schedulerSanityJobs 0
    (bs.map NativeBlock.witness))).map Msg.toFp`), **`codec_digest_native`** (same for `expectedDigests`),
    **`codec_s0f_native`** (`bs.map [τ, b2n pres, vid]`), **`codec_splen_native`** (`bs.map [τ, 37+24n²]`),
    `codec_sha_counts` (the `cnt` form of `rcpt_trie_side`'s codec premises for `us := bs.map witness`),
    `jobs_congr`, **`codec_sha_counts_pinned`** (the premises for ANY `us` with
    `us.map schedulerWitnessSanity = (bs.map witness).map schedulerWitnessSanity`).
  * **FINDING (blocks the discharge of `rcpt_trie_side`'s codec premises):** `rcpt_trie_side`/
    `trie_side_exact` export `us` with only `∀ u ∈ us, u.Valid`. Its origin (`TrieUpsKeys.upserts_kf`)
    has `us.map (pre, output) = (oldPost, m.result.trie) :: steps…` — the main scheduler upsert is
    REBASED onto `oldPost` (not `m.pre`, where the spec runs `schedStep`), and `u.ctx` is not exported.
    `schedulerSanityJob τ u` depends on `schedPub u.ctx` and `readKey u.pre keyBwState`; with only
    `u.Valid`, two valid witnesses with different contexts give different jobs, so the BYTES/DIGEST
    premises are not provable from the exported statement. Needed from the trie lane (or lead), any of:
    (a) `us.map schedulerWitnessSanity = (bs.map witness).map schedulerWitnessSanity` for the
    `PriorCore` list (then `codec_sha_counts_pinned` closes both premises); or (b) per index
    `u.ctx = ctx_i` (main: `m.ctx k`, implicit: `implicitContext k e`) and
    `readKey u.pre keyBwState = readKey pre_i keyBwState` (main: `oldPost` vs `m.pre` — account writes
    do not touch `keyBwState`), from which (a) follows. The same pin is needed for S0F/SPLEN/SPOST
    (the ups side `view_*` is over the trie lane's `Js`, built from that `us`).
  * SPOST closed form still open: codec side = `[τ, pos, bpost]` on hdr/record/hash rows
    (`spost_*` per row done); remaining: block list = `(range (37+24N)).map [τ, p, (stateBytes ids afin
    dig).getD p 0]` (needs `N < 65536`, `afin < 2^24` — both in `Blk.Ok`), and
    `b.witness.value.map toNat = stateBytes …` (no existing lemma links the upsert value to the codec post
    bytes).
* **Task 3 — B_SCMP identity: algebraic part DONE** (59045937). `Render/CodecAllow.lean`: `pairs_eq`,
  **`allowances_canon`** (`ProcActualInput.allowances ids prev = a0Src ids prev` whenever
  `prev.links.map (s, r) = ids.flatMap (s ↦ ids.map (r ↦ (s, r)))`, duplicates allowed, via
  `allow0_src`), **`a0s_canon`** (`(blkOf b).recs kk .a0s = (allowances b.pub.ids b.old)[kk]!` for a
  present canonical prior). Open: canonicity of each block's prior from acceptance (`reads0f … all
  (canonical0f k.L)` ↔ `b.prior`, `k.L.shardIds = b.pub.ids`), and the SCMP bus balance itself
  (codec sends `(apR+fair, MA, cb)`, `(zt·(gfin+gb), zt·ft, zt)` vs the comparator table).
* **Task 4 — not started** (scheduler buses 40–62, ChaCha lane, packaging).

## 2026-10-12 (package 10, same session: lead's pin request — `us` pinned, SHA/SPLEN/SPOST balanced, canonical priors)

* **Pin (option (b), done; trie modules extended by conjuncts only, no statement weakened)** (4ba11819, 9baac291).
  * `Assembly/SchedulerSanityPin.lean`: `schedRead pre` (= `readKey pre keyBwState`), `sanF`/`sanOf`, `valF` +
    `value_valF` (a valid witness's value is a function of its call), `implicitCtx`, `callList k m steps`,
    **`CallPin k m steps us`** (`us.map (ctx, schedRead pre) = callList`), `CallPin.sanity`, `CallPin.values`,
    `sized_find_other` (account replay keeps every other key), `schedRead_rebased` (`oldPost` reads `m.pre`'s state).
  * Threaded: `TrieUpsKeys.implicit_upserts_pin` (new), `upserts_kf`/`physical_kf`/`coverage_kf` (+`CallPin`),
    `TrieUpsOrigin.UpsShaPin` (new def = `UpsSha` body + `CallPin`, `UpsShaPin.sha`), `accepted_ups_walks`/`trie_all_of`
    (+`UpsShaPin` after `UpsSha`; `trie_all_accepted` unchanged, projects it out), `TrieDigestUps.ups_sha_scheduler_pin`
    (new; + `(physicalPrefixUps p insts).map (τ, v) = us.mapIdx (i, value)`), `trie_side_exact` and `rcpt_trie_side`
    (+`CallPin A.k A.m A.steps us` and `∃ Js hok, r7 = upsRenderV3 A.pub Js hok ∧ ExtOf r7.tf (ups view) ∧
    Js.map (τ, v) = us.mapIdx …`; `trie_side` unchanged, projects them out). All trie/rcpt audits re-run: clean.
* **Codec premises of `rcpt_trie_side` discharged** — `Render/CodecGrantCore.lean`: `prior_core_on` (PriorCore on a GIVEN
  trace + `GrantWit` + the blocks' calls `bs.map (ctx, pre) = (m.ctx k, m.pre) :: steps.map (implicitCtx k e, e.pre)`);
  `Render/CodecTriePin.lean`: `codec_on A`, `calls_of_pairs`, **`codec_premises`**, **`RcptTrieSide.rcpt_trie_codec`**
  (rcpt_trie_side + table 11 render: `BYTES`, `DIGEST` balanced unconditionally).
* **SPLEN, SPOST balanced** (9baac291, c123c6a4). `Render/CodecUpsBus.lean`: `value_len` (`|value| = 37 + 24n²`), covers/pub
  lemmas, `link_at`, **`RenderBundleV3.balancedAt_splen`**, `vals_eq` (trie witnesses' values = blocks' values via
  `CallPin.values`). `Render/CodecSpost.lean`: `spT`/`rt_spost`, `posMsgs` (+append/flatten lemmas), `hdr_part`,
  `rec_part`, `hash_part`, **`blk_spost`** (block SPOST sends = `posMsgs τ 0 (stateBytes ids afin dig)`),
  `encode_bytes`, **`value_stateBytes`** (the upsert value = the codec's post bytes: `scheduled_output_exists` +
  `core_state` + `run_link_final` (vfin = st.al) + sanity hash of `b.old`), `codec_spost_native`,
  **`balancedAt_spost`**, **`RcptTrieSide.rcpt_trie_sched`** (rcpt_trie_codec + `SPLEN` ∧ `SPOST`).
* **B_SCMP prerequisite: canonical priors from acceptance (done)** (e38d849b). `Render/CodecCanon.lean`: `single_find`,
  `implicit_reads`, `implicit_found`, `reads_trace` (`reads0f A.k A.w` = the trace's state reads), **`prior_canonical`**
  (`canon0f` ⇒ every present prior has link pairs `ids × ids`), **`a0s_accepted`** (codec `a0s` = repaired process
  allowance on every block of `A`'s trace).
* Integration builds (4582 jobs); `make pin-check` OK; audits `test/AuditCodecTriePin.lean`, `test/AuditCodecNatRes.lean`.
* Parallel lanes: origin/lane/v3-link (05fb2b18) and v3-link-rest (c9427ba1) checked; the announced AIR changes
  (table 9 A9 counter, table 20 DedupTable) have not landed as code yet — not merged.

### Open (this lane), exact
1. **S0F** (codec recv `[τ, b2n pres, vid]` per block, `codec_s0f_native`; ups send `[I.tau, presN I, vidN I]` per
   instance, `view_s0f_send`). Missing: for the trie side's `Js[i]` (= `nativeInstance … root.tree run value Qs` via
   `NativeReaderOrigin`), `(step Js[i] 3).mode = 0 ↔ bs[i].prior.isSome` and then `(step Js[i] 3).e[3] = bs[i].vid`. The
   instance ids come from the forest of `us.map pre = oldPost :: steps.pre` (rebased), the codec's `vid` from
   `m.pre :: steps.pre`; needs (a) the step-3 semantics of `nativeInstance` (value-present lookup at `[0,15]`, its value id
   `root.vid + valueIndex`) and (b) `valueIndex oldPost keyBwState = valueIndex m.pre keyBwState` + equal forest value
   counts (`valsOf` lengths equal by `newchunk_old_tree_reconstruct`). Not started.
2. **B_SCMP: DONE** (16bb51a5, a5ae4cfb). `Render/CodecScmp.lean`: `bus_scmp`, `scmp_rec` (only `(2,2)` always and
   `(2,7)` at τ = 0 send), `CdcScmp.loop_append`, `field_reqs`, `block_reqs`, **`generated_reqs`** (repaired `out.cmps` =
   `(range n²).flatMap (k ↦ (range 3).flatMap (f ↦ (range 8).flatMap (requests … k f)))`), `blk_scmp`,
   **`codec_scmp_native`** (frozen codec SCMP sends = `(bs.flatMap (·.output.cmps)).map cmpMsg` on `A`'s trace, via
   `a0s_accepted`). `Render/CodecScmpBus.lean`: `codec_cmps_ok`, **`sched_renders_on`** (tables 12–15 on a GIVEN
   `PriorCore` list, same proof as `sched_renders_accepted`), **`RenderBundleV3.balancedAt_scmp`** (tables 11–15 of
   the same blocks ⇒ `B_SCMP` balanced; via `scmp_balance_core`). Integration 4585 jobs; pin-check OK.
3. Task 4 (scheduler buses 40–62, ChaCha lane, packaging for tables 8–15, 23, 24): not started. Note table 11 also sends on
   `B_VBYTES` (21; receivers 4, 17, 18, 22) — not covered by any lane's balance yet as far as checked.

## 2026-10-12 (package 11, fresh session: merge A9, S0F balanced, bus map)

* Merged origin/lane/v3-link (a272bd7d, A9 word counter; Integration import conflict resolved by keeping
  both sides) — merge commit 1006fd6b, pushed. lane/v3-link-rest (DedupTable/A10) has not landed: not merged.
* **Build note (performance):** after the A9 merge many heavy modules rebuild (CodecEndInt ~6.5G,
  HorizontalAuxCheck ~5G, CodecHeader, CodecRecInt); a full `lake build` under `HEAVY_MEM=14G` with
  8+ cores is OOM-killed (systemd `oom-kill`, shows as `Terminated`/rc 143).  Working recipe: build
  the heavy modules one by one first (`taskset -c 12-15`), then the target.
* **S0F: DONE** (85bb6710).
  * `Assembly/UpsS0FAddr.lean` (new): `IsVal` (LP/BR terminal), `step3_mode` (any `InstOk` instance:
    step 3 is a present lookup iff `ci ≤ 1`), `trace_val_present` (LP/BR ⇒ `find ≠ some none`),
    **`trace_val_addr`** (present read ⇒ LP/BR terminal, its source has an occurrence address on the
    key path and every such address has vid `w + valueIndex t key`; mutual over `traceUpsert`/
    `traceKids`, `sourceAddresses_size` for uniqueness), `forestRootAt_vid`, `nativeInstance_step3`
    (the step-3 target of `nativeInstance … (nativeWalkBase … (fun _ => vid) …)` on LP/BR is `vid`),
    **`s0f_vid`** (= `priorValueId (ts.take τ) root.tree`), `S0FVid`, `s0fOf` (= `(presN, vidN)`),
    `s0fPair`, **`s0fOf_native`**.
  * `Assembly/UpsS0FRebase.lean` (new): `S0FAt F τ I`, **`s0f_rebase`** (`oldPost` vs `m.pre`:
    `sized_find_other`, `write_value_index`, `write_vals_count`).
  * Threaded by conjuncts only: `forest_terminal_exact`, `forest_native_walk_exact` (+ terminal
    occurrence address), `scheduler_instance_origin_inputs`, `chosen_origin_instances`, `coverage_kf`
    (+ `S0FVid`), `UpsShaPin` (+ `S0FAt (m.pre :: steps.pre) τ I`), `ups_sha_scheduler_pin`,
    `trie_side_exact`, `rcpt_trie_side`, `rcpt_trie_codec` (+ `Js.map s0fOf = F.mapIdx (s0fPair (F.take i))`,
    `F = A.m.pre :: A.steps.map pre`); callers' patterns adjusted.
  * `Render/CodecS0F.lean` (new): `s0fPair_read`, **`RenderBundleV3.balancedAt_s0f`**;
    **`rcpt_trie_sched`** now also gives `R.BalancedAt B_S0F`.
  * Integration builds (4598 jobs); `make pin-check` OK; audit `test/AuditUpsS0F.lean` clean
    (`s0f_rebase` needs only `propext, Quot.sound`).
* **Bus map of `nearAirV3`** (bus, senders, receivers; `lake env lean` eval of `nearTablesFull`):
  0 [2,4,7,11,16,17,20,23]→[0,1]; 1 [0,1]→[2,3,7,11,16,20,23]; 2 [2,3]→[2]; 3 [17]→[2]; 4 [2,3,5,7]↔;
  5 [16,22]→[5]; 6 [5]→[16,22]; 7 [16,17]↔; 8 [16]→[24]; 9 [16,23]→[23]; 10 [7]→[3]; 11 [2,5,7]↔;
  14 pub→[20]; 15 [16,19]↔; 16 [16]↔; 17 [2,3]→[6]; 18 [2,4,7,20]→[21]; 19 [6]→[2,4]; 20 [2,4]↔;
  21 [11,17,18,22]→[4]; 22 [2]→[4]; 23 [7]↔; 24 [3]→[7]; 25 [2,7]↔; 26 [16]→[20]; 27 [16,18]↔;
  28 pub→[19]; 29 [22]↔; 40 [11,12,13,14]→[15]; 41 [11,12,13]→[14]; 42 [14]→[11,12]; 43 [12]→[13];
  44 [12,13]→[13]; 45 [13]→[10]; 46 [10]→[13]; 47 [10]↔; 48 [9]→[10]; 49 [10]→[13]; 50 [8]→[9];
  51 pub→[11,13]; 52 pub→[11,12]; 56 [11]↔; 57 [12]↔; 58 [12]→[11]; 59 [7]→[11]; 60 [11]→[7];
  61 [11]→[7]; 62 [11]↔; 63 [22]↔; 70 [7]→[2]; 71 [7]→[4].  (53–55 unused.)
* **Uncovered buses (no bundle-level `BalancedAt` anywhere), exact:** 9 `MPOS` (rcpt 16 + mrk 23 → mrk 23),
  21 `VBYTES`, 41 `SOP`, 42 `SFIN`, 43 `SINC`, 44 `SPUSH`, 45 `SSIN`, 46 `SSOUT`, 47 `SSMEM`, 48 `SGEN`,
  49 `SSHUF`, 50 `SCHACHA`, 51 `SPUBB`, 52 `SPAR`, 56 `SDL`, 57 `SDLX`, 58 `SDG`, 62 `SA0`.  Everything
  else is in `rcpt_trie_sched` (+ `balancedAt_scmp`).  Hence `CompleteV3Stmt` cannot be assembled yet.
* **VBYTES analysis (not started as proof):** revealed pre-forest values are exactly the `.val` slots
  that `buildFor` reveals for the EXACT keys in the per-trie key list (`mkSlot … (keys.any (· == k))`),
  so the statement to prove is: for each forest tree, the key list's present non-empty values are read
  once each by exactly one of codec (`keyBwState`), acct (receiver account keys, once per distinct
  key), akey, qv (queue keys); duplicates in the key list / repeated receivers must be sent once.  If
  any key in a tree's key list is read by none of the four (e.g. a key listed but not read on an
  implicit step), the honest render has an unmatched val receive — check this first.
* Open, in order: VBYTES (above); scheduler 41–44, 51, 52, 56–58, 62 (closed forms of tables 11–14
  traffic exist only for SCMP/BYTES/DIGEST/S0F/SPLEN/SPOST); ChaCha 45–50 (+ the RNG `hW`); MPOS
  (receipt/mrk lane?); then the packaging (`sched_renders_on` + `rcpt_trie_sched` + `RenderV3Header`).

## 2026-10-12 (package 12, fresh session: every remaining scheduler bus balanced)

All ten uncovered scheduler buses are now balanced on the honest render: 41 SOP, 42 SFIN, 43 SINC, 44 SPUSH,
51 SPUBB, 52 SPAR, 56 SDL, 57 SDLX, 58 SDG and 62 SA0. No AIR gap was found and no AIR change was needed.
Each bus was proved from closed forms of the table traffic plus native run identities.
Integration builds (4631 jobs), `make pin-check` is OK, and there is no sorry, axiom, native_decide or
implemented_by. Audit: `test/AuditSchedBuses.lean`, axioms ⊆ {propext, Classical.choice, Quot.sound}.
The existing audits AuditCodecTriePin, AuditUpsS0F and AuditCodecNatRes were re-run and are clean.

* **Top lemmas** (`Render/SchedBusAll.lean`):
  * **`RenderBundleV3.sched_buses_balanced`**. It takes `A`, `R`, `PriorCore A.p B0 bs`, `GrantWit`, `hctx`,
    `hfw` (see below), `R.tf 11 =` the codec traffic, and the `.tr` of tables 12, 13 and 14 equal to the
    renders of `sched_renders_on`. It concludes the ten `BalancedAt`.
  * **`sched_side`**. From the `PriorCore`/`GrantWit`/`hctx`/`hfw` data and the `r11` of `rcpt_trie_sched`,
    it gives `∃ r12 r13 r14 r15` such that every bundle carrying `r11 … r15` balances all eleven scheduler
    buses 40–44, 51, 52, 56–58 and 62 (SCMP included).
* **Per-bus lemmas** (`RenderBundleV3.balancedAt_*`):
  * `SchedBusSA0`: `srcOf` is injective, so the sends and receives are permutations of each other, and a
    u64 allowance has a byte ≥ 3 set iff it is ≥ 2^24.
  * `SchedBusSDL`: the delay line telescopes, with the public endpoints at instances 0 and K+1, all
    instances having the layout's ids.
  * `SchedBusSPAR`: the codec header, scan param/raw rows, shard rows and link cells together give
    exactly `render`'s `par` (shards and links up to a permutation).
  * `SchedBusSPUSH`, `SchedBusSINC`, `SchedBusSFIN`, `SchedBusSOP`, `SchedBusSPUBB`.
  * `SchedBusSDLX`, `SchedBusSDG`: from the distribute grid model.
* **Infrastructure:**
  * `SchedBusCodec`, `SchedBusCodecBlk`: codec per-row and per-block forms for SA0, SDL, SPUBB, SPAR, SOP,
    SFIN and SDG.
  * `SchedBusSsd*`: ssd per-row bus messages; `SchedBusSsdDist` is a functional model of the distribute
    generator (`cells`, `grid`, `dist_rows`).
  * `SchedBusConv`: converted requests are the public raw requests with a set bit.
  * `SchedBusPub`: the public `SPUBB`, `SPAR` and `SDL` counts of `A.pub`; `bs.map pub = p.sched`.
  * `SchedBusProc`, `SchedBusMem`: proc and mem closed forms.
  * `SchedBusRun*`: run-level SOP, SFIN, SPUSH and SINC identities from a replay ghost invariant.
    Processed entries are distinct; each processed increment occurs exactly once.
  * `SchedBusGrid*`: the grid endpoints, grants and allowed-cell check. The model's grants are
    `GrantWit`'s `b.grants`.
  * `SchedBusPackaging`: `usedBuses` (51 buses, kernel-checked against all tables and public segments) and
    `RenderBundleV3.balanced_of_used`, which says a bundle balancing every used bus is `Balanced`.
* **Shared-statement change (conjunct only; needed for SPUBB):** instance 0's codec block forwards
  `b.forwarded`, which nothing exported before. The conjunct
  `(∀ b, bs[0]? = some b → b.forwarded = fwdLinks (A.m.ctx A.k) A.m.result.outgoing)` was added after the
  `hctx` conjunct of:
  * `CdcGrant.ordered_blocks` (as `main.forwarded = …`), `allocated_blocks` and `prior_core_on`
    (`Render/CodecGrantCore.lean`);
  * `codec_on`, `codec_premises` and `RcptTrieSide.rcpt_trie_codec` (`Render/CodecTriePin.lean`);
  * **`RcptTrieSide.rcpt_trie_sched`** (`Render/CodecSpost.lean`).

  No statement was weakened; the callers' patterns were adjusted. `prep_fwd` gives
  `A.p.fwd = fwdLinks (A.m.ctx A.k) A.m.result.outgoing` (from `prepD0_fwd` and `body_decodes`).
  **Merge note:** if a sibling lane also extends `rcpt_trie_sched`, keep both conjuncts.
* **Open (for packaging, after all three lanes land):**
  * Lane v3-render-vbytes: 9 MPOS and 21 VBYTES.
  * Lane v3-render-chacha: 45–50 and the RNG `hW`.
  * All other 41 used buses are already covered: 63, 70 and 71 are QVC, RPL and RPLV (in
    `rcpt_trie_sched`). The full map is in the `SchedBusPackaging` docstring. The receipt side's
    `BusBalanced` is the same proposition as `BalancedAt` (`balancedAt_of_bus`).
  * Build the full 25-table bundle and the header check (`RenderWitnessV3`) using `balanced_of_used`.
