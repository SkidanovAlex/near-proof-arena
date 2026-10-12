# Lane v3-render-chacha — log (2026-10)

Goal: bundle-level balance of the ChaCha/rng/shuffle buses 45 SSIN, 46 SSOUT, 47 SSMEM, 48 SGEN,
49 SSHUF, 50 SCHACHA for the honest render, and the RNG render's `hW : rngRows calls ≤ W0` from A9.
Branched from lane/v3-render-sched (bdb67614).

## 2026-10-12 (session 1)

* `Render/ChachaReplay.lean`: `replay_inst` (a successful `replayShuffle key k vals` is the `shufV3`
  instance `⟨lid, key, k, vals⟩`: result `final`, end `kBefore 0`, every draw succeeds),
  `kAt_mono`, `kBefore_le`, `final_perm`.
* `Render/ChachaRun.lean`: loop invariants of the native run's replay (entry loop: `ein`, `eout`,
  request bound; round loop: `RoundOk` + `Stamped`), **`run_rounds`**.
* `Render/ChachaProcBus.lean`: table-13 traffic on SSHUF/SSIN/SSOUT per row / per run / whole table
  (`table_count`), `keyN_leWords`, `lid_fp`.
* `Render/ChachaLane.lean`: lane instances of the native runs (`laneInsts` = one `shufV3` instance per
  round, `laneCalls` = their `gen_index` calls in drawing order, `laneReqs` = `Sched.Gen.Lane.chachaReqs`,
  `laneWords`); `RunOk`/`RdOk`; `shuf_run`/`in_run`/`out_run` (process ↔ shuffle messages, exact),
  `gen_perm` (SGEN, permutation), `words_lane` (genV3 receives = `laneWords`, exact; words of each run
  are `0 … kfin−1` via the `Stamped` cursor chain), `chacha_lane_perm` (chachaV3 sends ~ `laneWords`);
  support conditions `inst_ok`/`call_ok`/`req_ok`; row counts `shufRows_le`, `rngRows_lane` (= Σ kfin),
  `reqs_lane`/`reqs_sum`; `round_T` (list ids < p).
* `Render/ChachaWords.lean` (the `hW` discharge): `block_words` (spec `schedWords` of a block's
  scheduler input = its native run's `kfin`, via `prims_sched_eq_mid`, `runMid_stW`/`coreMidW` (copies
  of lane v3-link's `A9Words.runMid_st`/`coreMid`, renamed — lane v3-link is not merged here),
  `coreMid_proc`, `prepared_process_exists`, `run_rounds`), `schedIns_native` (`schedInsD0` of the
  accepted claim = the native trace's inputs), **`kfin_sum`** (`Σ kfin = chachaWords cb wb`),
  **`kfin_W0`** (A9 ⇒ `≤ W0`), **`runOk_all`**.
* `Render/ChachaBusBalance.lean`: `RenderBundleV3.balancedAt_{ssin,ssout,ssmem,sgen,sshuf,schacha}` and
  **`chacha_buses_balanced`** (premises: `A : AcceptedV3`, `PriorCore A.p B0 bs`, the `hctx` pin — as
  `balancedAt_scmp`): `rngRows (laneCalls runs) ≤ W0` and ∃ renders r8/r9/r10 (ChaCha/RNG-with-A9/shuffle
  of the lane lists) such that every bundle with them and table 13 = `procTraceV3 runs` balances the six
  buses. No AIR change was needed; no shared statement changed.
* Audit `test/AuditChachaBus.lean` (19 guarded `#print axioms`, ⊆ {propext, Classical.choice, Quot.sound}).
* Note for the lead: the honest renders are fixed by `bs` (`laneReqs/laneCalls/laneInsts (bs.map run)`),
  same `bs` as `sched_renders_on` / `rcpt_trie_sched`; packaging into `CompleteV3Stmt` still needs the
  scheduler buses 41–44, 51, 52, 56–58, 62 (lane v3-render-sched), VBYTES/MPOS (lane v3-render-vbytes).
* Integration builds (4604 jobs); `make pin-check` OK.
