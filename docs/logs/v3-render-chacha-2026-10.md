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
