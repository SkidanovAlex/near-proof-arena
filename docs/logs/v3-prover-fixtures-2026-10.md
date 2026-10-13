# Lane v3-prover-fixtures (np-udr-stark-v2, D0a prover) — 2026-10

## 2026-10-13 — extra D0a fixtures: repeated source keys, empty values

Gap: the 64 public D0a fixtures never repeat a source key (SrcpDD dup/rep rows, public dup
byte 1, gated RC digests only unit-tested) and never read an empty value (zero-length VPRE jobs,
val `vz` rows only unit-tested).

* Branch from lane/v3-prover 28e1c68f; merged origin/lane/v3-prover-prep (conflicts run-v2.sh,
  src/v3/mod.rs resolved as on lane/v3-prover-rcptfam 8a3366a5), then origin/main bb37a433 (clean).
* Provenance of the public fixtures: nearcore chaingen (`oracle/v3-d0a`, seed 4243); duplicates
  were previously only constructed by `oracle/tools/dupkey_v3.py` (2 copies, older block, not
  committed as fixtures).  New generator
  `examples/np-udr-stark-v2/conformance/fixtures-extra/gen_extra_d0a.py` (+ `generate.sh`):
  slot-inner copies (any block/slot, any count) and groups-data value overrides / new
  `BufferedReceiptIndices`; restores all hashes, post roots fixed point-wise by the Python
  reference (`spec_check_v3.py`, verdict ok).  Nothing frozen touched.
* Empty values: in D0 only `BufferedReceiptGroupsQueueData` (read with `readKey`, value ignored)
  can be present-and-empty in an accepted witness; account/access-key/queue-index/scheduler
  reads must decode, so codec/acct/akey cannot carry an empty value.  Empty values enter via qv.
* Fixtures: 17 accepted (`d0/`: dup 2x/3x/4x in B2, older block, across blocks both directions,
  two repeated keys, with implicit block; 1/2/3 empty values, empty + absent + non-empty, with
  implicit block; combinations) and 3 rejected (`mutants/`, dup without the extra unused entry).
  Inconsistent repeats (dup byte 2) cannot come from a claim (key = chunk hash commits to
  from-shard and root), so that negative is a prepared-statement mutation.
* Lean `nearspec-v3-check-d0a` in the worktree was stale (Oct 9, old A7 measure: `unfold` =
  today's `unfold_diff`); rebuilt (91 jobs).  D0a difftest on fixtures-extra: 17/17 accepted by
  Lean and Python, 3/3 mutants rejected, 0 disagreements (incl. unfold/chacha/path-depth).
* Rust: `check::bus_imbalance_with_pub` + `npudr v3bus <air> <pub.bin> <bus> <table>=<json>...`
  (one bus over the supplied tables + the tape's public messages).  No Rust divergence found;
  collect.rs / rcpt.rs not touched.
* `run-v2.d/extra.sh` (runs by default in run-v2.sh): 292 PASS / 0 FAIL — acceptance; public
  tape, Prep.encode, Hint, d0-prep, v3prepare byte-identical to Lean; `[dup, rep]` bytes = an
  independent `sourceDupByte`/`sourceRep`; node/val/head v3check, val/head Rust == Lean; SHA
  families + bins identical (zero-length VPRE jobs 1–3 per empty case; RC gated 1–3 per dup
  case), sha_t/sha_r v3check; srcp/acct v3check + Rust == Lean; bus 14 balanced; negatives
  (from-shard / root change -> dup byte 2 row, cleared rep) -> bus 14 unbalanced.
  `run-v2-section.sh` takes `FX=<dir>`; `collect` section with FX=fixtures-extra/d0: 17/17
  families + bins identical.
* Not covered: receipt SHA family (gated RC) is Lean-supplied until the rcpt dumper exists
  (lane v3-prover-rcptfam); Lean node render skipped (slow); sched/rcpt/a7/rcs sections use
  seeded samplers, not fixtures (unaffected).
* cargo fmt / clippy (no new findings in changed code); make pin-check ok.
