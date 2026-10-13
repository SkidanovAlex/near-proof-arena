# lane/v3-prover-prove — first real v3 D0a proof, end to end (2026-10-13)

**Base.** `integration/prover-20261013b` (main + lane/v3-prover-trie, `7b704766`); merged
`origin/lane/v3-prover-schedqv` (`39407deb`, native tables 8–15, 22). Lean sources of `zk-formal`
untouched; only `examples/np-udr-stark-v2/{source,conformance,formal}` and this log.

## What was built

* **`npudr v3prove <case_dir> <out_dir> --air <nearAirV3.json> [--pub <public.bin>] [--extra
  <dir>] [--check-only]`** (`src/v3/prove.rs` `case_inputs`/`render_cols`/`bus_balances`/`join`,
  `src/bin/npudr.rs`): from `claim.bin` + `witness.bin` only —
  hint `hintOf` (`v3::hint`), prepared statement `cb' = Public.preparedBytes (prepD0 cb h) 0`,
  all 25 honest tables natively (`v3::trie` 2–7, 21; `v3::schedqv` + `chacha::lane` 8–15, 22;
  `v3::rcptfam` 16–20, 23, 24; SHA collector 0, 1), rendered straight into compact columns
  (SHA tables without the padded row-major copy), **every table's constraints**
  (`failing_constraints_cols`, publics of `cb'`), **every bus balanced** — exact multisets per
  bus over all 25 tables **plus the public messages of the tape** (`pubFit`, `pubMsgs`; the
  cross-side buses BYTES 0, DIGEST 1, SIZE 18, VSLOT 21, KEYNIB 5/6, FINAL, VBYTES 60, MPOS … are
  checked here for the first time) — then the STARK at `auxGroup = 2` over
  (`public.bin`, `cb'`), proof `join (Hint.encode h) π = borshBytes h ++ π`, re-checked by the
  Rust verifier. Imbalances / constraint failures are reported precisely (bus, message,
  sent/received; table, constraint, row) in stderr and `report.json`, and no proof is written.
* **`np-lean-verify-v3 <pub.bin> <claim.bin> <proof.bin>`** (`conformance/VerifyV3.lean`): the
  deployed model `(npVerifierP challengeSpecD0a nearAirV3 split prepV3b).toVerifier.deployed`
  at `auxGroup = 2`, with the Lean constant `nearAirV3` (no JSON import), i.e.
  `NpUdrStarkV2.Model.verifier`.
* **`np-lean-bundle-v3 <case> <dir>`** (`conformance/BundleV3.lean`): stopgap Lean dumper of the
  scheduler blocks (`PriorCore` construction: `p.sched[τ]`, `readKey pre keyBwState`,
  `ActualRun.run`, `priorValueId`, distribution grants, `fwdLinks` at τ = 0), ChaCha lanes and
  qv walks/records, written before the sibling's native port landed; now a second, independent
  ground truth for `npudr v3sched` (prove.sh step 1).
* **`run-v2.d/prove.sh`** (gated `PROVE_V3=1`; knobs `PROVE_CASES`, `PROVE_NEG`, `PROVE_REUSE`).
* **Certificate:** `formal/NpUdrStarkV2/Certificate.lean` `certificate (bd tid)` is now main's
  unconditional `ZkFormal.NearV3.Assembly.nearV3_admission_final` with `hpub`/`himpl` by `rfl`;
  `#print axioms` = `[propext, Classical.choice, Quot.sound]` (guarded by `#guard_msgs`).
  Needed `set_option maxRecDepth 20000` (elaborator resource limit while unifying the artifact
  literal; not a logical option). `lake build NpUdrStarkV2.Certificate` OK (4,566 jobs; the
  zk-formal cache was completed with `cp -an` from the clean `v3-integ-d` worktree at the same
  commit, no hard links; lake rebuilt ~2,000 modules whose traces did not match).

## Results

**Bus balance with all 25 tables (task 1).** `npudr v3prove --check-only` on all 81 fixtures
(64 `public-d0a/d0` + 17 `fixtures-extra/d0`): every table's constraints hold and **all 51 buses
balance** (tables + public messages) — the cross-side buses (BYTES 0, DIGEST 1, KEYNIB 5/6,
SIZE 18, VSLOT 21, VBYTES 60, MPOS, FINAL, the scheduler buses 40–62, …) had never been checked
together before. No imbalance found on honest data, so no Rust/Lean disagreement to report.
First pass used the Lean dumps for 8–15/22 (np-lean-bundle-v3), second pass fully native after the
schedqv merge: 81/81 both times. The two independent derivations of tables 8–15, 22 (my Lean
`np-lean-bundle-v3`, the sibling's Rust `npudr v3sched`) are JSON-identical on 81/81 (even though
they compute `vid`/grants through different definitions: `priorValueId`/`distRows` vs
`nativePriorIds`/`distributeEv`). Caveat: no fixture has ChaCha requests (all `conv = []`; 3 have
shuffle instances), so tables 8/9 are exercised only at their empty (log 1) shape by real data.
One bug found and fixed on the way: the Lean dumper emitted only the payload's own field for qv
records; the Rust `QvRecIn` needs all three (`index`/`entries`/`bytes`).

**Proofs (task 2/3)** — 8 CPUs (`taskset -c 8-15`), `HEAVY_MEM=32G`, `NPUDR_MEM_GB=20`:

| case | proof B (hint B) | prove s | max RSS | Lean verify | negatives |
|---|---|---|---|---|---|
| 00-h10004-s3 (smallest) | 5,256,829 (16) | 749 | 12.2 GB (internal peak 15.5 GB) | accept, 2.8 s | 14/14 rejected |
| 00-h10035-s3 (largest witness, 118 KB) | 5,674,156 (155) | 736 | 13.3 GB | accept, 2.9 s | 14/14 |
| 01-h10009-s1 (2 scheduler blocks) | 5,618,528 (155) | 710 | 12.6 GB | accept, 3.1 s | 14/14 |

All ≤ `maxProofBytes` = 8,388,608 and STARK parts ≤ `v3MaxInner` 6,435,489. Phase split
(smallest): main commit 196 s, aux 104 s, quotient 209 s, quot commit 79 s, ood 23 s, deep 31 s,
FRI 1.5 s, openings 106 s. Cost is dominated by the six fixed `2^22`-row tables (codec 91,
scandist 119, proc 64, mem 18, cmp 33, rcpt 263 columns: ~3.1 GB compact, LDE `2^26`); the
row-major `Tab` of a 2^22 table is transient (rcpt 4.4 GB) and SHA tables are now built straight
into compact columns. Rust verifier: 0.11 s. The low-memory prover (`NPUDR_MEM_GB`) keeps RSS
well under HEAVY_MEM.

Negatives (Lean `np-lean-verify-v3` must print `reject`): π byte flips at its first, middle, last
byte; truncated by 1; extended by 1; empty proof; hint `n` byte; first hint body byte; outer hint
length +1; public tape byte; claim byte at 3 / middle / last; another fixture's claim.

**Fully native (after the schedqv merge).** `run-v2-section.sh prove` (`PROVE_V3=1`) on
00-h10004-s3 with no Lean input to the prover: Lean bundle == Rust v3sched, 51 buses balanced,
proof 5,256,829 B (same size), prove 680 s, 12.2 GB, Lean accepts (3.1 s), 14/14 negatives
rejected — ALL PASS.

**Checks.** `cargo fmt --check` OK; clippy: no findings in the files this lane touched
(`v3/prove.rs`, `v3/sha.rs`, `bin/npudr.rs`; the crate's pre-existing findings remain);
`cargo test --release` 140 passed / 0 failed; `make pin-check` OK; no `sorry`/`axiom`/
`native_decide`/`implemented_by` added.

## Remaining

* The candidate's packaged `out/prove`/`out/prepare` (`build-recipe/build.sh`, `bin/prove.rs`) are
  still the inherited v1 surfaces; wire them to `v3prove` (prepare = public.bin, prove = proof.bin)
  before a judge run.
* No fixture exercises ChaCha requests (tables 8/9 non-empty) — a fixture with scheduler requests
  would cover them on real data (the sched section covers them on sampled blocks).
* Prove time ~12 min on 8 cores, dominated by the fixed 2^22 tables; the D0a judge budget for
  `prove` should be checked against this (and the elaboration budget of the certificate's
  closure, HANDOVER §5, is still unmeasured for this package).
