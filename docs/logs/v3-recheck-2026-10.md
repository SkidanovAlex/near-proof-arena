# Lane `lane/v3-recheck` — kernel rechecks of the D0a certificate closure, log

Worktree `/data/illia/nearproof-wt/v3-prune`, branch `lane/v3-recheck` from main `c6247f3d`.
Goal: measure the three independent rechecks the formal judge runs on the packaged
`NpUdrStarkV2.certificate` (= `nearV3_admission_final`, 3,964 modules after pruning), against
`Limits::default` (2 h per recheck run, 4 h per rechecker; 1 h per module and 4 h total
elaboration). CPUs 12-14 (+ siblings 28-30) only.

## 2026-10-13

### What the judge runs (`runners/formal-checker/src/pipeline.rs`, Stage B)

* Required rechecker set: challenge `toolchain_policy.recheckers` = `leanchecker, nanoda,
  lean4lean` (draft `near-chunk-validation-d0-stark`); `Policy::default().required_recheckers` =
  leanchecker + nanoda; lean4lean runs whenever installed.
* Candidate `.olean`s are copied (regular files) into a fresh replay dir with the judge's
  trusted `.olean`s linked in; `LEAN_PATH` = that one dir; env `PATH=<tc>/bin:/usr/bin:/bin`,
  `HOME=/tmp`, `ARENA_LEAN_SYSROOT`, `LEAN_ABORT_ON_PANIC=1`, cwd `/tmp`, no `mem_bytes` limit.
* **B1 leanchecker** (toolchain v4.34.1 `bin/leanchecker`, sha256 `ccef1bfe…`): one sandbox run
  per candidate module (`recheck_batch_modules = 1`), argv `leanchecker <Module>`, no flags;
  each run imports the module's imports and replays its declarations through the C++ kernel.
  Runs are serial; each has a 2 h timeout, all of them together 4 h (`recheck_total`, checked
  before each run).
* **B2 lean4export** (`076e8e57`, sha256 `8c5d64ba…`): `lean4export <all candidate modules> --
  <certificate> <candidate @[csimp] lemmas>` → NDJSON (2 h, ≤ 16 GiB).
* **B3 nanoda** (`nanoda_lib 3a240721`, sha256 `25906eb2…`): one run on the export, config
  `{nat_extension, string_extension, unsafe_permit_all_axioms, print_success_message}` (2 h).
* **B4 lean4lean** (`8223d223`, sha256 `bab5916d…`, default fuel, recDepth 50,000): like B1,
  one run per module, 2 h / 4 h.
* Both module checkers treat each argument as a *prefix*: `leanchecker M` also replays every
  `M.*` module. In this closure only 3 modules prefix others (11 extra module replays).

### Method

1. *Replication* (exact peak RSS via `/usr/bin/time`): lake-built `.olean`s of the 3,964
   modules (zk-formal `.lake` after a no-op `lake build`, the 4 `NpUdrStarkV2` modules built in
   the package; vendored `formal/{ZkFormal,ReexecV3D0}` byte-identical to `zk-formal/` and
   `examples/reexec-v3-d0/formal`, lock `zk-formal.sha256` checks) copied into one replay dir
   with the repo's trusted ArenaCore/NearSpec/NearSpecV3 `.olean`s; the judge's argv and env,
   one run per module, serial, each run pinned to one physical core (`taskset -c 12|13|14`;
   siblings 28-30 idle). Wall time = sum of per-run wall.
2. *Full judge pipeline*: `target/release/formal-check` (this tree) on the packaged
   candidate, dev bwrap sandbox, `Limits::default`.

Note: symlinked candidate `.olean`s are invisible to both checkers (the search-path walk skips
symlinks: "Could not find any oleans"); the judge copies regular files, so the replication does too.

### Packaging blocker found on the way (not a recheck issue)

`examples/np-udr-stark-v2/formal/lakefile.toml` has `[[require]] name = "ZkFormal" path =
"../../../zk-formal"`. Staging (`staging.rs` `check_lakefile_toml`) rejects every `require` not in
`Policy.allowed_requires`, which is empty by default and set nowhere in production (the draft's
`allowed_packages` is `[]` too): **as packaged, the judge stops with MANIFEST_INVALID +
CERTIFICATE_MISSING before elaborating anything.** The other candidates (`np-udr-stark/formal`,
`reexec-v3-d*`) ship no `require`. Fix (packaging, not done here): drop the `[[require]]` block
(the vendored sources are already inside `formal/`) or the whole lakefile, and use the conformance
package / `zk-formal` for local builds. The full pipeline run below uses a copy with the block
removed.

### Results

**leanchecker — PASS**, 3,964/3,964 runs exit 0. Sum of per-run wall 5,437 s (1.51 h); longest
run `Render.CodecRecInt` 254 s, then `MemLink` 253, `Avail` 194, `MemTau` 137, `CodecEndInt` 134;
3,802 runs < 2 s (import-dominated) sum to 1,806 s. Peak RSS 6.9 GB (`Extract.Ups.PlanDefs`).
Fits 2 h / run and 4 h total. Caveat: from 19:28 another lane's `lake build` (`v3-size-opt`,
`taskset -c 8-15,24-31`) shared these CPUs, so the wall sum is an upper bound.

**lean4lean — `Render.CodecRecInt` does not complete within the memory available.**
Samples: `CodecHeader` 180 s / 13.6 GB, `CodecEndInt` 362 s / 5.8 GB (both pass).
`CodecRecInt`: after 2,598 s wall (only ~10 CPU-min: the shared `zkbuild.slice`, memory.high 40 GiB
for all lanes, was at 44.5 GB and throttling everything) RSS was 31.3 GB and still growing; killed
(it was starving the other lanes). Shape: `rec_in_int` is ONE theorem whose proof is 21
`codec_int` cases (f ∈ {0,1,2} × gg ∈ {0..6}); `hdr_int` (CodecHeader) is one theorem with 4 cases
and already needs 13.6 GB, while `CodecEndInt` (several smaller theorems) needs 5.8 GB — lean4lean
memory scales with the size of a single declaration (its whnf/defeq/infer caches live per
declaration). Experiment (scratch copy of `CodecHeader` with each case `as_aux_lemma => codec_int`,
each case its own kernel declaration `hdr_int._proof_1_N`): lean4lean **4.8 GB** (was 13.6 GB),
218 s (was 180 s; ~50–60 s per case). Hypothesis confirmed for memory. But elaboration of that
variant took 1,114 CPU-s vs ~335 s for the original (measured on a contended HT sibling; being
re-measured cleanly) — for `CodecRecInt` (1,255 s today) that could approach the 1 h per-module cap.

**lean4lean — two outright rejections in the other 3,961 modules** (3 shards, one per physical core):

1. `Candidates.SortGeneralTraffic`: `SortGeneral.traffic: (kernel) deep recursion detected`.
   Bisected (scratch modules, `sorry`-stubbed variants; leanchecker accepts the original in 13 s):
   the `have row` sub-proof, branch `¬ q < 32 * S.length`, the `simp` closing
   `List.replicate (if Fp.ofNat 0 = 1 then 1 else 0) [cells…] = []`. That `simp` also rewrites the
   *dead* cells `SortGen.bbAt S ((q + 2 * 2^18 - 1 - …) % 2^18)`: `Nat.add_one_sub_one` turns
   `q + 524288 - 1` into `q + 524287` (simp trace), i.e. the proof uses
   `Nat.add_one_sub_one (q + 524287)` at type `q + 524288 - 1 = q + 524287`. The kernel must check
   `q + 524287 + 1 ≡ q + 524288` with `q` free. The C++ kernel peels one `succ`; lean4lean's
   `reduceNat` has no free-variable short-cut and unfolds `Nat.add q 524288` one `succ` per level
   → > 50,000 (`recDepth`) → "deep recursion". Same lean4lean divergence as D3α
   (`docs/logs/d3-lean4lean-2026-10.md`, `Nat.mul x 65536`).
   **Fix (proof only):** `split; · rw [if_neg (show ¬ (Fp.ofNat 0 = 1) from fp_zero_ne_one)]; rfl;
   · rfl` — never touches the cells.
2. `Render.Ups.CopyPayload`: `FieldPayloadEdit.byte: (kernel) deterministic timeout` (fuel).
   Bisected to case `ix = 0, ts ≠ 1` (`x = 15`), then to the `simp` set: `hx, ht, reduceIte,
   Nat.reducePow` alone passes; adding `getElem?_pos, List.getElem_cons_zero, Option.getD_some`
   (simp's route for `[(old + 32768) % 256, (old + 32768) / 256].getD 0 0`) fails — checking that
   route makes lean4lean reduce `(old + 32768) % 256` with `old` free, again one `succ` at a time
   (32,768 levels, `Nat.mod` iterations), until its whnf fuel runs out.
   **Fix (proof only):** `simp only [List.getD_cons_zero, List.getD_cons_succ]` before the
   original `simp … <;> omega`.

Both fixed proofs pass lean4lean in scratch copies (full theorems, no `sorry`).

**lean4lean, all other modules:** 3,959 of the remaining 3,961 accepted; sum of per-run wall
4,489 s on 3 cores (contended; CPU time recorded from mid-run on), peak RSS 6.9 GB outside the codec
modules.

**`CodecRecInt` fix: one theorem per case.** `as_aux_lemma` works for lean4lean but doubles
elaboration: same CPUs, same contention, `hdr_int` original 594 CPU-s vs `as_aux_lemma` variant
1,185 CPU-s (each aux lemma is closed over the large local context and added synchronously).
Instead `rec_in_int` keeps its statement and proof skeleton, and each of the 21 cases is a separate
theorem `rec_in_int_F_G` (generated by a local `hygiene false` command macro: the hypotheses of
`rec_in_int` plus `f = F`, `gg = G`, then `subst` and the original tactic script, so `codec_int`
sees the same context as before). Scratch elaboration: rc 0, 1,052 s wall on 3 threads (the cases
elaborate in parallel), 2,410 CPU-s on contended HT siblings, 12.2 GB.

**lean4export — PASS:** 202 s, 7.9 GB RSS, NDJSON 2.96 GB (limits: 2 h, 16 GiB file).

**nanoda — FAIL: `thread 'main' has overflowed its stack`, exit 134 after 698 s (5.3 GB).** The
judge counts any non-zero exit as `rejected` (RECHECK_FAILED). The judge's config leaves
`num_threads` at 0, so nanoda checks serially *on the main thread*, whose stack is the inherited
RLIMIT_STACK (8 MiB here; the sandbox helper sets no stack limit). nanoda's own worker threads
(`num_threads ≥ 2`) get `STACK_SIZE` = 16 MiB.

Diagnosis (scratch copy of the pinned `nanoda_lib 3a240721` printing each declaration before it is
checked; diagnostic only): the overflow is in **`RcptSkeleton.deposit_inverse_cell`**
(`Assembly/RcptDepositFrame.lean`), the 51,762nd declaration; everything before it passes. It is
not a too-small stack: with a 64 MiB stack it overflows after 11 s, with an unlimited stack RSS grew
~1 GB / 20 s until killed. Isolated (export of just that constant): the proof was
`have haux (aux) : receiptCell … (booleanReceiptAux aux) … invB = aux … invB := rfl; rw [haux];
simp only […]`. Each half alone passes nanoda (the generic `rfl` 0.3 s, the `simp only` part
0.1 s); `have` + `exact (haux _).trans …` fails; a top-level generic lemma + `rw`/`trans` passes.
nanoda's `infer_let` (`tc.rs`) ignores the `nondep` flag of a `have` and substitutes the value into
the body, so `haux (depositAux …)` becomes `(fun aux => rfl) (depositAux …)`: the `rfl` (type
`x = x`) is re-checked against the statement at the *concrete* `aux := depositAux accounts fallback`,
which unfolds `depositAux`'s column chain down to `depositInverse` (an `Fp` inverse) — a reduction
that does not terminate; Lean's own kernel also fails on that specialised `rfl`
(`(kernel) deep recursion detected` for `show … (depositAux …) … = depositAux … from rfl`).
The C++ kernel and lean4lean check the `have` body against `haux`'s declared type.
**Fix (proof only):** new top-level `receiptCell_dep_invB` (the generic `rfl`, for all `aux`);
`deposit_inverse_cell` = `refine (receiptCell_dep_invB … _).trans ?_; simp only […]` (same `simp`).
Statement unchanged. Further nanoda failures are searched with a skip list (the instrumented
copy skips named declarations).

Skip run 1 (skipping `deposit_inverse_cell`): next overflow at declaration 66,014,
**`Render.UpsGen.upsert_memory_growth._f`** (`Render/Ups/MemGrowth.lean`, the structural-recursion
functional of the `mutual` block `upsert_memory_growth` / `kids_memory_growth`). Also unbounded
(overflows with a 512 MiB stack). Bisected with renamed scratch copies (cases `sorry`-stubbed): the
`.leaf` and `.branch []` cases fail on their own (as plain theorems too — not a recursion issue);
in `.branch []` the `simp [PTrie.memD, PTrie.mem?, fdepth, valueMem]` step; by `simp?` lemma set,
only adding `Nat.reducePow, Nat.reduceAdd, Nat.reduceMul` breaks it (they fold
`2^65 * (fdepth … + 1)` into `73786976294838206464` inside a goal with free variables). gdb on the
isolated declaration: ~30,000 nested `TypeChecker::def_eq` frames. Mechanism: nanoda's `def_eq_nat`
compares a literal `N` with a `Nat.succ` application by recursing on `def_eq(N-1, pred)`, one frame
per unit; a `Nat` term with free variables exposes `Nat.succ` under whnf (`Nat.add x lit`), so a
comparison against a ~2^66 literal never bottoms out. (nanoda's literal arithmetic itself is
fvar-safe; the peeling path is not — the same divergence family as lean4lean above.)
**Fix (proof only):** both cases use `simp only […]` with the `simp?` lemma list minus the
literal-folding simprocs, then the original `omega`. The fixed block passes nanoda in full
(`_f`s, both theorems, `partialTrie_memory_bound`).

Skip run 2 was OOM-killed (16 G scope) inside the *old* `rec_in_int` (one 21-case proof term) —
nanoda had the same memory problem as lean4lean there; the per-case split fixes both.

### After the fixes (`c258eede`)

Rebuild: `lake build ZkFormal.V3.Integration` (all dependents), package modules rebuilt; only **18**
of the 3,964 candidate `.olean`s changed byte-wise (the 5 edited modules + 13 downstream), so the
replay dir was refreshed and those 18 re-run (all others are byte-identical to the measured ones).
TypeHashes over `ZkFormal.V3.Integration`: 0 missing, **0 changed**, 26 new (`receiptCell_dep_invB`,
`rec_in_int_0_0 … rec_in_int_2_6`, 4 private macro declarations). `AuditAdmissionV3` and the audits
of the touched theorems (`AuditSortGeneralTraffic`, `AuditRcptDepositFrame`, `AuditCodecRows`,
`AuditMemGrowth`, `AuditUpsBytes`) pass; `make pin-check` ok; package re-vendored
(`zk-formal.sha256`, 5 lines; `lean-vendor` unchanged).

Replication totals (per-run wall summed = the judge's serial time; one core per run):

| checker | verdict | runs | sum of runs | longest run | peak RSS | limits (2 h run / 4 h total) |
|---|---|---|---|---|---|---|
| leanchecker | PASS 3,964/3,964 | 3,964 | 5,425 s (1.5 h) | `CodecRecInt` 260 s | 6.9 GB (`Extract.Ups.PlanDefs`) | fits |
| lean4lean | PASS 3,964/3,964 | 3,964 | 5,729 s (1.6 h) | `CodecRecInt` 705 s | 13.6 GB (`CodecHeader`) | fits |
| lean4export | PASS | 1 | 141 s | — | 7.9 GB (NDJSON 2.87 GB) | fits (16 GiB cap) |
| nanoda | PASS (instrumented copy: 86,938 decls, no errors) | 1 | 1,471 s | — | 12.8 GB | fits |

Wall sums are upper bounds: part of the runs shared CPUs with another lane's builds, and some
lean4lean runs (`NearAirSize` 534 s, `Node…Traffic4` 522 s) ran while the shared `zkbuild.slice`
was memory-throttled (they got 13–23 % CPU). Next: the judge's own `formal-check` binary end to end.

Official `nanoda_bin` (`25906eb2…`, judge config, 8 MiB stack) on the post-fix export: **PASS**,
`Checked 86938 declarations with no typechecker errors` (plus the usual "Unable to print axioms"
pretty-printer note from `unsafe_permit_all_axioms`), exit 0, 1,485 s wall / 1,442 s CPU, 12.8 GB.

### Full judge pipeline (`target/release/formal-check`, dev bwrap sandbox, `Limits::default`)

Inputs needed beyond the repo, all scratch (nothing committed), each a deployment gap to close:

1. **Challenge pin:** the draft `near-chunk-validation-d0-stark` pins trusted tree `8f71611e…`, but
   `formal-core` + `spec/lean` now hash to `325c34af…` (spec moved on: A12, `PrepD0`, …) and no frozen
   store of `8f71611e` exists. The certificate is built against the current spec, so the run uses a
   copy of the draft with `tree_digest = 325c34af…` (and without the non-schema `draft_notes` field,
   which the strict parser rejects).
2. **No formal config for the D0a challenge:** `runners/formal-checker/challenges/` has only the D0
   config (`near-chunk-validation-d0.json`). With it, staging rejects 23 candidate modules
   (MANIFEST_INVALID: imports of `NearSpecV3.ChallengeD0a`, `NearSpecV3.PrepD0`,
   `NearSpecV3.ChunkValidationV0a`, `NearSpec.TrieUpsertProofs` are "not a candidate, trusted or
   toolchain module"). The run uses a copy whose trusted includes add exactly the package's vendored
   trusted closure (those 4 modules; 48 trusted modules in all), expected template
   `ExpectedV3D0.native-lean`.
3. **`formal/lakefile.toml` `require`** (see above): removed in the scratch candidate copy.
