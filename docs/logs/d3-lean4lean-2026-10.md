# D3α reference: lean4lean admission blocker (lane `lane/d3-lean4lean`, 2026-10-13)

Goal: make the D3α reference (`examples/reexec-v3-d3`) pass all three rechecks (leanchecker,
nanoda, lean4lean) by proof-only refactoring. No checker limit, option or policy changes.

## 1. Reproduction

Worktree build (`examples/reexec-v3-d3/source/verifier`, `lake build ReexecV3D3.Logged.WasmStepE`),
then the arena's own lean4lean binary (sha256 `bab5916d…`, tools cache
`~/.cache/arena-formal-checker/leanprover--lean4---v4.34.1/57218f6d040706e1/bin/lean4lean`, default
fuel):

```
lake env <lean4lean> ReexecV3D3.Logged.WasmStepE
lean4lean found a problem in ReexecV3D3.Logged.WasmStepE:
at ReexecV3D3.Logged.W.E_exec: (kernel) deep recursion detected, use `set_option maxRecDepth <num>` to increase the limit
```

Same verdict as the configured formal report (`RECHECK_FAILED`, batch 40 of 72). With
`--config:recDepth=100000` (diagnosis only, never used for admission) the isolated memCopy
equation is accepted, so the required depth is between 50,000 (lean4lean's default `recDepth`) and
100,000.

## 2. Root cause

Isolating instructions (`exec … .X = body` by `rfl`, each case of `E_exec` separately):
only `.memFill` and `.memCopy` fail; `memInit`, `tableInit`, `store`, `memGrow`, … pass.
The Lean-generated equation lemmas `exec.eq_36` / `exec.eq_37` (realized by `simp only [exec]` in
`WasmStepE`, and replayed by lean4lean in the module that realizes them) fail in the same way.

An instrumented copy of lean4lean (scratch only; prints the call stack near the fuel limit) shows the
chain: two non-syntactically-equal applications of the shared matcher `enter.match_3` on
`memCopy s d src n` (or `memFill …`) are compared; matchers have `abbrev` hints, so lazy delta unfolds
both instead of comparing arguments; `Res.rec` iota needs `whnf (memCopy …)`, which reduces the
bounds check `src + n > memBytes s`, and `memBytes s = s.pages.size * 65536`. lean4lean's
`reduceNat` whnf's both arguments of `Nat.mul`/`Nat.add` looking for literals **without** the C++
kernel's `has_fvar` short-cut, so `Nat.mul x 65536` (x symbolic) unfolds the structural recursion on
65536 one nested level at a time: 65,536 nested calls > 50,000 fuel. (memInit/tableInit check
`data.size`/`table.size` first and get stuck before `memBytes`.) This is a lean4lean divergence, not
an ill-typed term; leanchecker and nanoda accept.

## 3. Proof-only refactor (`formal/ReexecV3D3/Logged/WasmStepE.lean`, `E_exec` only)

* `exec` is unfolded with `exec.eq_def` / `unfold exec` (as `WasmStep` already does), never with
  `simp only [exec]`, so `exec.eq_36/37` are no longer realized in the candidate closure.
* `memFill`/`memCopy` cases: after `rw [exec.eq_def]` the new tactic `opaque_gen memFill hE`
  abstracts the constant into a variable `mf` and proves the goal from
  `key : ∀ mf, (∀ t d v n, mf (E σ t) d v n = mapRes (E σ) (mf t d v n)) → G[mf]`, bound by a
  non-dependent `let` (a `generalize` does not work: `instantiateMVars` beta-reduces the constant back
  in). The kernel checks `key` with `mf` free, so no reduction reaches `memBytes`. The rest of the
  case is the original rewriting (`E_popN`, `E_memFill`/`E_memCopy`, `E_setFrame`).
* Statement of `E_exec` and every other declaration unchanged.

Lessons from the earlier attempt (`/data/illia/nearproof-deps/validation/v3-read-reference-20261007/
proof-refactor-experiment`): `as_aux_lemma` and `rw [exec.eq_def]` alone only move the failure
(`_proof_1_96`, then `exec.eq_37`, then `exec_memFill_eq`); any proof where the kernel must compare a
`match memFill …`/`match memCopy …` against a differently-normalized copy fails.

Provenance: the candidate Logged library is a recorded transform of upstream
`spec/lean/v3/NearSpecV3/Logged` (`77b844e0`). `source/verifier/sync-logged.py` now applies recorded
proof-only patches (`source/verifier/logged-proof-patches/*.json`, exact old/new text) after the
transform and records their hashes in `dependency-locks/logged-candidate.json`; `--check` passes.
Upstream `spec/` (pinned) is untouched.

## 4. Results (all on the worktree, CPUs 12-15 via `heavy`)

* `lake env <lean4lean> ReexecV3D3.Logged.WasmStepE` → `checked 194 declarations` (was: deep
  recursion at `W.E_exec`).
* Configured formal check, judge pipeline, default `Limits`, unchanged policy:
  `/data/illia/nearproof-deps/validation/d3-lean4lean-20261013/formal-check.sh`
  (`formal-check --challenge challenges/drafts/near-chunk-v3.draft.json --challenge-config
  runners/formal-checker/challenges/near-chunk-v3.json --repo-root <frozen tree 03fb64fd…>
  --public-digest b10e9585… --native-model ReexecV3D3.Model.verifier@ReexecV3D3.Model
  --declared-tier D3a`). Report sha256 `279158aa…`:
  all six gates PASS; leanchecker accepted (72 modules / 72 runs), nanoda accepted, lean4lean
  accepted (72 modules / 72 runs), arena-audit and ndjson-audit accepted (12,718 decls). Closure axioms
  {propext, Classical.choice, Quot.sound}. Judge-built `verify` sha256 `f661d7b8…`, model closure
  digest `063b6c17…` (both unchanged).
* Clean `build-recipe/build.sh` in a copy of the package: `prepare 8341e9de…`, `prove 8010f24e…`,
  `verify f661d7b8…`, byte-identical to the recorded post-split binaries, so the post-split public
  (407+244, 3,062 mutations) and held-out (208+64, 1,433 mutations) strict results apply unchanged.
* `lake env lean test/AuditReadLocal.lean`: passes, with new guards for `W.E_exec` and `W.E_step`
  (only propext/Classical.choice/Quot.sound). `#print axioms ReexecV3D3.certificate` unchanged.
* `sync-logged.py 77b844e0 --check`: verified 39 modules (with the recorded proof patch).
* `make pin-check`: pass. No change under `spec/`, `formal-core/`, `oracle/`, `challenges/`.

Possible upstream follow-up (not needed for admission): lean4lean's `reduceNat` could skip terms with
free variables like the C++ kernel; that would be a checker change and is out of scope here.
