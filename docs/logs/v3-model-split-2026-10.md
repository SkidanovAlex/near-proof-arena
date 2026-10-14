# Lane `lane/v3-model-split` — verifier-model import closure, log

Worktree `/data/illia/nearproof-wt/v3-integ-d`, branch `lane/v3-model-split`, from `lane/v3-package`
`cd3e3e1d` (main `c6247f3d` + the v3 packaging commits), origin/main `484a2e0d` merged in
(D0a challenge config + `ExpectedV3D0a*` templates; no zk-formal change). CPUs 15,31 only.

## Problem (packaging lane, `docs/logs/v3-package-2026-10.md`)

The judge's native-lean build (`runners/formal-checker/src/pipeline.rs`, `native_build`) checks
every import of every module in the verifier model's import closure:

```
ok = tb.modules.contains(i) || model_mods.iter().any(|x| &x.name == i) || staging::has_prefix(i, "Init")
-> ARTIFACT_BINDING_FAILED "verifier model module {m} imports {i}: model modules may import only
   trusted modules, other model modules and Init (no metaprogramming in code the judge compiles)"
```

and then elaborates each model module in its own sandbox (`lean -c`, serially), `leanc -O3`s the C
and links it with the trusted C and the judge wrapper, inside the BUILD budget (`max_build_ms`,
draft 3,600,000 ms).

`NpUdrStarkV2.Model` (`(npVerifierP challengeSpecD0a nearAirV3 split prepV3b).toVerifier`)
imported `ZkFormal.NearV3.Assembly.NearAdmission`: **657 candidate modules**, including
`ZkFormal.Near.Render.Common → Std.Data.HashMap` (via `NearAir → Candidates.SortEmpty →
Render.Proof.*`); replicated native build ~67 min (contended, packaging lane).

## Method (same technique as the prune lane)

1. `DeclInfo` (scratch, like `scripts/ClosureDeps.lean` plus declaration ranges): kernel
   dependency walk from the model's roots (`npVerifierP`, `challengeSpecD0a`, `nearAirV3`, `split`,
   `prepV3b`, `TreeVerifier.toVerifier`, `AuxG.mk`): 7,903 constants, defined in **93 candidate
   modules** (of the 657). Of those, 51 import only other such modules (kept as they are) and 42
   do not; 2 of the 42 (`Near.Spec.SoundTrie`, `Sched.Spec.Canon`; also `ReexecV3D0.Size`,
   `NearV3.Spec.Codec` among the kept) contribute only realized equation lemmas of trusted
   functions (`NearSpec.takeN.eq_3`, …), which are re-realized where needed.
2. For each of the other **40** modules `M`: the needed declarations move **verbatim** (source
   text from the declaration ranges, with their docstrings/attributes and `omit … in`/`open … in`
   prefixes, inside the same `namespace`/`section`/`open`/`variable`/`set_option`/
   `attribute [local instance]` scaffolding, in the original order) into a new
   `<M>Defs` (`<M>Core` when `M` already ends in `Defs`: `V2.G.DefsCore`, `V2.PG.NpDefsCore`).
   `M` keeps everything else and imports `<M>Defs` after its own imports, so every importer
   sees the same names. `<M>Defs` imports only kept modules, other `*Defs` and trusted modules
   (the modules its constants reference). `open`s of namespaces that do not exist there are
   dropped (cannot change name resolution). Unused `variable`s are dropped.
3. `@[csimp]` fast paths: `ZkFormal.Stark.Bcs` installs `take?_eq_takeF`, `readInj_eq_readInjF`,
   `mpLeaves_eq_mpLeavesF` "before any caller is compiled" — without them the compiled verifier
   reads the proof quadratically. They are not kernel dependencies of the model, but they are
   part of what the *native* model needs, so they and their proofs (`takeF_eq`, `take?_consume`,
   `readU32s_consume`, `readFs_consume`, `readRows_consume`, `readRows_raw`, `readInjF_eq`,
   `mpLeavesF_eq`; 11 theorems, Init-only proofs) moved too, with `readInjF`/`mpLeavesF`.
   `BcsDefs` is the only new module with theorems. (A first round without them compiled, but
   `readInjF`/`mpLeavesF` then re-created their own matchers: see TypeHashes below.)
4. Matcher sharing: Lean reuses an identical `match_N` auxiliary only within a module. Two
   unneeded definitions reused matchers of moved ones (`V2.globalOkP` ← `prepP.match_*`,
   `V3.inner`); they moved along so their bodies stay identical.
5. `NpUdrStarkV2.Model` imports `NearAdmissionDefs`, `NearAirDefs`, `V2.PG.AdmissionDefs`
   (+ `NearSpecV3.ChallengeD0a`) instead of `NearAdmission`.

No declaration was edited, renamed or deleted; no proof changed; no import order of an existing
module changed except the appended `import <M>Defs`. 40 files changed in zk-formal (−2,071 lines
moved), 40 new `*Defs`/`*Core` files.

## Results

| | before | after |
|---|---|---|
| model closure (candidate modules, `NpUdrStarkV2.Model` incl.) | 657 | **90** |
| imports outside trusted/candidate/Init | 1 (`Std.Data.HashMap`) | **0** |
| proof modules in the model closure | most of them | none (only `BcsDefs`' 11 csimp-support theorems) |
| replicated native build (`build.sh`, Lean part: 48 trusted + model, `lean -c` + `leanc -O3` + link, serial, CPUs 15/31) | ~67 min (contended) | **≈90 s** |
| `out/verify` on `00-h10004-s3` | accept 2.6 s | accept 2.63 s, flipped byte rejected |
| certificate/package closure (`NpUdrStarkV2/*.lean`) | 3,964 | 4,004 (+40 `*Defs`) |

TODO judge run.

## Verification

* All 5,414 modules build (every `ZkFormal`/`ReexecV3D0` module explicitly, `ZkFormal`,
  `ZkFormal.V3.Integration`); the heavy `Codec*`/`HorizontalAuxCheck` one at a time.
* `scripts/TypeHashes.lean` now also fingerprints `def`/`opaque` values (5th column). Baseline on
  the unmodified tree (fully rebuilt here) vs after, over all modules (tool `main`s separately):
  151,619 named constants before, 151,621 after; **0 missing, 0 new, 0 changed types, 0 changed
  definition values among named constants**; 742 constants moved module. The only differences
  are 56 compiler-generated auxiliaries:
  * 25 private realized lemmas `_private.ZkFormal.Stark.Bcs.0.…match_N.{eq_k,splitter}` now
    `_private.ZkFormal.Stark.BcsDefs.0.…` (module-prefixed private names of the moved theorems'
    `split` lemmas; pairwise identical types);
  * `readRows_consume._f`, `readU32s_consume._f` (structural-recursion aux of two moved theorems)
    whose bodies mention those renamed private lemmas;
  * the private `split` lemmas `MerklePublic.expression.match_1.splitter` and
    `Sched.rawOf.match_1.splitter` (realized in the original module by its proofs, for a matcher
    that now lives in the `*Defs` module): body re-numbers a `_sparseCasesOn` helper
    (2 new `…splitter._sparseCasesOn_*`).
* TODO tests, audit, judge run.

## Package fixes (requested by the coordinator)

* `formal/lakefile.toml` removed: its `require ZkFormal` is rejected by judge staging
  (`check_lakefile_toml`, empty `allowed_requires` → MANIFEST_INVALID). As in
  `examples/reexec-v3-d*`, `formal/` has no lakefile; the vendored sources are inside it. Local
  elaboration: `conformance/lakefile.toml` gained `lean_lib NpUdrStarkV2` (`srcDir = "../formal"`).
* `NpUdrStarkV2.certificate : ArenaExpectedInst.expectedType :=
  nearV3_admission_final _ publicBin (by decide +kernel) rfl` (the judge compares the type
  syntactically); the quantified form is kept as `certificate_forall`. `#print axioms` guard kept.
