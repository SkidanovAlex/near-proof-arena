# v3-package lane (2026-10-13): np-udr-stark-v2 as a v3 D0a submission

Branch `lane/v3-package` (from main `c6247f3d`), worktree `/data/illia/nearproof-wt/v3-integ-d`.
CPUs 15,31 only. Nothing registered, submitted, signed or deployed.

## Runner contract (what the judge does; runners/worker/src/stages/{build,common}.rs)

* BUILD: `bash build-recipe/build.sh` from the package root, twice; fresh `$HOME`,
  `SOURCE_DATE_EPOCH=0`, no network, `max_build_ms` (draft: 3,600,000 ms); collects
  `[build] outputs`; the two trees must be identical. Then the judge runs `prepare` twice and
  requires identical public dirs.
* `prepare --params @in/params.bin --out @scratch/out/public`; `params.bin` = the oracle's
  approved params, pin-checked (`RequestPin::check_params_v3`: `near-arena-params-v3`,
  statement, pv, domain = the `#<domain>` suffix of `semantic_scope.name` (`D0a` for
  `near-chunk-validation-d0-stark`), runtime-config digest).
* `prove --public @in/public --request @in/request.bin --witness @in/witness.bin
  --claim-out @scratch/out/claim.bin --proof-out @scratch/out/proof.bin`; for
  `near-arena-claim-v3` request = expected_claim = claim.bin; claim must equal it byte for byte;
  proof ≤ `max_proof_bytes` (8 MiB); RSS ≤ `max_ram_bytes` (16 GiB); `max_prove_ms` 600,000.
* verify (native-lean route): the judge's own build of `[formal] verifier_model`
  (`--public DIR --claim C --proof Q`, reads `DIR/public.bin`). `out/verify` must still exist and
  be executable in the bundle.

## What changed

* `source/src/bin/prepare_v3.rs` → `out/prepare`: params must equal `NpUdrStarkV2.publicBin`
  (re-encoded from its fields; the 100 B / sha256 `ab13c199…` tape the certificate pins), else
  exit 2; writes `public.bin` verbatim. std only.
* `source/src/bin/prove_v3.rs` → `out/prove`: claim = request; proof = the `npudr v3prove`
  pipeline (case_inputs → render 25 tables → `prove_cols_bytes` at auxGroup 2 → Rust `verify`
  self-check → `join`), AIR `source/near-air-v3.json` (np-lean-export-v3, sha256 `fa599b3b…`)
  compiled in. No constraint/bus pre-check (saves ~40 s; the post-proof verify covers it). All
  failures exit 2, nothing written. v1 bins `prepare`/`prove` kept in source/ but not shipped.
* `build.sh` builds `prepare_v3 prove_v3 leanorder`; `candidate.toml`/`README.md` describe the
  v3 contract; `dependency-locks/vendor-digest.txt` regenerated (`CARGO_NET_OFFLINE=true
  build-recipe/vendor.sh`: 2,368 files, `8305b575…`); `.gitignore` ignores the dev
  `formal/lake-manifest.json`.
* `sync-lean.sh` at c6247f3d: lock files unchanged (54 trusted files, 3,960 candidate modules).

## Dry run

Package dir = git tree of `examples/np-udr-stark-v2` + `formal/{ZkFormal,ReexecV3D0}`
(sync-lean) + `source/vendor`, built with `env -i HOME=<fresh> SOURCE_DATE_EPOCH=0
CARGO_NET_OFFLINE=true bash build-recipe/build.sh` under `heavy` (16G) on CPUs 15,31.

### Build

* **Rust**: OK. `out/prepare` `c1b21dd9…`, `out/prove` `6ab59bb3…` — identical in three builds
  from three package dirs / fresh HOMEs (incl. one from the committed tree, `SKIP_LEAN=1`);
  ~1 min on 2 CPUs. Lock check `source/Cargo.lock == dependency-locks/Cargo.lock` OK; offline
  vendored build OK.
* **Lean (out/verify): FAILS** at the judge's model-import rule, replicated by `leanorder`:
  `verifier model module ZkFormal.Near.Render.Common imports Std.Data.HashMap: model modules may
  import only trusted modules, other model modules and Init`. The judge enforces the same rule in
  `runners/formal-checker/src/pipeline.rs` `native_build` (ARTIFACT_BINDING_FAILED). The model
  closure of `NpUdrStarkV2.Model` is 657 modules (it imports `NearAdmission`, where `prepV3b`
  lives); exactly one import violates the rule. Chain: `Model ← NearAdmission ← NearAirCheck ←
  NearAir ← Candidates.SortEmpty ← Render.Proof.SortLocal ← Render.Proof.SortIds ←
  Render.Proof.Base ← Render.Statements ← Render.Trace ← Render.Tables ← Render.Rcpt ←
  Render.RcptSim ← Render.Common`. `edgeUses : … → Std.HashMap Edge Nat` is used by ~10 Render
  proof modules, so the fix is in zk-formal (not this lane): cut the `NearAir → SortEmpty →
  Render.Proof.*` edge (e.g. a `*Core` split so the AIR definition does not import proof
  modules), or replace the HashMap. The prune lane's judge-time measurement (`judge-time.py`)
  mirrors `compile()` only and did not run this check.
* With the rule relaxed to allow `Std` (scratch copy only, leanorder patched; not committed) the
  replicated native build completes: 48 trusted + 657 model modules, `lean -c` + `leanc -O3`
  serial, **67 min wall** (3.6 GB RSS) on CPU 15/31 while another lane's lean jobs shared
  8-15,24-31 and the prover ran alongside. `max_build_ms` is 60 min, and this recipe compiles
  the model closure serially; on an idle core it may fit, but it is marginal (estimate:
  elaboration alone ≈ 626 s single-core from the prune lane's `times.tsv`, plus C emission and
  `leanc -O3`). `out/verify` `aab31190…`.

### prepare

* params = `NpUdrStarkV2.publicBin` (extracted from PublicBin.lean): exit 0, twice, identical
  `public.bin` == params (sha256 `ab13c199…`). D0-domain params (reexec-v3-d0's) and empty
  params: exit 2.

### prove + verify (CPUs 15,31, `heavy` 16G, no NPUDR_MEM_GB = prover default 11)

| case | kind | prove wall | user | max RSS | proof B | out/verify (native-lean, vendored sources) | np-lean-verify-v3 | negatives (flip mid byte, other public.bin) |
|---|---|---|---|---|---|---|---|---|
| 00-h10004-s3 | quiet | 3,903 s* | 2,170 s | 10.6 GiB | 5,256,829 | accept 2.6 s | accept | both rejected |
| 00-h10008-s3 | 4 transfer receipts | 1,342 s | 2,291 s | 11.0 GiB | 5,554,125 | accept 3.1 s | accept | both rejected |
| 00-h10006-s3 | missing chunk (implicit) + receipt | 1,342 s | 2,305 s | 10.9 GiB | 5,551,580 | accept 3.3 s | accept | both rejected |
| 00-h10035-s3 | largest witness (814 receipts) | 1,515 s | 2,592 s | 11.6 GiB | 5,674,156 | accept 2.9 s | accept | both rejected |

\* contended with the native Lean build and another lane's lean jobs on the same CPUs.
claim.bin == expected claim on all four; all proofs ≤ 8 MiB; peak RSS ≤ 11.6 GiB < 16 GiB
`max_ram_bytes` at the default budget. The 00-h10004-s3 proof is byte-identical to the earlier
`npudr v3prove` proof (conformance/out-v2/prove). These are 2-CPU timings, not judge timings;
earlier 8-CPU runs took 710–750 s, above the draft's `max_prove_ms` 600,000 (perf lane).

### rejections (prove on public-d0a mutants with expected_rel_d0a = false)

* `c.dup_bw_request` (×3), `w.empty_pre_state`, `w.foreign_routed_receipt` (×2): exit 2 in
  seconds, nothing written.
* `w.path_depth_over` (×2): NOT refused early — hintOf/prepD0 accept, the prover starts proving
  (killed at the 300 s timeout). The AIR (A10 depth bits) makes the proof invalid and the
  post-proof Rust self-check would exit 2 after a full proof; sound, but wastes a prove budget.
  Only 11 of the 299 mutants were run (time).

### Formal side

Not elaborated here (2.4 h single-core). Relied on the prune lane's judge-style measurement
(`docs/logs/v3-prune-2026-10.md`: 3,964 modules, 8,734 s single-core, certificate +
`#print axioms` guard elaborated) on byte-identical sources: `sync-lean.sh` at c6247f3d
reproduces `dependency-locks/zk-formal.sha256` and `lean-vendor.sha256` exactly. Checked here:
every import of the 657-module model closure resolves to formal/, the vendored trusted tree or
Init — except the one `Std.Data.HashMap` above; and the replicated native build compiles
and links them.

## Open questions

1. **Blocker**: `Std.Data.HashMap` in the model closure (above) — zk-formal fix, or a judge-policy
   decision to allow `Std` in model closures.
2. Build time: the replicated serial native build of the 657-module model closure is ~1 h on a
   shared core vs `max_build_ms` 1 h. `out/verify` is not used on the native-lean route (the
   judge builds its own), so the recipe could ship a stub `out/verify`, but that departs from
   the reexec-v3-d0 precedent: decide.
3. Which challenge: `near-chunk-validation-d0-stark` (scope `#D0a`, params domain `D0a`, what
   the certificate and `prepare` pin) vs `near-chunk-v3` (coverage-tiered, scope `#D3a`, no D0a
   tier; would need params domain `D3a`, exit 3 `UNSUPPORTED` for out-of-tier claims, and a
   different certificate). Neither is signed; `challenge` in candidate.toml stays a TODO.
4. `oracle/fixtures/v3/public-d0a` has no `params.bin`; the judge's v3 oracle reads
   `<fixtures>/params.bin`. The dry run used the PublicBin.lean bytes;
   `spec/tools/params_bin_v3.py` has no `D0a` entry.
5. The d0-stark draft has `allowed_packages: []`; `build.sh` assumes the trusted set
   ArenaCore/NearSpec/NearSpecV3 (48 modules in the closure).
6. Prove time vs `max_prove_ms` (perf lane) and memory budget: prove runs with the default
   `NPUDR_MEM_GB` (11) since the judge passes no environment.
