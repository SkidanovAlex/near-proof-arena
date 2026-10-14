# Lane `lane/v3-deploy-d0a` — deploy the signed D0a challenge, submit np-udr-stark-v2

Worktree `/data/illia/nearproof-wt/v3-deploy-d0a`, branch `lane/v3-deploy-d0a` from main `0b4c499d`.
User approval 2026-10-14: register + deploy `chl_5607727929ca2c634a92c3f0bd4bdeb6`
(`near-chunk-validation-d0-stark`, signed, trusted tree `b890e835…` already frozen into the live
store) and submit `examples/np-udr-stark-v2` for a real admission run. Local heavy work on CPUs
8,24 only (heavy wrapper); live w1 owns 0-7,16-23.

## Pre-flight (local)

### Packaging

* `build-recipe/sync-lean.sh` at `0b4c499d`: 48 trusted + 4,002 candidate modules; no change to
  `dependency-locks/{lean-vendor,zk-formal}.sha256` (git clean). The 48 vendored trusted `.lean`
  files are byte-identical to `trusted-trees/b890e835…`.
* `build-recipe/vendor.sh` (offline, warm cache): digest `8305b575…` = committed
  `dependency-locks/vendor-digest.txt`; 2,368 files, 39 MB. Package (git tree + generated
  trees, minus target/out/.lake): 75 MB.
* `build.sh` clean (`env -i`, fresh HOME, `SOURCE_DATE_EPOCH=0`, CPUs 8,24): rc 0 in 3 min 5 s;
  `out/prepare` `c1b21dd9…`, `out/prove` `efdf0b6a…`, `out/verify` `e3695215…` (= the judge-built
  verifier digest of the model-split run).
* Fixture digests: `arena-public-d0a` TreeDigest `865949a6…` = the challenge's `public_fixtures`;
  `nearproof-deps/heldout/near-chunk-validation-d0-stark` `56e6f599…` = `heldout_commitment`.

### prepare / prove / verify (built `out/*`, `env -i`, heavy 13G, **1 CPU** (24))

| case (arena-public-d0a) | prove wall / user | max RSS | proof | claim == expected | out/verify | flipped byte |
|---|---|---|---|---|---|---|
| `00-h10007-s3-w.path_depth_at_bound` | 1,475 s / 1,284 s | 11.9 GiB | 5,549,140 B | yes | accept, 4 s | reject (rc 1) |
| `01-h10025-s2-w.dup_key_last_good` | 1,503 s / 1,342 s | 11.9 GiB | 5,642,881 B | yes | accept, 5 s | reject (rc 1) |

`prepare` exit 0, `public.bin` == `params.bin` (`ab13c199…`). Single-core timings; the judge runs
8 vCPU (perf lane: 263–312 s on 8 dedicated vCPU, cap `max_prove_ms` 600 s). RSS is within
`max_ram_bytes` 16 GiB.

### Deploy-script / web changes on this lane (no Rust change: binaries = main `0b4c499d`)

* `3e6f05fe` `deploy/live/arena-live`: the release snapshot includes
  `oracle/fixtures/v3/arena-public-d0a`; `install` adds it to `ARENA_FIXTURES_DIRS` and
  `nearproof-deps/heldout/near-chunk-validation-d0-stark` to `ARENA_HELDOUT_DIRS`. Without it the
  worker finds no fixtures dir with TreeDigest `865949a6…` (fail-closed INFRA_ERROR).
* `9da1032a` `web/src/generated/drafts.ts`: the web build regenerates it from the committed
  near-chunk-v3 draft (main's copy predated the D0a tier); committed so `install`'s clean-tree
  check passes.

### Judge formal check (`formal-check` from this release build, D0a config, `Limits::default`, native-lean)

`--formal <package>/formal --certificate NpUdrStarkV2.certificate --challenge
challenges/chl_5607727929ca2c634a92c3f0bd4bdeb6.json --challenge-config
runners/formal-checker/challenges/near-chunk-validation-d0-stark.json --trusted-store
/data/illia/nearproof-live/trusted-trees` (the frozen `b890e835…`, copied and re-verified as the
worker does) `--public-digest ab13c199… --native-model NpUdrStarkV2.Model.verifier@NpUdrStarkV2.Model
--candidate-native-binary out/verify`, dev bwrap, CPU 8 (8,24 from the recheck phase), heavy 11→22G.

**exit 0, no findings, no warnings; all six gates PASS** (FORMAL_SEMANTIC_SOUNDNESS/COMPLETENESS,
FORMAL_CRYPTO_SOUNDNESS, FORMAL_IMPL_CONNECTION: "certificate type equals the judge-constructed
statement; kernel rechecks accepted"; AXIOM_AUDIT; ARTIFACT_BINDING: judge-built verifier
`e3695215…` = the package's `out/verify`). Wall 3 h 18 min (15:12–18:31 UTC); peak memory of the
scope ≤ ~7 GB.

| step | wall |
|---|---|
| candidate elaboration (4,007 modules, serial) | 6,698 s (slowest `Render.Ups.GWalk` 195 s, `Render.Node.Links` 149 s, `Render.Ups.GPlan` 86 s) |
| trusted elaboration / model elaboration / native cc | 54 s / 37 s / 41 s |
| leanchecker (4,007 runs) | 1,712 s, accepted |
| lean4lean (4,007 runs) | 2,061 s, accepted |
| lean4export + nanoda | 90 s + 532 s, accepted |
| arena-audit / ndjson-audit (87,078 decls) | 26 s / 30 s, accepted |

All within `Limits::default` (1 h/module, 4 h elaboration, 2 h/recheck run, 4 h/rechecker).

## Deploy (2026-10-14 18:31–18:35 UTC, queue empty, nothing leased)

* Build: `ARENA_LIVE_BUILD_CPUS=8,24 deploy/live/arena-live build` (stamp `9da1032a`; Rust sources =
  main `0b4c499d`), web `pnpm install --frozen-lockfile && pnpm run build` (CPU 24).
* Backups: `backups/pre-d0a-deploy-1792002715/` (bin/, release/ at `64713b80`, web-dist, config/,
  systemd user units); `config/*.env.bak-1792002715`; `arena-live backup` →
  `backups/20261014T183158Z` (its rotation dropped the three oldest dated backups, as nightly).
* `deploy/live/arena-live install` → `release/REVISION` `9da1032a`; `worker.env` +=
  `ARENA_FIXTURES_DIRS …/arena-public-d0a`, `ARENA_HELDOUT_DIRS …/near-chunk-validation-d0-stark`
  (install's `upgrade_config`); `check-trusted` OK for all 15 challenges incl.
  `chl_56077279… → trusted-trees/b890e835…`. `migrate` (no new migration). Restarted
  server, w1, w2, w3 (web: nginx reloaded by install). Health OK, tailnet `/v1/admin` 403.
* Registration: the signed `challenges/chl_56077279….json/.sig` is in the release snapshot
  (git archive of `challenges/`); `arena-admin verify` (local + dev governance keys, security dir)
  OK — warning "no baseline yet: scores are null"; the server lists it (`registered_by
  challenges-dir`, open, formal). Installed: `release/runners/formal-checker/challenges/
  near-chunk-validation-d0-stark.json` (= repo), fixtures TreeDigest `865949a6…`, the
  `ExpectedV3D0a{,.native-lean}` templates come from the frozen tree. `/v1/challenges/chl_56077279…`
  200 on :8470, :8473 and the ts.net URL; the web challenge page renders (headless Chrome).

## Submission

`arena submit <package> --challenge chl_5607727929ca2c634a92c3f0bd4bdeb6` (release CLI, `env -i`,
agent `reference`): **`sub_423f1e22279f42a3a44ad5fd016237b2`**, upload 7,682,701 B
(`sha256:2ccb946a…`), package TreeDigest `69be71c7…` (6,712 files, 60.5 MB). The package is the git
tree of `examples/np-udr-stark-v2` at `0b4c499d` plus `sync-lean.sh` / `vendor.sh` output.

### Live run (`sub_423f1e22…`, attempt 1)

| stage | worker | time (UTC) | result |
|---|---|---|---|
| VALIDATE | w2 | 18:33 | PKG_WELLFORMED PASS (6,712 files, 60.5 MB) |
| BUILD | w2 | 18:33–18:37 (4 min 44 s) | BUILD_REPRODUCIBLE PASS (two identical builds, tree `aab2159d…`; prepare 8 ms, public dir 100 B `0a4102d4…`) |
| FORMAL_CHECK | w2 | from 18:37 | running — **will not fit the 4 h elaboration budget** (below) |

**Blocker (needs a decision; nothing changed on live): the Firecracker formal check is quadratic in
the candidate's `.olean` tree.** The checker elaborates each candidate module in its own sandbox
(`runners/formal-checker/src/pipeline.rs`, one `lean -o` run per module) and on Firecracker every
run re-stages the whole writable `.olean` tree into a fresh ext4 seed image and copies it back out
(`runners/firecracker/src/sandbox.rs`, "rw dirs: seed images (uncached; contents change every
run)"). For np-udr-stark-v2 the tree grows to **3.1 GB** (4,007 modules; local `cand-out`), so the
per-module cost grows with progress: measured on w2 at 19:00–19:08 UTC ≈ 8.5 modules/min (~7 s per
module, tree 198 → 260 MB, CCD1 CPUs ≥ 64 % idle — I/O/VM-bound, not CPU-bound), vs 36 modules/min
for the same elaboration under bwrap (6,698 s total). Projected candidate elaboration on Firecracker
≫ 7 h, while `Limits::default` caps elaboration at 4 h wall (`start.elapsed()` includes the VM
overhead) — expected outcome: `TIMEOUT` finding ("elaboration of … timed out") on the formal gates
around 22:40 UTC; the tree would also approach the 4 GiB Firecracker output clamp. The local
bwrap pre-flight (same binary, same limits) passes, so this is judge infrastructure, not the
candidate. Options (user/lead decision): (a) judge fix — elaborate a batch of modules per VM (or
keep the rw tree on a persistent per-job drive instead of re-imaging it per run), then
`arena-live rerun-submission sub_423f1e22… "<reason>"`; (b) raise `ARENA_FORMAL_ELAB_SECS` on the
workers (a judge-budget change; still quadratic I/O, likely > 10 h); (c) run FORMAL_CHECK on a
bwrap formal worker (not allowed at formal tier on live).

Forward risks for the later stages (not yet reached): CONFORMANCE proves every public positive
(80) + 3 judge-sampled + 3 held-out at ~5 min each on 8 vCPU (~7 h) on w2/w3, whose CPUs 9-15 /
25-31 other lanes also use (the 600 s `max_prove_ms` has ~2× headroom only on idle cores);
BENCHMARK at batch 8 × (3 warm-up + 15 measured + 1 cold) runs × 3 classes is ≈ 500 proves ≈ 40 h
on w1.
