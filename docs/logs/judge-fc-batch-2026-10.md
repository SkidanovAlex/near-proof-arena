# Lane `lane/judge-fc-batch` — Firecracker formal check without a per-module copy of the olean tree

Worktree `/data/illia/nearproof-wt/judge-fc-batch`, branch `lane/judge-fc-batch` from main `7e133b7d`.
User approval 2026-10-14: fix the live judge's Firecracker formal-check runner so large
candidates do not pay a per-module copy of the whole compiled tree, deploy it to the live
workers, rerun the D0a submission. Local heavy work on CPUs 10-13,26-29 only.

## Problem (docs/logs/v3-deploy-d0a-2026-10.md)

The formal checker runs every candidate module (`lean -o`) and every recheck (`leanchecker`,
`lean4lean`, one module per run) in its own sandbox run. On Firecracker each run:

* stages (copy + sha256), images (`mkfs.ext4 -d` + per-inode `debugfs`) the whole read-write
  `.olean` tree, the guest copies it into scratch, collects all of it back through the output
  device and the host rewrites every file — about five passes over the tree per module;
* re-stages (copy + sha256) every read-only dir mount before the image-cache lookup — for the
  rechecks that is the whole replay `.olean` set (3.1 GB for np-udr-stark-v2) per module;
* boots a fresh VM whose page cache is cold (imports read again at the 512 MiB/s drive limit).

For np-udr-stark-v2 (4,007 modules, 3.1 GB tree) that is O(tree) per module: live w2
(`sub_423f1e22…`, attempt 1) did 8.5 modules/min at a 0.2 GB tree and 4.7 modules/min
(≈ 13 s/module) at 0.45 GB, against 36 modules/min under bwrap, so candidate elaboration cannot
fit the 4 h `elaboration_budget`; the rechecks (2 × 4,007 runs, each re-staging 3.1 GB) would not
fit `recheck_total` either.

## Design chosen: (a)+(c) — up to 64 module runs per microVM (steps mode with a persistent rw tree)

Options considered:

* **(b) one VM per module, persistent per-job writable disk.** Keeps one VM per module, but the
  host must never mount a guest-written ext4 (hostile filesystem): the tree still has to leave
  through the output device (O(tree) once per job, at the 4 GiB output clamp for D0a), every
  later VM's kernel would mount a filesystem an earlier candidate run wrote raw blocks of (a new
  guest-kernel attack surface that single runs do not have), and every VM still starts with a cold
  page cache (each module re-reads its import closure through the 512 MiB/s drive limit) plus the
  boot and per-run staging. Rejected: more new surface, less speed-up.
* **(c) one long-lived VM per job.** Same mechanism as (a) with one batch; bounded by the guest
  protocol (`MAX_STEPS` = 64, 512 KiB step reports) and gives one VM the whole budget. (a) with
  fixed 64-run chunks is (c) cut into protocol-sized pieces.
* **(a) batches of consecutive modules (dependency order unchanged) in one VM, per-module
  timeouts enforced inside** — chosen. It reuses the existing, VM-tested steps mode (benchmark
  `vm_per_batch`), whose per-step isolation was designed for hostile provers, and extends it with
  the one piece of carried state the formal checker already has between single runs: the
  read-write output tree.

What changed (commits on this branch):

* `arena-init` (guest): steps mode accepts `rw_dirs`. Each is an overlay — lower = the seed drive
  (inodes owned by the candidate uid, as the copy of a single run's seed is), upper = a dir on the
  scratch device under the root-only `judge/` dir (outside the per-step wiped `work/`), mounted at
  the guest path; `redirect_dir=off,metacopy=off,index=off`. After the last step only the upper
  layer is collected (new or modified regular files; overlay whiteouts skipped — deletions were
  never propagated; symlinks never returned, as before). New budgets: `steps_deadline_ms` (kill
  deadline: step timeout = min(own, deadline − elapsed)) and `steps_start_deadline_ms` (no new
  step after it).
* host (`runners/firecracker`): steps with rw dirs, the deadlines, `full_capture_last` (the last
  step's stdout/stderr come from the guest's run report: the same 64 KiB capture as a single run;
  other steps keep the 2 KiB step capture — benchmark/conformance steps are unchanged, the option
  is off by default); read-only dir mounts already imaged by this process are reused while their
  metadata fingerprint (relative path, type, size, mode, mtime, ctime, inode, device, nlink of
  every entry; taken before staging and re-checked after) is unchanged.
* `arena-sandbox`: `SandboxSpec.steps: StepsOptions`; the default `run_steps` (bwrap) honours it.
* formal checker: `UntrustedRunner::run_batch` / `batch_max`. When the backend shares one
  instance across steps (Firecracker) `compile()` (trusted, reference, wrapper-stub, statement,
  candidate) and the module rechecker run up to 64 consecutive runs per VM with exactly the same
  argv, mounts, rw tree, per-run timeout (`min(module_timeout, remaining elaboration budget)` /
  `recheck_timeout`) and budgets (elaboration budget as the kill deadline; `recheck_total` as the
  start deadline, i.e. "a run starts only while the total is not exceeded", as the sequential loop
  checks it), and every outcome is judged run by run with the same code paths and messages
  (`Timeout`, `BuildFailed` with the last 1500/500 bytes, `SandboxViolation` attributed to the
  module whose step tripped it, incomplete collection = INFRA_ERROR). bwrap-dev does not batch
  (one run per module, as before). Model-closure modules (`compile_isolated`, own output dir each)
  and the native C compile/link stay single runs.
* worker: optional `ARENA_FORMAL_FC_DEPS` — a FORMAL_CHECK-only Firecracker set
  (`/data/illia/nearproof-deps/firecracker-fcbatch`: same kernel 6.1.155 and fc-runner
  `sha256:03fdfcda…` as `firecracker-rc`, rootfs built from this branch). Build, conformance,
  adversarial and benchmark keep `ARENA_FC_DEPS` (`firecracker-rc`, rootfs `bb60e932…`), so the
  benchmark environment the baselines were measured in does not change. `arena-live install`
  adds the key when the set exists.

### Isolation argument

Unchanged per run (step): a fresh process tree in a fresh cgroup, killed as a whole at its end;
scratch, `/tmp` and `/dev/shm` wiped; fresh IPC namespace; keyrings disabled; no network device;
same read-only mounts; same seccomp `Tooling` policy; same uid; same memory/pids limits and
timeouts. Carried between runs: the read-write `.olean` tree only — exactly what consecutive single
runs carried (each run's write-back seeded the next). The checker already treats that tree as
hostile: a module's `#eval`/`initialize` can rewrite any earlier `.olean` in both designs; Stage B
re-derives nothing from the elaboration but re-checks every candidate `.olean` with the kernels
(leanchecker and lean4lean replay each module against a fresh replay copy that holds only regular
`.olean` files plus links to the pristine trusted ones; lean4export + nanoda on the certificate
closure), and the NDJSON/Environment audits compare the certificate statement and every trusted
declaration hash against the judge's reference. Trusted `.olean`s are only ever reachable through
symlinks into a read-only mount (the replay dir re-links them; a guest-made file in their place
fails the write-back as before).

What a batch adds: a *guest-kernel* compromise in one step could forge the reports of the later
steps of the same VM (≤ 63 runs). A guest-kernel compromise could already forge its own run's
report and rewrite the shared tree; forging "success" of later compiles yields at most an
attacker-chosen `.olean` set — which the candidate controls anyway — and every recheck/audit
verdict that admission depends on still comes from kernels run on that set (a compromise in a
recheck VM could forge that VM's verdicts, as it could forge a single recheck run's). The guest
kernel remains the single isolation boundary, as documented (docs/ISOLATION.md §2); no documented
guarantee is weakened. The contract text "each module in its own sandbox run" now reads "… (on
Firecracker, up to 64 consecutive runs are steps of one microVM, each with a single run's
isolation; only the output tree is carried)" (runners/formal-checker/README.md).

Resource-limit notes (no `Limits`/policy change): the per-module and budget timeouts are the
same; the guest measures the budgets from its first step (after boot), so a batch may run up to
one VM boot (≈ 1 s) past where a single-run sequence would have stopped. The whole-tree 4 GiB
output clamp no longer applies to every module (only changes leave the VM); the tree stays bounded
by the seed staging limits (8 GiB / 100,000 entries) and the 8 GiB scratch.

## Measurements

### Per-module sandbox overhead (`runners/worker/examples/fc_rw_overhead.rs`, `/bin/true` runs, 1 vCPU)

| rw `.olean` tree | before: one microVM per run | after: 64 runs in one microVM |
|---|---|---|
| empty | 0.28–0.32 s / run | 0.40 s / 64 = 0.006 s / run |
| 0.48 GB (D0a after ~1,000 modules) | 9.3–11.6 s / run | 2.15 s / 64 = 0.034 s / run |
| 3.29 GB (D0a, complete) | **fails**: `GuestProtocol("bad record tag 0")` (the whole tree no longer fits the output path) | 21.1 s / 64 = 0.33 s / run |

Bytes per module, tree size T: before ≈ 5 T moved (host staging copy + sha256, `mkfs -d`, guest copy
into scratch, guest collect through the output drive, host rewrite of every file) plus a re-stage
of every read-only dir (the 3.1 GB replay set for each recheck run); after ≈ 2 T / 64 (seed staging
+ image once per batch) + the module's own new files out, and read-only dirs staged once per check
(fingerprint memo). Live w2 evidence of the old path: 8.5 modules/min at a 0.2 GB tree, 4.7/min
(≈ 13 s/module) at 0.45 GB (19:39–19:58 UTC); its FORMAL_CHECK reported at 22:44 with every gate
UNKNOWN after the 4 h budget ("sandbox refused: zero wall timeout", see below).

### D0a np-udr-stark-v2 on Firecracker, new path (`examples/formal_fc`, worker-equivalent)

`--backend firecracker --fc-deps firecracker-fcbatch` (rootfs `98868130…`, logic-identical to the
deployed `1c2a5f0f…`, which only differs by rustfmt), lean-checker image `463fdcf4…`, the submitted
package (object `2ccb946a…`), `chl_56077279…`, frozen tree `b890e835…` from the live store, public
digest `ab13c199…`, native model `NpUdrStarkV2.Model.verifier@NpUdrStarkV2.Model`, candidate binary
`e3695215…`, `Limits::from_env()` (= default), `ARENA_FORMAL_MEM_BYTES=24G`, VMs pinned to CPU 29
(1 vCPU, as live), driver on 10-13,26-29. 19:38 → 23:12 UTC.

**All six gates PASS, no findings, no warnings** (same summaries as the bwrap pre-flight), judge-built
verifier `e3695215…`, 87,078 decls. Wall 12,845 s.

| step | runs (VMs) | wall (sum of step walls) | bwrap pre-flight |
|---|---|---|---|
| trusted elaboration | 48 (1 VM) | 58 s | 54 s |
| model closure (`compile_isolated`, one VM each, unchanged) | 90 | 90 s (≈ 6 min wall incl. boot/staging) | 37 s |
| native cc / link (one VM each, unchanged) | 139 + 1 | 48 s | 41 s |
| candidate elaboration | 3,916 (62 VMs) | 5,889 s step time; ≈ 6,200 s wall (19:50–21:33) vs the 14,400 s budget | 6,698 s |
| leanchecker | 4,007 (63 VMs) | 1,792 s | 1,712 s |
| lean4export + nanoda | 1 + 1 | 108 + 636 s | 90 + 532 s |
| lean4lean | 4,007 (63 VMs) | 3,071 s | 2,061 s |
| arena-audit / ndjson-audit | 1 / 1 | 35 / 38 s | 26 / 30 s |

### Same verdicts as before (strict comparison)

`cmp.py` compares gates (status, codes, summary), findings (code, scope, severity), rechecks (id,
ran, verdict, detail); "strict" adds cache key, every evidence digest (incl. each candidate
`.olean` digest), finding details, timing step labels, warnings, runner/tier cap. Backtrace
addresses and thread ids are normalized (ASLR).

* formal-checker corpus (38 cases: 6 positive, 32 negative incl. `#eval` fake-PASS writer,
  `initialize`, prebuilt `.olean`, shadowing by module copy, `skipKernelTC`, non-terminating
  elaboration → TIMEOUT): **FC per-module path vs FC batched: strictly identical, 38/38**; bwrap-dev
  vs FC batched: identical gates/findings/rechecks 38/38; every case matches its `expect.json`.
* NEAR-formal hostile suite (`adversarial/hostile-submissions`, all 14 near-formal cases +
  the honest base `examples/reexec-witness`, materialized with `run_hostile.py --materialize`,
  on `chl_7c0456cb…` (v1-6, tree `35fbd260…`), public `38c230e8…`, judge build `9093c634…`):
  **FC per-module vs FC batched strictly identical 15/15; bwrap vs FC batched identical 15/15**;
  base PASS; additional-axiom → FORBIDDEN_AXIOM, native-decide-certificate → NATIVE_EVAL_FOUND,
  false-premise / restricted-domain / wrong-verification-key / changed-security-parameters →
  THEOREM_TYPE_MISMATCH, sorry-certificate and near-reexec-csimp-sorry → SORRY_FOUND,
  shadowed-definition → SHADOWED_DEFINITION, missing-certificate → CERTIFICATE_MISSING,
  (near-reexec-)malicious-executable and stale-certificate → ARTIFACT_BINDING_FAILED. Batched
  ≈ 55 s per case vs ≈ 95 s per-module. The sandbox-escape-* / fork-bomb / ptrace cases target
  BUILD/CONFORMANCE (`targets: ["demo"]`), not the formal stage, and run on `ARENA_FC_DEPS` unchanged.
* Tests: `arena-fc-proto`, `arena-firecracker` (lib), `arena-sandbox` (incl. new
  `default_run_steps_honours_deadlines`), `arena-formal-checker` (lib + corpus + native_route +
  formal_core + near_spec on bwrap), `arena-worker` (lib + all integration tests): pass.
  Firecracker VM suite (`ARENA_FC_TESTS=1`, 23 tests incl. new
  `steps_rw_dirs_persist_and_return_only_changes`) passes on the new rootfs; the existing
  `steps_share_one_vm_but_no_state` host-vs-guest timing assertion is flaky under load at the same
  rate on main's rootfs `9650c8a9…` (3/8 each), pre-existing. clippy clean, `make pin-check` OK.

### The live attempt-1 verdict: "sandbox refused: zero wall timeout"

The per-module path computes each module's timeout as `min(module_timeout, budget − elapsed)`; once
the budget is spent that is 0 s and the sandbox refuses the spec, so the run ended as INFRA_ERROR
(UNKNOWN) instead of the intended TIMEOUT ("elaboration of … timed out"). Contract
(docs/CONTRACTS.md §7; formal-checker README): timeouts and infra problems are UNKNOWN, never PASS;
"any UNKNOWN mandatory gate → INCONCLUSIVE"; fail-fast only after a mandatory **FAIL** — so
continuing to CONFORMANCE/ADVERSARIAL after a formal UNKNOWN, and an INCONCLUSIVE decision at the
end, is the documented behaviour. The reason code (INFRA_ERROR vs TIMEOUT) is the only defect; the
batched path reports TIMEOUT there (a step started with no budget left gets 1 ms and times out).
The bwrap per-module path still has the 0 s edge; not changed here (verdict status is the same).

## Deploy (2026-10-14 23:13–23:15 UTC)

Coordination: merged origin/main `c5ccb768` (near-chunk-v3 registered and deployed by
`lane/v3-deploy-v3` at release `a8c55352`; its oracles `near-arena-oracle-v3-d{1,3}` and the
`ARENA_NEAR_ORACLE_V3_D{1,3}` keys kept by install) before building; live `release/REVISION` was
`a8c55352` right before install; no concurrent deploy.

* Build: lane-specific target `ARENA_LIVE_TARGET=~/.cache/nearproof-live-target-judge-fc-batch`
  (never the shared one), `ARENA_LIVE_BUILD_CPUS=10-13,26-29 arena-live build` → stamp **`13d2e653`**
  (branch head, pushed). Web `pnpm run build` (no diff). Rootfs for `ARENA_FORMAL_FC_DEPS`:
  `deploy/images/rootfs/build.sh --check` (two bit-identical builds) →
  `/data/illia/nearproof-deps/firecracker-fcbatch/images/rootfs-1c2a5f0fd65b.ext4`
  (`sha256:1c2a5f0f…`, arena-init `976b1606…`; init source unchanged since `6bf7f3bf`); kernel and
  fc-runner are `firecracker-rc`'s.
* Attempt 1 (`run` of `sub_423f1e22…`): FORMAL_CHECK had reported at 22:44 (all formal gates
  UNKNOWN, "sandbox refused: zero wall timeout"), CONFORMANCE was leased on w2 (≈ 7 h, then ≈ 40 h
  benchmark, on a run already bound to INCONCLUSIVE), ADVERSARIAL done. Chosen: **cancel** through
  the documented agent path (`arena cancel sub_423f1e22…` with the submitting agent's credentials,
  never printed) at 23:12 → CONFORMANCE `cancelled` (w2 logged "cancelled by the control plane",
  its microVM ended on its own), decision CANCELLED; queue empty.
* Backups: `backups/pre-judge-fc-batch-1792019693/` (bin/, release/ at `a8c55352`, web-dist,
  config/, systemd user units), `config/*.env.bak-1792019693`, `arena-live backup` →
  `backups/20261014T231457Z`.
* `arena-live install` → `release/REVISION` **`13d2e653`**; `upgrade_config` added
  `ARENA_FORMAL_FC_DEPS=/data/illia/nearproof-deps/firecracker-fcbatch` to `worker.env`
  (`ARENA_FC_DEPS` stays `firecracker-rc`); `check-trusted` OK for all 16 challenges. No migration
  (no server change since `a8c55352`). Restarted **w1, w2, w3 only** (server/web untouched; this
  also performs the w2 restart `lane/v3-deploy-v3` left pending). Each worker logs
  "FORMAL_CHECK sandbox from ARENA_FORMAL_FC_DEPS=… (rootfs sha256:1c2a5f0f…)". Health OK.

## Rerun

`arena-live rerun-submission sub_423f1e22279f42a3a44ad5fd016237b2 "…"` →
**`run_335e1cda2a154779981267d37bbd55a0`** (23:15 UTC). VALIDATE done 23:15, BUILD PASS 23:20 (w2), FORMAL_CHECK leased by w2 at 23:20.

**FORMAL_CHECK (w2, 23:20:03 → 02:15:47 UTC, 2 h 56 min): all six gates PASS**
(FORMAL_SEMANTIC_SOUNDNESS/COMPLETENESS, FORMAL_CRYPTO_SOUNDNESS, FORMAL_IMPL_CONNECTION: "certificate
type equals the judge-constructed statement; kernel rechecks accepted"; AXIOM_AUDIT;
ARTIFACT_BINDING: judge-built verifier `e3695215…`), runner `firecracker`, no findings; report
object `sha256:4a93b8b8…`. Step walls (trusted/reference from the worker's formal-ref-cache):

| step | runs | wall |
|---|---|---|
| model closure / native cc+link | 90 / 140 | 73 s / 40 s |
| candidate elaboration | 3,916 (62 microVMs) | 5,024 s step time (≈ 1 h 30 min wall of the 4 h budget) |
| leanchecker | 4,007 (63 microVMs) | 1,736 s |
| lean4export + nanoda | 1 + 1 | 102 + 612 s |
| lean4lean | 4,007 (63 microVMs) | 2,190 s |
| arena-audit / ndjson-audit | 1 / 1 | 34 / 32 s |

Attempt 1 on the same worker had reached ≈ 1,500 of 3,916 modules when its 4 h budget ran out.

Next stages (02:16 UTC): CONFORMANCE leased by w3 (80 public positives + 3 judge-sampled + 3
held-out at ≈ 5 min/prove on 8 vCPU: ETA ≈ 09:15 UTC), ADVERSARIAL leased by w2; then BENCHMARK on
w1 (≈ 500 proves, ≈ 40 h). Not waited for.
