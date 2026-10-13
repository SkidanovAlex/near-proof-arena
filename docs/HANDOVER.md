# NEAR Proof Arena — handover (updated 2026-10-13)

This is for the next lead agent. Read it first. The raw working log for 2026-10-07 to 2026-10-09 (≈6,500 lines) now lives in `docs/logs/v3-progress-log-2026-10.md`. Use it only for evidence lookup.

**Rule for this file:** keep it short and current. Append progress to `docs/logs/`, not here.

## 0. Goal and standing user directives

**Goal.** A self-hostable arena where candidates submit NEAR state-transition provers. Each submission comes with a machine-checked Lean certificate. The judge independently builds the submission, checks it formally (fixed trusted root), tests it, and benchmarks it.

**Current target.** A **succinct proof of a NEAR chunk state transition, with a formal proof of correctness.** It must be a drop-in replacement for the stateless validator's `validate_chunk_state_witness`.

User directives (binding):
* **Don't shortcut.**
  * Use explicit, decidable domain conditions rather than hidden assumptions.
  * Prove things where possible; don't settle for testing alone.
  * Never loosen measurement rules to make something pass.
* **Proof size and verify time are first-class.** Proofs must be succinct.
* **One challenge.** `near-chunk-v3` covers the whole chunk transition with coverage tiers D0a < D0 < D1 < D2 < D3α. Do not create one challenge per domain.
* **The strategic value of ZK** is one proof across *all* shards, which standard validator hardware cannot re-execute. Single-proof capacity (`G_α`) is the key metric.
* **Recursion: R5.** No proof composition and no bounded R1. Single-proof capacity is raised through the prover, table and verifier levers listed in `docs/requirements/D3_WASM_REQUIREMENTS.md` §2.4.
* **Decisions already taken by the user:**
  * Price model: N_v = 50 validators **per shard**.
  * B0 = 2.0 MB for D0a.
  * A8 is in RelD0a.
  * A9 and A10 are in RelD0a (2026-10-09): ChaCha words drawn by all scheduler runs ≤ W0 = 770,000, and every used source Merkle path ≤ Dp0 = 32 items.
  * D3 error kinds count as one failure; floats come in a later stage; block facts are derived from headers.
  * 2026-10-11: **A11 `w.post_rebuild`** in RelD0a (no SHA-collision shadow changes the A7 post rebuild);
    **A7's measure** is the unfolded pre trie plus the whole rebuilt post trie (was position-matched
    `diffT`); A7 and A10 are **enforced in the AIR** (A10 by a depth counter in `srcpV3`, A7 by running
    sums checked against B0 in `sizeV3`); the **rcpt repairs** (13-bit deposit age, gated gas surplus) are
    adopted. `nearAirV3` may be revised to make soundness and completeness hold.
* **Security and operations:**
  * Repo: GitHub `ilblackdragon/near-proof-arena`, private.
  * Remote access is through `tailscale serve` only, never funnel. Everything binds to loopback.
  * Keys and secrets live outside the repo. Never print keys, env files or env vars.
  * Never modify signed challenges (`challenges/chl_*.json`), the frozen `oracle/v3`, or any pinned file. `make pin-check` must pass.

## 1. Host rules (the host OOM-crashed twice; follow these strictly)

* **Run heavy builds through the wrapper:** `HEAVY_MEM=16G taskset -c 8-15,24-31 /data/illia/nearproof-deps/bin/heavy <cmd>`.
  * The wrapper is a systemd scope in `zkbuild.slice` with a 48G cap, and `mem-watchdog` runs alongside.
  * Use `HEAVY_MEM=32G` only for the D2 kernel-eval proofs.
  * At most about 3 lanes, and at most 2 heavy builds per lane at a time.
* **CPUs 0-7 and 16-23 are reserved for the live benchmark worker w1.**
  * Stop w1 only in short, logged windows with an empty queue (`docs/LIVE.md` §5f).
  * If a run is interrupted, restart w1.
* **Disk:** `/` is at **98%** (20 GB free) and `/data` at **90%** (2026-10-11).
  * Delete merged worktrees and their `target/` dirs.
  * Session scratchpads under `/tmp/claude-1002/...` are large (`lean`, `npai-e2e`, `elan` ≈ 25 GB) and can go once you have confirmed nothing needs them.
* **Merging:**
  * Use explicit `git add <paths>` only; other agents work in worktrees. Check `git status` before committing.
  * Merge lanes to main **before** installing live.
  * Run `cargo fmt --check`, clippy with `-D warnings`, the affected tests and `make pin-check` before pushing.
  * Commit trailer: `Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>`.
* **Worktrees:** lanes live in `/data/illia/nearproof-wt/<lane>`, one per concurrent agent. Never share a worktree between agents.
* **Helper:** `/data/illia/nearproof-deps/bin/resolve-members.py` resolves `Cargo.toml` member conflicts.


## 2. Repository state

* **2026-10-11 (evening):** `integration/v3-20261011b` merged into main: `lane/v3-a11` (A11, A7 measure,
  `factorComplete`), `lane/v3-link` (ExtractV3Stmt at B0, v1-style `LinkV3Stmt`, `extractV3_of_link`,
  `LinkClaim`), `lane/v3-render-rcpt` (acct/size/srcp/qv renders, cap changes, A10 counter, rcpt repairs),
  `lane/v3-render-sched` (sha/ChaCha/mrk/sort/mem/cmp/ups renders, ChaCha 22, empty-capable mrk/sort),
  `lane/v3-render-asm` (`RenderBundleV3`, `CompleteV3Stmt`, `nearV3_admission_of`). See §5 and §6.
* **2026-10-11:** `integration/v3-20261011` merged into main:
  * `lane/v3-prover` at `5347fed3`: Rust prover part 1, `examples/np-udr-stark-v2/` (forked from the live `np-udr-stark-fast2`). It adds `auxGroup` g ∈ {1,2,3}, the `np-air-v2` format with public segments and `maxPub`, `pubFit` checked before any record is enumerated, and public messages in the bus equation. `conformance/run-v2.sh`: the deployed Lean v2 verifier (`np-lean-verify-v2`) accepts the Rust proofs at g = 1/2/3 and rejects them under the other g, plus 9 proof and 5 claim mutations per case (166/166). Rust's per-table layout of `nearAirV3` equals Lean's (`np-lean-export-v3 --layout g`) for all 25 tables. The inherited v1 suite passes 205/205. See its `README.md`.
  * `agent/v3-assembly` at `5ef6767d`: the `RenderV3` obligation types, `HoldsP` assembly from per-table traffic, the `traceSum` composition, and head/walk `maxLog` raised to 13/22. The lane is still active; merge its next commits the same way.
* **2026-10-10:** `integration/v3-20261010` merged into main:
  * `agent/v3-assembly` at `85a02cb1` (committed tip only), which includes `RcptV3ViewStmt` (rcpt-view package done), all per-table views from `HoldsP`, and the `LinkV3` interface. The lane is **still active**: an agent has uncommitted work in `/data/illia/nearproof-wt/integration`, so don't touch that worktree. Merge its next commits the same way.
  * `NearV3/Candidates/ProcActualGrantOperands` was fixed (binder type annotations) and committed; it was the one module that failed to build on 2026-10-09.
  * New guarded audit `zk-formal/test/AuditNearV3Admission.lean`.
* **main** (2026-10-09) contains everything below. It was merged from `integration/v3-20261009` on 2026-10-09, which combined:
  * `lane/v3-air`, `lane/v3-hpl`, `lane/v3-assembly`, `lane/v3-qvals`, `lane/v3-public`;
  * `lane/v3-d3`;
  * `codex/near-state-proof-20261008`, which was recovered from the local bundle `checkpoints/near-state-proof-20261008.bundle` because the codex sandbox could not push;
  * the uncommitted work that sat in the main checkout: about 160 newer files, the web Research page and the PR template.
* **Merge checks:**
  * Conflicts were limited to import lists, axiom-audit files and status docs. They were resolved by taking the union, with duplicates removed.
  * Every `import ZkFormal.*` resolves.
  * No new `sorry`, `axiom`, `native_decide` or `implemented_by`.
  * `make pin-check` OK. Rust: fmt, clippy `-D warnings` and 355 workspace tests pass.
  * Lean build of all ZkFormal modules: see §6.
* **Not merged, on purpose:** two old WIP commits that don't build, kept on origin:
  * `lane/v3-trie-h` `1d8b2f12`;
  * `lane/v3-rcpt-h` `4ae51a13`.
* **Live arena:** reinstalled on 2026-10-10 from main `64713b80`, to serve the web Research page (`deploy/live/arena-live build`, web build, `install`, `migrate`, `restart`; health OK, workers w1–w3 active). No challenge was signed or registered; the v3 challenge is still a draft.

## 3. What is DONE

* **v1 arena: milestones A–D, live.** NPAI (CHECKED) and native-lean routes. The succinct STARK np-udr-stark is formally admitted; it is a validity proof, not zero-knowledge.
* **Cost scoring:**
  * governed price model `pm-near-mainnet-2026q4@v2` (N_v = 50 per shard);
  * paired baseline control and pinned calibration (bench-spec-v1.6);
  * v1-7 cost board live.
* **v3 D0 (`chl_4b431651…`):** the proven normal-form reference and its fast child (rank 1) are ADMITTED.
* **v3 spec ladder:** D1, D2 and D3α, each difftested three ways (nearcore / Lean / Python) with 0 disagreements. RelD0a has B0 = 2.0 MB and A1/A2/canon0f/A7/A8.
* **Read-logging checker** (`checkD2L_eq`, `checkD3L_eq`, plus the stack-safe WASM loop):
  * proved equal to the trusted checker;
  * D3: the 115,284 saved results reproduce;
  * fresh D2 regressions recorded over both the D2 corpus and the D1 corpus;
  * WASM and trie harness parity recorded.
* **D3α read-set reference** (`examples/reexec-v3-d3`):
  * complete read-set normalisation is proved, with a single run;
  * strict public and held-out worker gates pass;
  * all 3,062 mutations rejected, including unread-value and unread-code injection.

## 4. Stream A: unified challenge `near-chunk-v3`

**Design.** One challenge whose statement is `RelD0 ∨ RelD1 ∨ RelD2 ∨ RelD3`. Candidates declare a tier, D0a < D0 < D1 < D2 < D3α, and may abstain outside it. Ranking is by tier, then cost. See `CONTRACTS.md` §11 and `BENCHMARK_SPEC.md` §17.
* **Draft:** `challenges/drafts/near-chunk-v3.draft.json`, unsigned.
* **Class weights:** ASSUMED until a mainnet replay measures them.
* **Known limitation:** four transcriptions are trusted. The follow-up is to make `Rel_Dk := RelD3 ∧ InDk`.

**Blockers, in order:**
1. ~~lean4lean fails on the D3α reference~~: fixed proof-only on `lane/d3-lean4lean` (2026-10-13). The configured
   formal check passes every gate; leanchecker, nanoda and lean4lean accept all 72 modules at default limits;
   native binaries are byte-identical. Root cause and evidence: `docs/logs/d3-lean4lean-2026-10.md`.
2. **The D0a tier needs real workload-class coverage in the draft.** An empty class list would silently allow abstention on every input.
3. ~~Domain bounds A9/A10~~: merged to main (`b06167fa`), with difftests showing 0 disagreements.
4. **Freeze, then measure, then release:**
   * freeze once;
   * run the joint w1 paired-baseline window with the cost tooling;
   * sign, register and deploy;
   * submit the reference (expect ADMITTED) and `near-v3-d3-lenient-codes` (expect REJECTED);
   * record the results.

## 5. Stream B: succinct D0a STARK (np-udr-stark-v2), the critical path

**Location:** `zk-formal/ZkFormal/NearV3/` (Assembly, Candidates, Rcpt, Qv, Render, Sched, Extract, Link, Public) and `ZkFormal/V3`, `ZkFormal/Size`.
* About 5,000 modules. Integration target: `ZkFormal.V3.Integration`.
* About 2,400 axiom-audit files in `zk-formal/test/`. Run each with `lake env lean test/<file>`.

**State (2026-10-12, main `abf81215`): the D0a certificate is unconditional.**
`Assembly/AdmissionV3.lean:nearV3_admission_final` proves the `AdmissionStatement` of
`near-chunk-validation-d0-stark` from only `hpub` (public digest binding) and `himpl` (the artifact's
implementation connection). Soundness `extractV3 : ExtractV3Stmt` (`Assembly/ExtractV3Proof.lean`)
and completeness `completeV3 : CompleteV3Stmt` (`Render/CompleteV3Chacha.lean`) are both proved.
Guarded audit `test/AuditAdmissionV3.lean` (only propext/Classical.choice/Quot.sound). Details:
`docs/logs/integration-v3-20261012d.md` and the lane logs `v3-link-2026-10.md`,
`v3-render-sched-2026-10.md` (packages 11–13), `v3-render-vbytes-2026-10.md`,
`v3-render-chacha-2026-10.md`.

* `nearAirV3`: table 20 = `SrcpDD` (DedupTable + A10 depth bits); table 9 carries the A9 word
  counter; A7 tables nodeA7/valA7/upsA7/sizeA7 (RPL 70, RPLV 71); rcpt q<128 check.
  Size bound **6,435,489 B** at g=2 (`v3MaxInner`), `v3MaxHintBytes` 1,953,115 (4+hint+inner =
  8 MiB exactly); honest hints ≤ 1,295,025 B.
* **Public format change (2026-10-12):** prepared source rows are 34 bytes `[dup, rep] ++ root`;
  dup byte 0 first occurrence, 1 consistent repeat, 2 inconsistent repeat (AIR rejects 2).
  `PreparedByteLength = 340 + 34·|lists| + …`. `prepD0` unchanged.
* Spec (unsigned draft): A7 = unfolded pre trie + native post trie ≤ B0; A11 retired; A12
  `|boundaries|+1 = |shardIds|`.

**Rust prover (2026-10-13, main `c6330302`): first real proofs, accepted by Lean.**
`examples/np-udr-stark-v2`: `npudr v3prove <case> <out>` builds all 25 `nearAirV3` tables natively
from claim + witness (`v3prepare` hint/prep/public tape, `v3trie` 2–7/21/A7, `v3rcptfam` 16–20/23/24,
`v3sched` 8–15/22, SHA collector 0/1), checks constraints + all 51 buses + public messages, and
proves at g=2. `np-lean-verify-v3` (deployed `npVerifierP challengeSpecD0a nearAirV3 split prepV3b`)
accepts proofs of 00-h10004-s3, 00-h10035-s3, 01-h10009-s1 (5.26–5.67 MB, ~12 min on 8 cores,
≤13.3 GB RSS) and rejects 14/14 mutations each. `--check-only`: all buses balance on all 81 fixtures
(64 public-d0a + 17 `conformance/fixtures-extra`, repeated source keys / empty values).
`formal/NpUdrStarkV2.certificate` = `nearV3_admission_final` (unconditional; maxRecDepth 20000).
Every Rust generator/preprocessor is differential-tested against Lean (`conformance/run-v2.sh`,
sections in `run-v2.d/`; `PROVE_V3=1` adds the real proof). Logs: `docs/logs/v3-prover-*.md`.

**Open:**
* **Elaboration budget** (below) — the main feasibility question; not measured yet.
* **Packaging:** `build-recipe/build.sh`'s `out/prove`/`out/prepare` are still the v1 binaries; wire
  them to `v3prepare`/`v3prove`; vendor; judge-style build. Check ~12 min prove time against the
  judge's prove budget.
* ~~Oracle~~ (lane oracle-d0a, 2026-10-13): `oracle/v3-d0a` implements A7 native post trie, A12,
  empty-key-extension fix, offline `unfold-case`; public-d0a regenerated (all `.bin` byte-identical,
  only meta.json); difftests 0 disagreements on public-d0a, fixtures-extra, full/heavy scratch corpora,
  d1run, d2corpus (`docs/logs/oracle-d0a-2026-10.md`). **Empty main pre-state is outside RelD0**
  (user decision 2026-10-13): Lean/Python/oracle reject it; mutant `public-d0a/mutants/
  00-h10004-s3-w.empty_pre_state` (re-add after any regeneration; command in its meta); spec v0a §1.
* ~~Fixture coverage~~ (lane v3-prover-cover): `fixtures-extra/d0` has 39 accepted cases incl. 9 ChaCha
  (1–597 words, block boundaries) and 13 upsert-path cases (all 11 terminal cases / 12 part kinds);
  real proof of x-bw-implicit accepted by Lean (`docs/logs/v3-prover-cover-2026-10.md`).
* **Rechecked (lane v3-prover-digest):** the schedqv bus-1 DIGEST imbalance was `npudr v3bus` evaluating
  with zero publics (mrk root row reads the outcome root from `p146..177`); `v3prove` was right. `v3bus`
  fixed; `run-v2.d/digest.sh` checks BYTES/DIGEST on all 81 (`docs/logs/v3-prover-digest-2026-10.md`).
* **Argued, not proved (prover-side only):** receipts read the pre-scheduler trie (scheduler writes only
  key `[0,15]`); native execution skips grant distribution and the refund-forwarding limit check.
* Cleanup: `ChachaWords.lean` duplicates `A9Words.coreMid`/`runMid_st`; 2 `clippy -D warnings` errors
  (`protocol.rs`, `chacha.rs`); Lean `rankWalks` and Rust `ups::uu` are quadratic.
* Conformance: full `run-v2.sh` on `c6330302` 2,126 PASS; its 92 FAILs were stale/missing Lean exes
  (fixed in `run-v2.sh`, `7bc2086e`); reruns schedqv 143 PASS, prove 18 PASS (real proof accepted).

**Judge budgets (user decision 2026-10-13: 4 h elaboration).** The formal checker enforces
`Limits::default` (`runners/formal-checker/src/pipeline.rs`, since `a0990606`): 1 h per module, 4 h
total elaboration, 2 h per recheck run, 4 h per rechecker; the older 1,800 s figure is superseded
(DESIGN.md F6). Measured (judge-style clean serial `lean -o`, warm trusted oleans): the unconditional
`nearV3_admission_final` closure was 4,514 modules before pruning, projected ≈ 5,000–6,000 s (first 1,523 modules
took 1,800 s); slowest: `Candidates.HorizontalAuxCheck` 140 s, `Candidates.VerticalPriorFusion` 124 s,
`Render.Ups.GWalk` 86 s, `Render.Node.Links` 80 s, `Assembly.NearAirCheck` 68 s; 49 modules ≥ 10 s ≈
1,650 s. The conditional 748-module certificate (589 s) does NOT prove admission — never use it.
* **Pruning (done, `ea459caa`):** closure 4,514 → **3,964 modules**; full single-core serial
  `lean -o` (conservative; Lean's parallel elaboration is faster) 10,242 s → **8,734 s**. Import
  redirection + `*Core` splits of 16 modules; no code deleted; constant-type fingerprints
  unchanged (`zk-formal/scripts/TypeHashes.lean`); tools `ClosureDeps.lean`, `judge-time.py`;
  log `docs/logs/v3-prune-2026-10.md`. Packaged closure re-vendored (3,960 modules; `sync-lean.sh`
  layout bug fixed). Remaining hot spots: `CodecEndInt` 1,695 s, `CodecRecInt` 1,255 s,
  `CodecHeader` 335 s (≈ 38% of the closure; `simp` inside `codec_int`), `GWalk` 192 s,
  `Node.Links` 182 s. Proposed next levers (not applied): faster `codec_int`, per-case codec
  modules, a g = 2-only `NearAirCheck` lemma.
* **Not measured yet:** leanchecker / nanoda / lean4lean rechecks of the 3,964-module closure.
* **Prover resource limits miss:** draft `max_prove_ms` 600,000 and 16 GiB RAM / 8 vCPU; real proofs
  take 710–749 s and 13.3 GB RSS (15.5 GB internal peak).

**Quality notes for whoever continues:**
* Converge on `ExtractV3Stmt` / `CompleteV3Stmt`; every new module should sit on one of them.
* `nearAirV3` is no longer frozen, but each lane edits only its own tables' entries in
  `Assembly/NearAir.lean`; the lead recomputes the combined size bound at merge (`#eval
  sizeMaxAligned nearAirV3.toAir (pg 2)`), since lanes' bounds don't merge textually.
* Keep the guarded axiom audits.

## 6. Verification status of this merge

* **2026-10-12 (`integration/v3-20261012d`, main `abf81215`):** `lake build
  ZkFormal.V3.Integration` passes (4,692 jobs); 2,787 dependents of the 140 changed modules
  rebuild (153 top-level modules, 5,357 jobs, 0 errors); 15 guarded audits incl.
  `AuditAdmissionV3` pass; `make pin-check` OK; no sorry/axiom/native_decide/implemented_by.
  Difftest not re-run.
* **2026-10-11 (`integration/v3-20261011b`):** from clean caches (see §7), `lake build
  ZkFormal.V3.Integration nearspec-v3-check-d0a` passes (2,753 jobs); all 3,333 modules
  depending on the merged changes rebuild (`lake build` of their 185 top-level modules: 5,128
  jobs, 0 errors); the 14 new or changed audits and `AuditNearV3Admission` pass; `make pin-check` OK;
  D0a difftest on the public fixtures (300 cases): 0 disagreements.
* Earlier builds reported by lanes before the cache repair may have run against stale
  artifacts; the numbers above supersede them.
* **Not re-run:** the ~2,400 older audit files, the D3 reference check-local, the full difftest
  corpora (only public-d0a and the A11 measurement on d1run/d2corpus).

## 7. Process rules learned (2026-10-07 to 2026-10-11)

* **Never hard-link (`cp -al`) a `.lake` between worktrees.** Lake rewrites `.trace` files in
  place, so a build in one worktree marks modules up to date in all others while their `.olean`
  stays stale (false build results). On 2026-10-11 every mismatched trace was deleted and all
  small cache files de-linked. Copy with `cp -a` (or rebuild) instead.

* **Push every checkpoint to origin.** If the sandbox has no network, say so in the final report. Do not leave work only in bundles or as untracked files in the main checkout.
* **One worktree per agent.** Never work in `/data/illia/nearproof` itself; integrate on an `integration/*` branch.
* **Progress notes go to `docs/logs/`, not this file.** Don't make commits that only touch the log on main.
* **Never overwrite another lane's module.** Rename instead; this already caused one collision, which was caught and restored.

## 8. Smaller follow-ups

* **Succinct badge:** 2 MiB / 50 ms, log-log growth test. Not implemented.
* **Mainnet replay:** real class weights and a measured `G_α`.
* **Independence of the clean-room Python VM:** it was tuned against nearcore black-box runs.
* **Future challenges:**
  * 1 Pgas as a single STARK, which needs Goldilocks, a distributed prover and precompiles;
  * a cross-shard whole-block proof (`BENCHMARK_SPEC.md` §14.11).
* **Disk:** `/` about **98%** (20 GB free), `/data` about 90% (2026-10-11). Remove merged worktrees and their build dirs once they are clean and pushed. There are about 110 worktrees under `/data/illia/nearproof-wt`; most belong to merged lanes. The untracked drafts left in the `v3-air` and `v3-assembly` worktrees are superseded by main.

## 9. Key documents

| Topic | Documents |
|---|---|
| Architecture and contracts | `ARCHITECTURE.md`, `CONTRACTS.md`, `CHANGELOG-contracts.md` |
| Security model | `TCB.md`, `THREAT_MODEL.md`, `SECURITY_POLICY.md` |
| Benchmarking and operation | `BENCHMARK_SPEC.md`, `LIVE.md` |
| v3 domain specs | `spec/near-chunk-validation-{d0,v0a,d1,d2,d3}.md` |
| Requirements | `docs/requirements/` |
| ZK formalisation | `docs/zk-formal/` (DESIGN, V3-D0-DESIGN, STATUS-*) |
| Lane status files | `STATUS-V3-AIR.md`, `STATUS-V3-D3.md` |
| Raw log | `docs/logs/v3-progress-log-2026-10.md` |
