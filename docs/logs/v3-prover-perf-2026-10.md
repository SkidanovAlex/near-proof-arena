# lane/v3-prover-perf — `npudr v3prove` within the judge limits (2026-10-13)

Goal: `npudr v3prove` on 8 vCPU within `max_prove_ms` 600,000 and 16 GiB RAM with margin
(target ≤ 500 s wall, ≤ 14 GiB peak RSS). The judge times the whole `prove` entry point
(request + witness → claim + proof; `runners/worker/src/stages/common.rs` `prove_spec`,
`limits.max_prove_ms`); `prepare` (params → public) has its own 600 s budget. So the whole
`v3prove` wall counts (entries, rendering, constraint/bus checks, STARK, Rust re-verify).

Proof format, AIR, verifier and Lean are untouched: every change below must yield byte-identical
proofs (checked with `cmp` against the baseline proof on every run).

## Setup

* CPUs 8-11,24-27 (4 cores × 2 HT = 8 vCPU), `HEAVY_MEM=16G taskset -c 8-11,24-27 heavy
  /usr/bin/time -v npudr v3prove <case> <out> --air conformance/out-v2/nearAirV3.json --pub
  public.bin`. Foreign load on these CPUs is sampled every minute during each run (per-thread
  CPU time of non-npudr threads on CPUs 8-11,24-27 over 3 s); runs with foreign load > 0.5 CPU are
  discarded and repeated.
* Lean verifier: `np-lean-verify-v3` from the `v3-integ-d` worktree (same commit `c6247f3d` as
  this branch's base; the verifier is frozen).

## Finding: this host builds a scalar (non-AVX2) prover

`~/.cargo/config.toml` sets `[target.x86_64-unknown-linux-gnu] rustflags = ["-C",
"link-arg=-fuse-ld=mold"]`. In cargo, `target.<triple>.rustflags` takes precedence over
`build.rustflags`, so both the crate's `.cargo/config.toml` (`target-cpu=x86-64-v3`, `+sha,+aes`)
and `build-recipe/build.sh`'s `CARGO_BUILD_RUSTFLAGS` are ignored on this host: `npudr` had
125 ymm instructions (Plonky3's packed BabyBear is compile-time selected → scalar
`WIDTH = 1`). All earlier timings (710–749 s, 1,092 s) were of that scalar build. The judge
builds with build.sh's flags in its own environment, where they apply (unless its cargo home has
a target rustflags entry). Here, all builds use `RUSTFLAGS="-C target-cpu=x86-64-v3 -C
target-feature=+sha,+aes"` (RUSTFLAGS beats every config source; 42,774 ymm instructions).
**For the build-recipe lane:** a host-local cargo config can silently drop the codegen flags;
consider `RUSTFLAGS`/`CARGO_ENCODED_RUSTFLAGS` (and check `objdump | grep -c ymm`) in build.sh.

## Baseline (main `c6247f3d`), x-bw-implicit (slowest fixture)

| build | wall | prove | RSS | CPU% | main commit | aux | quotient | quot commit | ood | deep | fri | openings |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| scalar (host default) | 1,014 s | 997 s | 11.9 GB | 630% | 252 | 133 | 277 | 101 | 27 | 40 | 1.7 | 165 |
| AVX2 (judge flags) | 717 s¹ | 578 s | 11.9 GB | 435% | 164 | 100 | 158 | 73 | 11 | 21 | 1.3 | 49 |

¹ ~120 s of unexplained idle time before the STARK in that run (not seen again; the check-only
prefix takes 18 s), so the honest AVX2 baseline is ≈ 600 s wall.

Profile notes (AVX2): 193 M minor page faults (≈ 790 GB of fresh pages: every block buffer was a
fresh mmap at `M_MMAP_THRESHOLD = 1 MB`), only 435% CPU of 8 (serial copies such as `fold`'s
`f.clone()` of 512 MB per LDE block), `eval_range` (fold + Plonky3 coset DFT with two
bit-reversal passes) dominating every phase, the main commit recomputing each column chunk's
iDFT once per level-0 group (4 groups), and quotient loads on sub-block ranges (each folds all
coefficients) because the 11 GB default budget did not allow whole blocks.

## Changes

1. **`lde::CosetDft`** — cache-blocked coset DFT, natural-order coefficients → bit-reversed
   evaluations with no permutation pass (DIF: first `log R` layers on gathered residue batches
   in L2 scratch with the coset powers folded into the gather, last `log S` layers in place on
   contiguous blocks). 2^22 × 32 block: 0.106 s vs 0.281 s (`eval_range`) / 0.193 s (Plonky3 on
   a reused buffer) (`examples/ldebench.rs`). Bit-identical (test vs `eval_range`).
2. **Block-wise level 0 of the commitments** (`lmcommit::hash_level0_blocks`): column chunks are
   planned across the class-0 matrices so every feed ends on a 64-byte boundary of the leaf
   message (first chunk 52 + 64k bytes after the 12-byte WH prefix), so each leaf keeps only its
   two SHA-256 states (64 B, finished in place into the digest) — half the old per-leaf state;
   coefficients once per chunk per group, one `CosetDft` per LDE block. The main commit now runs as
   one group (2^26 positions, 4 GB of states) instead of 4. Tested against `mmcs::commit` (roots and
   openings) on tables crossing the chunk boundaries.
3. **Quotient loads**: whole LDE blocks through `CosetDft` (`Coefs::eval_into`), one half buffer
   for whole blocks, whole blocks chosen whenever they fit.
4. Default `NPUDR_MEM_GB` 11 → 13 (judge cap 16 GiB; peak RSS measured below).

| step | wall | prove | RSS | main commit | aux | quotient | quot commit | openings |
|---|---|---|---|---|---|---|---|---|
| 1+2 | 489 s | 471 s | 11.9 GB | 84 | 81 | 158 | 65 | 49 |
| 1–4 | 411 s | 393 s | 11.8 GB | 86 | 62 | 116 | 47 | 49 |
