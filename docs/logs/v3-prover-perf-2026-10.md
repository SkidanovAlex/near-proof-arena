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

| step | wall | prove | main commit | aux | quotient | quot commit | openings |
|---|---|---|---|---|---|---|---|
| 1+2 | 489 s | 471 s | 84 | 81 | 158 | 65 | 49 |
| 1–4 | 411 s | 393 s | 86 | 62 | 116 | 47 | 49 |

(Checkpoint 1, `a9a56455`.)

5. **Parallel serial sections**: Merkle node levels without matrices (`hash_ranges` mapped 2^25
   nodes serially), leaf-state init, DEEP's per-point `exp_u64` (2^26 exponentiations) and
   batch-inverse inputs, quotient selectors (`bitrev_coset`).
6. **`eval_range`** uses `CosetDft` for whole blocks and after the fold for sub-block ranges
   (≥ 2^10 points).
7. **Streaming whole-block quotient**: a table whose coefficients do not fit next to a whole LDE
   block (rcpt: 4.4 GB + 4.4 GB) is evaluated block by block from the compact trace (per column
   chunk: iDFT + coset DFT), instead of sub-block ranges (each a fold of all coefficients).
   `NPUDR_QSTREAM=1` forces it (test `lowmem_streaming_quotient_equals_reference`).
8. **`CosetDft::idft`** — the cache-blocked inverse (DIT mirror; bit-reversed input variant for
   the quotient interpolation, which skips a serial `reverse_slice_index_bits`): 0.133 s vs
   0.297 s (Plonky3) per 2^22 × 32.
9. **`bufpool`**: large buffers reused (fresh 512 MB mmaps were page-faulted and zeroed per call:
   193 M → 68 M minor faults), cleared at phase ends, capped at 1 GiB.
10. **`sha2x::compress_pair`**: SHA-NI compression of the same blocks into WH's two states with a
   shared message schedule and interleaved `sha256rnds2` chains (leaf and `WhStream` hashing).
   −20% leaf-hash time (hyperthreading already hid much of the latency).
11. Packed `dot_rows` / `combine_into` (OOD / DEEP), packed constraint pre-check (`BlockEval` on a
   fixed random combination; the exact per-constraint scan only if it is non-zero: rcpt 6.6 →
   1.2 s), packed `FastBus` (8 points at a time with `ExtensionPacking`).
12. **Opening fold** (`eval_ranges`): 8 coefficient chunks per step through
   `Algebra::mixed_dot_product::<8>` (delayed reduction): openings 46 → 29 s.
13. **In-place column ranges** (`CosetDft::eval_cols`): stored coefficients (quotient, cached aux)
   are not copied per segment.
14. **Memory**: FRI layers opened (and their 2+ GB of vectors dropped) before the trace openings;
   32-column chunks for the aux commit; block-wise group sized within 3/4 of the budget.
15. Bug fixed on the way (in checkpoint 1's block-wise commit): an uncached aux source split at a
   non-multiple of 8 columns (`AuxSrc::values` asserts 8-alignment; `lowmem_near` caught it; the
   real runs use the aux cache and never took that path).

| step | wall | prove | cgroup peak | main commit | aux | quotient | quot commit | ood | deep | openings |
|---|---|---|---|---|---|---|---|---|---|---|
| 5–9 | 324 s | 307 s | 13.7 GiB¹ | 68 | 46 | 86 | 34 | 11 | 14 | 46 |
| 5–10 | 323 s | 306 s | 13.4 GiB | 64 | 49 | 87 | 32 | 11 | 14 | 46 |
| 5–14 | 293 s | 285 s | 12.3 GiB | 65 | 48 | 87 | 33 | 9 | 13 | 29 |

¹ from the per-phase `VmHWM`. **`/usr/bin/time` under-reports the peak RSS of this prover**: it
wrote `5` to `/proc/self/clear_refs` after each phase to report per-phase peaks, which also resets
the high-water mark that `getrusage` (and so `time -v` and `prove.sh`'s `%M`) report at exit, so
those showed only the last phase's peak (11.9 GB for the baseline, whose true peak was ≈ 13.0 GB
by its per-phase reports — the "internal 15.5 GB" of the earlier log was at `NPUDR_MEM_GB=20`).
The judge reads cgroup `memory.peak` (`runners/sandbox`), and so do these runs now (scope of the
`heavy` wrapper, polled every 0.5 s). The reset is removed (`peak_rss_mb`, cumulative).

(Checkpoints 2 `a585ba93`, 3 `93da5cd7`.)

16. **AVX-512 row backend** for `CosetDft` / iDFT (runtime-detected, `NPUDR_NO_AVX512=1` disables;
   Montgomery multiply ported from Plonky3's AVX-512 packing; ops tested against `F`, transforms
   against the AVX2 backend and Plonky3): 0.106 → 0.084 s per 2^22 × 32 block (forward), 0.123 →
   0.103 s (inverse). End to end only −5 s on 00-h10035-s3 (312 vs 317 s): the build stays
   x86-64-v3 and the AVX2 path alone meets the target.
17. Packed aux group factors (`AuxSrc::rows`, 8 rows at a time; all 25 `nearAirV3` tables have
   single-bit multiplicities, so no chain columns): aux values 3.8 → 2.6 s per recomputation (×5).
18. Cumulative peak-RSS report (no `clear_refs` reset), clippy fix in `Schedule::new` (loop
   condition never mutated), `prove.sh` no longer forces `NPUDR_MEM_GB=20` (the prover's default
   13 GB budget is sized for the 16 GiB cap; 20 would oversize the block-wise groups).

(Checkpoint 4 `6f4ac21e`.)

## Results (final build, CPUs 8-11,24-27, `HEAVY_MEM=16G`, foreign load ≤ 0.62 CPU in every run)

Wall = `/usr/bin/time` elapsed of `npudr v3prove` (everything the judge's `prove` times); peak =
cgroup `memory.peak` of the run's scope (what the judge reads); all proofs byte-identical to the
baseline's.

| fixture | baseline AVX2 wall / prove / peak | after wall / prove / peak | speed-up |
|---|---|---|---|
| x-bw-implicit (fixtures-extra) | 717 s¹ / 578 s / ≈13.0 GB² | **274 s** / 266 s / 12,569 MiB | 2.6× (2.2× vs 600 s) |
| 00-h10004-s3 | 518 s / 502 s / 12,187 MiB | **263 s** / 255 s / 11,939 MiB | 2.0× |
| 00-h10035-s3 (heaviest: sha_r 2^19) | 592 s / 572 s / 13,362 MiB | **312 s** / 302 s / 12,917 MiB | 1.9× |
| 01-h10009-s1 | 525 s / 508 s / 12,721 MiB | **278 s** / 270 s / 12,273 MiB | 1.9× |
| 00-h10035-s3, AVX-512 off | | 317 s / 308 s / 12,918 MiB | |
| x-bw-implicit, scalar host build (main) | 1,014 s / 997 s / — | | |

¹ includes ≈120 s of unexplained idle at the start (see above). ² from the per-phase `VmHWM`
reports (cgroup peak not yet tracked in that run).

Phases (x-bw-implicit, after): entries/render/check/bus 8 s, main commit 62, aux 44, quotient 80,
quot commit 32, ood 8, deep 12, fri 1, openings 27 (s).

Fixture survey (`--check-only`, all 81): the class-0 (2^22) width is 588 in every fixture; the
heaviest shapes add `sha_r`/`walk`/`mrk` at 2^19 (00-h10035-s3, 00-h10036-s3: 673 × 2^22 cells
vs 588–607 elsewhere).

Final build (`cargo fmt` / clippy cleanup on top of checkpoint 4): x-bw-implicit 277 s wall,
269 s prove, 12,568 MiB cgroup peak, byte-identical.

## Verification

* `run-v2-section.sh prove` with `PROVE_V3=1`, `PROVE_CASES` = 00-h10004-s3, 00-h10035-s3,
  01-h10009-s1, x-bw-implicit (CPUs 8-11,24-27, `HEAVY_MEM=16G`, prover default budget): **ALL PASS**
  (72 checks): Lean `np-lean-bundle-v3` == Rust `npudr v3sched` entries, 25 tables / 51 buses,
  proofs ≤ 8 MiB, the deployed Lean `np-lean-verify-v3` ACCEPTS all four (2.6–3.0 s), 14/14
  negatives rejected per case. (Lean exes from the `v3-integ-d` worktree, same base commit
  `c6247f3d`, symlinked into the ignored `conformance/.lake`.)
* `cargo test --release` (all targets): all pass, incl. new tests — `lde` (coset DFT, iDFT,
  bit-reversed iDFT, column ranges, `eval_range` / `eval_ranges` vs full LDE, AVX-512 ops and
  transforms vs packed / Plonky3), `lmcommit::matches_mmcs_fast_level0` (block-wise level 0 vs
  `mmcs::commit`, roots and openings), `sha2x::pair_matches_sha2`,
  `lowmem_streaming_quotient_equals_reference`; `lowmem_equals_reference(_near)` compare the whole
  proof with `prover_ref` byte for byte. Also with `NPUDR_NO_AVX512=1`.
* `cargo fmt --check` OK; clippy: no errors (the two HANDOVER errors fixed: `protocol.rs` loop,
  `chacha.rs` test `2 * 0`); no new warnings in the new code; `make pin-check` OK; nothing under
  `challenges/`, `oracle/`, `spec/`, `zk-formal/`, `build-recipe/` or Lean touched; npudr CLI
  unchanged.

## Risks / headroom

* Timings are on 4 Zen 5 cores (9950X3D, ~5 GHz) with SMT; a cloud 8-vCPU box (4 cores, lower
  clocks, less memory bandwidth) will be slower — plausibly 1.3–1.6× (≈ 360–500 s for the heaviest
  fixture). The AVX2-only path costs +5 s.
* Memory: ≤ 12.6 GiB cgroup peak on all fixtures at the 13 GB default budget (judge cap 16 GiB).
  Peaks: main commit (4 GB of leaf states + traces) and FRI. If the judge falls back to
  `RLIMIT_AS`, virtual size counts: VmPeak was 13.3–13.7 GB.
* Shapes: every fixture has the same class-0 width (588); heavier witnesses (SHA tables beyond
  2^19, or more 2^22 tables) would scale time roughly with the committed cells (00-h10035-s3 has
  +12% cells over x-bw-implicit and +14% time).
* **Build flags**: the judge must build with `target-cpu=x86-64-v3` actually applied (see the
  finding above); a scalar build is ~1.6× slower (this branch's code paths are mostly packed).
* Remaining hot spots: coset DFTs ≈ 75 s total (main 32, aux 23, quot 16), leaf hashing ≈ 38 s
  (SHA-NI bound), quotient ≈ 80 s (rcpt streamed: iDFT per block; bus constraints 12 s), aux
  values recomputed 5× (2.6 s each), openings 27 s.
