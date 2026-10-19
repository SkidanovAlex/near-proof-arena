# Fast, low-memory CPU prover for the SWIRL stack (byte-identical proofs)

Lane `lane/pq-cpu-prover`, branched from `lane/pq-recursion-sha384` @ 717eb518e, with
`lane/pq-stream-commit` @ 26cdf5af7 merged (streamed commitments are the baseline). The
recursion head 71060036c is merged at the end and the overlays are ported to it (§7).

Only the prover changes. **Every proof is byte-identical to the original prover's**: same
transcript, same challenges, same bytes. §5 lists the evidence.

Labels: **M** measured on this host (AMD Ryzen 9 9950X3D, 16 cores / 32 threads, AVX-512, 125 GB),
which is shared with other lanes and often loaded 2× over; **CPU-s** = process CPU seconds
(`utime + stime`), the load-independent measure; wall times are given with the load they ran under.

---

## 0. Results in one page

**What was slow.** On the baseline, a real NV layer (NvAir 2^18 + SHA v4 2^20, n_stack 18, b = 1,
×15, every lever) took **9,521 s wall / 18,976 CPU-s at 8 threads, peak 18.2 GB** [M, loaded box].
The MLE rounds of the zerocheck were 8,329 s of it, and the LogUp GKR 220 s.
* Every Ext12 multiplication went through the generic schoolbook: 167–388 ns.
* The constraint DAG was re-evaluated per (y, x) point on scalar Ext12 values, with a node vector
  allocated each time.
* Every interaction was evaluated a second time as an expression tree, per point and per coset.
* The GKR kept a 2^(L+1)-entry segment tree plus a copy of the input plus per-layer column copies.

**The same layer now** [M]:

| | baseline | fast | ratio |
|---|---:|---:|---:|
| CPU seconds | 18,976 | **129** | **147×** |
| wall, 8 threads | 9,521 s (loaded) | **64.9 s** (shared box, ~2 cores effective) | 147× |
| peak RSS | 18.19 GB | **3.68 GB** (streamed commits) | **4.9×** |
| zerocheck MLE rounds | 8,329 s | 18.8 s | 443× |
| LogUp GKR | 220 s, 28 GB-class transient at 2^26 | 12.2 s, ≤ 3.6 GB (2.6 GB at cap 21) | 18× |
| proof SHA-256 | `ef3b730b…` | `ef3b730b…` | identical |

**Per stage** [M, 8 threads, CPU-s on the real layer unless noted]:

| stage | before | after |
|---|---:|---:|
| Ext12 × Ext12, scalar (1 thread) | 388 ns (generic build), 167 ns (native) | **22–24 ns** |
| Ext12 × Ext12, packed SoA (per element) | — | **7.8 ns** (6.9 ns fixed multiplier) |
| Ext12 × base | 11–13 ns | **1.3 ns** |
| SHA-384, 1 thread, 768-B leaves | 1.6–8 M compressions/s (`sha2`) | **24–30 M** (8-lane AVX-512) |
| T\* PoW grind, 1 thread | ~2 M candidates/s | **37 M/s** (2^32 ≈ 10 s at 32 threads) |
| in-memory commit (W 32, 2^16, b 3, ×15) | 13.98 ns/cell | **3.43 ns/cell** |
| streamed commit, W 82, n 20, b 1 | 15.8–17.4 ns/cell | **6.9 ns/cell** |
| streamed Ext12 WHIR round commit | 20–40 s (wall, 8 thr) | 1.3–1.9 s |
| q42 layer (NvAir 2^14, SHA 2^16) | 205 s wall, 18m CPU | **4.7 s**, 17 CPU-s |
| s48 layer (48-B digests) | 280 s wall, 27m CPU | **8–19 s** |

**Memory.** The GKR transient that set the final's peak (23–28 GB on a 10–16 GB base in the
stream lane's b = 2 final; 37–40 GB hwm in its d1 chain) is now ≤ 3.6 GB at 2^25 inputs with the
default cap and adjustable down to ~1.2 GB (§3.4). The zerocheck tables are stored at half size
(§3.3). Layer peak 18.2 → 3.7 GB (4.9×; 2.6 GB with `NEARPROOF_GKR_CAP_LOG=21`).

**L1 over the pinned base.** An L1-shaped layer (NvAir 2^21 + SHA 2^22, 510M cells) proves in
**152 s at 8 threads with a 10.1 GB peak** [M]. The e2e slice estimated 190–230 GB for the
unoptimised prover. L1 fits this machine with a wide margin (§6.3).

**Full chain.** See §6.4.

**What is left.** §8.

---

## 1. Layout and how to run

* `native/recursion/setup_cpu_fast_deps.sh`: the NV deps with the streamed-commit overlay
  (`setup_stream_deps.sh`), plus three overlay patches in the existing style:
  * `patches/stark-backend-cpu-fast.patch`: `cpu-backend/src/fast/*` (packed Ext12, MLE rounds,
    round 0, GKR), the integration in `cpu-backend/src/logup_zerocheck`, batched Merkle hashing,
    the streamed-commit and DFT changes in `stark-backend/src/prover/{stream_pcs,stacked_pcs,fast_dft}.rs`;
  * `patches/plonky3-ext12-simd.patch`: Ext12 under AVX2/AVX-512 builds (p3 had no SIMD path for
    degree 12 and panicked) and the one-dot-product Ext12 multiply;
  * `patches/openvm-recursion-cpu-fast.patch`: the 8/16-lane AVX-512 SHA-384 (`sha384/mb.rs`),
    used for grinding and for Merkle leaves and nodes.

  `make_cpu_fast_patches.sh` regenerates them; the setup script verifies that the live trees
  equal the patches. A fresh setup reproduces the trees exactly (checked with `diff -r`).
* Build with `RUSTFLAGS="-C target-cpu=native"` (AVX-512 packing). Without it everything still
  works with 1-lane "packing" and the scalar SHA.
* `NEARPROOF_CPU_FAST=0` selects the original code at run time (every fast path is gated), for
  A/B identity checks inside one binary. Finer switches: `NEARPROOF_CPU_DA=0` (no degree-aware MLE
  rounds), `NEARPROOF_CPU_PLE_DEFER=0` (store the skip-folded tables),
  `NEARPROOF_GKR_CAP_LOG=k` (GKR memory/time trade-off, default 24), `NEARPROOF_GKR_CHECK=1`
  (asserts the GKR claim-derived t(0) against the direct sum each round).
* `results/pq-cpu-prover/`:
  * `run_bench.sh <example>`: builds a bench example against the deps tree (8 threads, 24 GB,
    nice 10 by default);
  * `identity.sh <binary> <cfg>`: one NV layer at the real lever settings, prints the proof
    SHA-256; configs `q42`, `q48`, `s42`, `s48`, `real`, `l1`, `fx42`, `fx48`;
  * `bench/nv_layer.rs` (from the latency lane, + proof hash), `bench/ident_small.rs` (backend
    fixtures), `bench/ext12_bench.rs`, `bench/sha_bench.rs`, `bench/latency_bench.rs`
    (+ `stream` and `dft` modes);
  * `prof/`: the gdb poor-man's profiler used instead of perf (perf_event_paranoid = 4 here).
* `native/recursion/run_cpu_chain.sh`: the stream lane's real-settings chain with this prover.

## 2. Profile of the baseline

`perf` is not usable on this host, so `prof/pmp.sh` attaches gdb once a second and records every
thread's stack (`logs/profile-base-s42.txt`, s42-like layer, 8 threads, 2,761 busy thread-samples):

* **42 %** `eval_interactions`: the interaction expressions re-evaluated as trees
  (`SymbolicExpression::eval_expr`, recursion depth 20+) per point, in the MLE rounds, round 0
  and the GKR input;
* **14 %** `acc_constraints` → `eval_nodes` in the MLE rounds (the DAG on scalar Ext12, a fresh
  node vector per evaluation);
* **11 %** `overflowing_sub` and the rest of the innermost frames are Montgomery arithmetic inside
  the generic Ext12 schoolbook (`binomial_mul`, `monty_reduce`, `wrapping_mul`);
* **5 %** the GKR sumcheck (`sumcheck_round_poly_evals` over col-major copies).

Op mix: the SHA AIR v4 DAG has 5,848 nodes (2,034 Ext×Ext multiplications, 1,190 by constants,
2,411 linear, 269 output terms); NvAir 4,857 nodes (2,239 / 306 / 2,038 / 892). At 9 evaluation
points per pair, the SHA AIR needs ~20.7k Ext12 multiplications per 16 pairs; at 167–388 ns each
this is what took the time. 8-thread runs used only ~1.1 cores on average (`time -v`): the hot loops
allocated per evaluation and serialised on the allocator.

## 3. Changes

Each change computes the same field elements as the code it replaces; field arithmetic is exact,
so different evaluation orders and algorithms give the same values, and the transcript sees the
same sequence. Where an algebraic shortcut is used (Gruen factoring, finite differences, Lagrange
matrices, four-step DFT), it is an identity of polynomials that holds exactly.

### 3.1 Ext12 arithmetic

* **Packed SoA Ext12** (`fast/pext.rs`): `PE<P>` holds 16 Ext12 elements, coefficient-major, in
  `PackedBabyBearAVX512` lanes. `a·b` is 12 lazy-reduction dot products of length 12
  (`PrimeCharacteristicRing::dot_product`, u64 sums before one Montgomery reduction) over
  `[w·b_1..w·b_11, b_0..b_11]`; a fixed multiplier is precomputed (`PreMul`). 7.8 ns per element.
* **Scalar Ext12** (p3 overlay): the degree-12 `binomial_mul` is one AVX-512 dot product with the
  output coefficients in the lanes (167 → 22 ns); `Ext12 × base` is one vector multiply (1.3 ns).
  Degree-12 add/sub/base-mul under AVX builds no longer panic.
* Runtime detection (`detect_w`): the fast paths run only if `EF` is `F[X]/(X^12 − w)`, checked on
  sample products; otherwise the original code runs.

### 3.2 Zerocheck and LogUp MLE rounds

* **One compiled program per AIR** (`fast/zc.rs`): constraints and interaction messages/counts in
  one DAG pass, register-allocated slots with liveness, constants folded, multiplications by
  constants as Ext × base. The three outputs (Σ λ^i C_i, Σ eq3b_i count_i, Σ eq3b_i denom_i) are
  linear functionals of node values; their coefficients are precomputed and merged per node.
* **Lane-strided SoA tables**: lane l of block b holds row l·B + b, so row pairs (2y, 2y+1) are in
  blocks (2b', 2b'+1) of the same lane: the round evaluation and the fold are pure vector code and
  the fold keeps the layout.
* **Degree-aware evaluation**: each node is evaluated at x = 1..deg+1 only and extended to the
  round's points by finite differences (additions) when a consumer needs more; outputs are
  grouped by degree.
* **Round 0** (`fast/round0.rs`): lanes over hypercube points; the coset values come from one
  precomputed Lagrange matrix per coset (L_z(s·ω^z'), lazy 4-term dot products); one DAG pass gives
  the zerocheck and both LogUp functionals for all cosets.

### 3.3 Small-value round 1 (zerocheck tables at half size)

The first multilinear round reads the **base-field trace** and applies the univariate-skip fold on
the fly (4 Ext × base per input value); the first stored Ext12 table is folded by r_0 and r_1 in
one pass (8 Ext × base weights), so it has half the rows of the skip-folded table the original
stores. Real layer: the MLE-phase peak 4.26 → 3.27 GB. (The univariate skip with l_skip = 2 is
already the base-field round, and after it the trace values are Ext12, so the Bagad–Dao–Domb–Thaler
small-value expansion does not pay beyond this one round for degree-9 constraints: the round-2
expansion has C(9+3, 3) terms per product.)

### 3.4 LogUp GKR (`fast/gkr.rs`)

* **Input from the traces, in row-block order.** The input layer (numerators in the base field) is
  never stored. `InputSource::visit_runs` evaluates each block of trace rows once for all
  interactions (one pass over the trace) and hands the GKR runs of consecutive positions; sums are
  order-independent and folded entries are written by index.
* **Small-space layers.** Tree levels above 2^cap (`NEARPROOF_GKR_CAP_LOG`, default 24) are never
  stored: such a layer runs its first K sumcheck rounds as passes over regenerated runs (folded on
  the fly by the earlier challenges) and materialises its table only once it is ≤ 2^cap entries
  (the prefix–suffix / small-space idea of Nair–Thaler–Zhu, applied to the GKR layers).
* **Gruen eq split**: s(X) = A·eq(ξ_i, X)·t(X), with t of degree 2; per pair only t(1), t(2) are
  evaluated; t(0) comes from the round claim, t(3) by extrapolation; no eq column is interpolated
  or folded; sqrt-split eq tables. **Fused fold + next round**, one pass per round.
* Base-field numerators in the input layer (Ext × base products).

### 3.5 Hashing

* **8/16-lane AVX-512 SHA-384** (`sha384/mb.rs`, isa-l mb_sha512 design: one 64-bit word per
  message per zmm lane, `vprorq`, `vpternlogq` for Ch/Maj/σ). Two independent 8-lane groups are
  interleaved because the round is latency-bound. Plain SHA-384 (contract U-7), equal to `sha2` on
  every length 0..300 and the PoW, node and leaf sizes.
* **Grinding**: `grind_mb` searches the same candidates in the same order and returns the same
  smallest witness (tests against `pow_step` at 8–17 bits, narrow and wide, T\* on and off; PoW
  proofs identical).
* **Merkle**: `MerkleHasher::{hash_coset_batch, hash_leaves_flat, compress_pairs}` (default:
  one by one); leaves are gathered column by column from column-major codewords and hashed from
  one byte arena.

### 3.6 Commitments and DFTs

* **Streamed commitments** (`stream_pcs.rs`): sub-cosets of at least 2^16 points (a short Ext12
  polynomial on a 2^27-point domain was 983,040 tiny DFTs in the stream lane's chain); one
  sequential task per group of sub-cosets for small ones (the per-sub-coset parallel regions stall
  on a busy machine); query rows of a leaf from one coefficient pass per fold coset
  (f(x_0 ζ^t) = Σ_j ζ^{tj} x_0^j H_j(x_0^g)) instead of one Horner per row; segmented Horner for
  base columns.
* **Four-step coset DFT** (`fast_dft.rs`): row-SIMD radix-2 DIF on L2-sized blocks, bit reversal
  absorbed into the transposed store and the final scatter, several shifts per call for narrow
  matrices. Used by the streamed commitments and by `rs_code_matrix_odd` (which ran one fresh
  `Radix2DitParallel` per column and coset).

## 4. Profile after

`logs/real-fast-8t-*` and `logs/quiet-fast-8t-*`. On the real layer (streamed, 8 threads,
~129 CPU-s): MLE rounds 59 CPU-s, round 0 18, GKR 18, commit 9, WHIR 25 (Ext12 round commits,
query rebuilds, sumcheck), stacking 4. The remaining cost is spread out; §8 lists what is left.

## 5. Identity evidence

All runs print the SHA-256 of the encoded proof (`identity.sh`, `ident_small`). "base" is the
frozen baseline binary built from the unmodified overlays (generic x86-64, as the other lanes
build it); "fast" is this lane's binary (`target-cpu=native`).

| fixture | digest mode | base | fast | |
|---|---|---|---|---|
| q42: NV layer, NvAir 2^14, SHA 2^16 (717eb518e) | 42 B + coset leaf | `1df5e391…` | `1df5e391…` | = |
| s42: NV layer, NvAir 2^16, SHA 2^16 | 42 B + coset leaf | `b8ad34ab…` | `b8ad34ab…` | = |
| s48: same, default digests | 48 B, row leaves | `0851b166…` | `0851b166…` | = |
| **real: NvAir 2^18 + SHA v4 2^20, n_stack 18** | 42 B + coset leaf | `ef3b730b…` | `ef3b730b…` (in-memory and streamed, every checkpoint) | = |
| L1-shaped: NvAir 2^21 + SHA 2^22 | 42 B + coset leaf | (not run: est. 100+ GB) | `7917543c…` (stable across GKR modes) | |
| backend fixtures (Mixture + Fib, log h 8/12/14) | 42 B and 48 B | FAST=0 | FAST=1, generic and native builds | = |
| PoW fixtures (query 18, logup 12, mu 10, fold 8 bits) | 42 B | FAST=0 | FAST=1 (8- and 16-lane grind) | = |
| `nv::stream_tests` b = 2 (streamed vs in-memory) | 42 B + coset leaf | — | 36/36 identical | = |
| recursion head 71060036c: q42 / s48 / real | 42 / 48 B | §7 | `565dc85a…` / `bc2f39bf…` / `97026bf4…` | §7 |

Unit tests: `sha384::mb` (SHA-384 vs `sha2` on lengths 0..300 and 104/105/109/768/1000/4096,
mixed lengths; hasher batches vs one-by-one in both digest modes; grind vs `pow_step`);
`NEARPROOF_GKR_CHECK=1` runs (claim-derived t(0) equals the direct sum in every GKR round, at caps
24/16/12/3); `latency_bench dft` (four-step DFT equal to p3's `Radix2Dit` and `Radix2DitParallel`);
`ext12_bench` (packed, premul and scalar products equal the schoolbook on 1,000 pairs).

## 6. Measurements

### 6.1 Arithmetic and hashing (1 thread unless noted) [M]

`bench/ext12_bench.rs`, `bench/sha_bench.rs`, `latency_bench dft|commit|stream`:

| | before | after |
|---|---:|---:|
| Ext12 mul, p3 `*` | 167 ns (native build), 388 ns (generic, LATENCY §2.2) | 22–24 ns |
| Ext12 mul, packed, per element | — | 7.8–8.3 ns |
| Ext12 mul, fixed multiplier, per element | — | 6.9 ns |
| Ext12 × base | 11.3 ns | 1.3 ns |
| SHA-384 1-block, compressions/s | 2.9–6.8 M (`sha2`) | 21–25 M (8 lanes) |
| SHA-384 768-B leaves, compressions/s | 1.6–8.3 M | 24–30 M |
| grind candidates/s | 0.9–2.1 M | 37 M |
| stream rebuild, 22,272 rows × 2^15 Ext12, 8 thr | 1.58 s | 0.25 s (packed Horner); per-coset rows: 9.4 → 0.75 s in situ |
| DFT 2^20 × 82, 8 thr | 0.42–0.54 s (Radix2DitParallel) | 0.32–0.34 s (four-step) |

### 6.2 Layers at 8 threads [M]

| layer | base wall | base CPU | base peak | fast wall | fast CPU | fast peak |
|---|---:|---:|---:|---:|---:|---:|
| q42 | 205 s | 1,098 s | 1.89 GB | 4.7 s | 17 s | 1.60 GB |
| s48 | 280 s | 1,608 s | 5.27 GB | 7.9–18.9 s | 35 s | 2.70 GB |
| real (in-memory commits) | 9,521 s (loaded) | 18,976 s | 18.19 GB | 70.0 s | 157 s | 7.55 GB |
| real (streamed commits) | — | — | — | 64.9 s | 125 s | 3.68 GB |
| L1-shaped (streamed) | — | — | (est. 190–230 GB) | 152 s | 761 s | 10.07 GB |

32-thread numbers: §6.4.

### 6.3 L1 over the real pinned base, re-estimated

The e2e slice (lane/pq-e2e-slice README §4) estimated 190–230 GB for L1 over the pinned base
(NvAir 2^21 × 74 + SHA 2^22 × 83 ≈ 503M cells), from 0.45 KB per cell measured on the r268 A2.
The L1-shaped layer here (NvAir 2^21 + SHA v4 2^22, 510M cells, the Fib child padded to these
heights; the prover's work and memory are functions of the heights) proves with a **10.07 GB peak
in 152 s at 8 threads** (20 B per cell). The peak is the zerocheck tables of the SHA trace after
round 1 (2^19 rows × 166 columns × 48 B); the GKR stays ≤ ~6.6 GB (2^28 LogUp inputs, cap 24).
With the real base proof as child the program is larger (623,802 rows), which changes the NvAir
fill but not the heights. **L1 fits this 125-GB machine** (and a 24-GB budget).

### 6.4 32 threads and the full chain

PENDING.

## 7. Merge of the recursion head (71060036c)

`lane/pq-recursion-sha384` 71060036c (G2 anchors, WIP; nv-preprocessed folded) is merged. Its
patches changed `stark-backend-unified.patch` (test utilities: cached traces committed with k1)
and `openvm-recursion-sha384.patch` (circuit, nv_chain). The stream lane's recursion overlay no
longer applied (nv_chain restructured); it is ported here (`openvm-recursion-stream.patch`: the
stream tests and the FINAL proof hash kept; the per-level save and regime prints dropped, the head
saves proofs itself). The cpu-fast patches only moved by offsets. A fresh `setup_cpu_fast_deps.sh`
on the merged branch verifies.

PENDING: base shas on the new head.

## 8. What is left

PENDING.
