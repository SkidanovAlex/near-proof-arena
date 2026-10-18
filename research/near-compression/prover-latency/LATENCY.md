# PQ prover latency: 1 Pgas chunk → final proof, on H200 (U-8)

Lane `lane/pq-prover-latency`, 2026-10-18. Branched from `lane/pq-recursion-sha384` @ 46b7e62e2. Base and
aggregation numbers come from `lane/pq-base-aggregation` @ 6c97b4b28 (`DESIGN-BASE.md`).

Labels:
* **M**: measured on this host (Ryzen 9 9950X3D, 16 cores / 32 threads, Zen 5, AVX-512, no SHA-512
  instructions). Logs are in `logs/`.
* **C**: a cited public benchmark or vendor figure. Not reproduced here.
* **D**: derived by arithmetic from stated inputs.
* **A**: assumption.
* **[L]** and **[B]**: a measured-law or `bound.py` figure imported from DESIGN-BASE or `extrapolate_nv2.py`.

There is no GPU on this host. Every H200 number is a model figure.

Files:
* `latency_model.py`, output in `results/latency-model.txt`: every table below comes from it.
* `bench/latency_bench.rs`: microbenchmarks (SHA-512 compression, T\* grind, Ext12, NTT, ×15 commit).
* `bench/nv_layer.rs` with `run_nv_layer.sh`: one NV layer at the real protocol settings, with
  per-phase timing (tracing-forest).
* `run_bench.sh`: builds both against a private copy of the unified backend and openvm-sha384, rebuilt
  from this branch's patches, under `/data/illia/nearproof-deps/pq-latency`.

---

## 0. Answers in one page

**Settings.**
* 268-bit target with z = 32 (236 query bits), 42-B SHA-384 digests, T\*, WHIR-Y, tight heights.
* The NV inner shape is c = 15, b = 6, n_stack = 17. The final layer has c = 15 and its own b.
* The pipeline is DESIGN-BASE design **G**: one shared-transcript base proof over all GPUs (P-PERF-4),
  then L1 → T1 → T2 → FINAL.
* With these settings the final proof is **≈ 325 KB**. No lever point in the model reaches 300 KB at 268
  bits (§5).

**The critical path after execution ends.** In order: base phase B, then L1, T1, T2 and FINAL. These are
four strictly sequential single proofs.
* Each recursive layer is dominated by **zerocheck + LogUp-GKR of the degree-21 SHA AIR in Ext12**, not
  by hashing or NTT. Measured on CPU, zerocheck + GKR is **94 % of an NV layer's prove time**.
* The next-largest items are:
  * the 2³² grinds, 4–5 per layer at z = 32;
  * the final layer's commit (LDE 0.29 TB at b = 6, 1.1 TB at b = 8; it must be streamed).
* The base matters only for adversarial chunks.
* The recursion tail does not depend on the workload. At 32 H200 it costs **≈ 2.6 s in the mid case and
  ≈ 0.8 s in the optimistic case**.

**End to end, after execution ends.** Seconds; optimistic / **mid** / pessimistic. Recommended settings:
z = 24 on base and inner layers, z = 32 and b = 6 on the final layer. Final proof 324,927 B.

| chunk class | 8 H200 | 16 H200 | 32 H200 |
|---|---|---|---|
| typical (4.1·10⁷ ops) | 2.7 / **8.3** / 42 | 1.5 / **5.1** / 29 | 0.83 / **2.7** / 15 |
| mainnet-like (3.6·10⁸ ops) | 2.7 / **8.9** / 44 | 1.5 / **5.1** / 30 | 0.83 / **2.7** / 15 |
| adversarial (1.22·10⁹ ops) | 8.9 / **20.9** / 68 | 4.3 / **12.3** / 46 | 1.6 / **5.7** / 23 |

How to read the columns:
* **Optimistic**: GPU zerocheck at 1.5× the bottom-up operation count, top-quartile kernels, base at 60 %
  of peak.
* **Mid**: zerocheck 4× bottom-up, base at 35 % (PERF's and DESIGN-BASE's assumption).
* **Pessimistic**: GPU code as inefficient as today's CPU port (12× bottom-up), base at 20 %.

**H200s needed for real time at 1 Pgas** (real time meaning ≤ 1–2 s after execution, comparable to
block time):
* **mid case: not reachable at any N.**
  * The four-layer recursion tail is ≈ 2.6 s even at 32 GPUs per proof (§4.4).
  * The model does not shard one recursive proof beyond 32 GPUs.
  * So ≤ 3 s takes 32 H200 for typical and mainnet-like chunks, and 96 for adversarial.
* **Optimistic case:**
  * typical and mainnet-like: ≤ 1 s on 32 H200, ≤ 2 s on 16;
  * adversarial: ≤ 2 s on **32 H200**, ≤ 1 s on 48.
* So "a few H200 machines" (16–32 GPUs) is enough **only if** two things hold:
  1. the Ext12 zerocheck / GKR kernels for the NV circuit get within ≈ 1.5–2× of the bottom-up count;
  2. the base sustains ≈ 60 % of peak.

  The biggest single lever is to cut the SHA AIR's (d + 1) × DAG cost (§5.5).

**Measured constants (M)** that calibrate the model (§2):

| quantity | value |
|---|---|
| SHA-512 compression (sha2 0.10.9), 1 thread | 3.44 M/s (291 ns); OpenSSL: 6.0 M/s |
| SHA-512 compression, 32 threads | 45.1 M/s |
| T\* grind attempt (honest `pow_step`), 32 threads | 34.3 M/s, so **2³² takes 125 s on average** |
| T\* grind attempt, 8 threads | 13.3 M/s, **322 s** on average (§2.1) |
| Ext12 mul (p3 generic), 1 thread / 32 threads | 388 ns / 36.9 M/s |
| Ext12 × base mul | 13 ns |
| BabyBear NTT as the backend runs it (per column), 32 threads, 2²⁴ × 16 columns | 13.6 ns/point |
| ×15 commit (RS + SHA-384 Merkle, 42 B, coset leaves), 32 threads, 10⁹ LDE cells | RS 22–36 ns/cell; Merkle 3.8–4.1 ns/cell (1.0 ns/byte) |
| NV layer (NvAir 2¹⁸ + SHA 2¹⁶ rows, 236 query bits, ×15, all levers), 32 threads | 1,200 s, peak 9.9 GB; zerocheck + GKR 1,124 s (94 %); commit 9.7 s |

**The size–latency frontier** (§5) is flat around 325 KB:
* final b = 3 → 8 moves FINAL from 0.51 to 0.86 s (mid, 32 GPUs) and the size from 351 KB to 322–324 KB;
* across 313–354 KB the whole tail moves by ≤ 0.26 s at 32 GPUs;
* final z = 0 → 32 costs +0.12 s (mid, 32 GPUs; +0.48 s at 8 GPUs) and saves 29 KB;
* z = 36 costs +1.8 s for −3 KB;
* dropping one recursion level saves 0.4 s for +1.7 KB.

Nothing at the 268-bit target reaches 300 KB. A 258-bit final target gives 313–316 KB.

**Biggest risks:**
1. The GPU efficiency of the Ext12 degree-21 zerocheck: this alone is the 3× spread between optimistic
   and mid.
2. A single proof sharded across 16–32 GPUs: distributed sumcheck/GKR, distributed WHIR codewords.
3. Grinding variance: p99 = 2.5× the mean for a layer's 4 grinds.
4. Streaming a 0.3–1.1 TB final LDE plus 97-GB Ext12 round codewords.
5. Base cost on SWIRL/Ext12 (DESIGN-BASE R1).

---

## 1. Pipeline and what is on the critical path

```
t=0 ── native execution + checkpoints (1.2 s / Pgas, outside the target: P-PERF-6) ──┐
       └─ segment tracing on host cores → GPU main-trace LDE + leaf digests (streams)  │
                                                         last main root ───────────────┴─►
base phase B (all GPUs, one transcript): GKR LogUp + zerocheck (distributed sumcheck) → stacking → WHIR
  (5 query phases, grind 2^z_base each)
L1   NV verifying the base proof            (2^28.0–28.7 NV cells, c = 1, b = 3, m = 8)      all GPUs
T1   NV verifying L1, app-table binding     (≈ 2^27.1,  c = 15, b = 6, n_stack = 17)         all GPUs
T2   NV verifying T1, own-program binding   (≈ 2^26.2 = the fixed point)                     all GPUs
FINAL NV verifying T2, the transmitted proof (2^26.1, c = 15, b_final, z = 32)               all GPUs
```

* **Strictly sequential.** Each level's verifier program, and so its trace, needs the child proof.
  Phase B needs the last main root, because the LogUp challenges are global.
* **Parallel within a level.**
  * Commit splits by coset: 15 cosets × sub-cosets, each GPU building subtrees.
  * Sumcheck and GKR split by rows. Each round all-reduces (d + 1) Ext12 values: ≈ 300–600 rounds
    per layer, a few µs each on NVLink, ≈ 10–30 µs on InfiniBand.
  * Grinding splits by nonce range and is embarrassingly parallel.
* **Pipelining across levels** is limited to small overlaps: the host trace generation of the next level
  runs while the current proof's WHIR openings are serialised.
* **Design G vs tree designs.** DESIGN-BASE's T8 tree needs ≈ 20 N1×8 nodes of 2^30.9 NV cells each. At
  the measured NV cost per cell (§4.3), T8 takes **≈ 87 s** after execution on 32 H200. Design G is the
  only DESIGN-BASE design compatible with real time.
  * DESIGN-BASE assumed 4–30 cell-eq per NV cell. This lane gets **≈ 400–1,250 (mid) and 140–660
    (optimistic)** (§4.3).

## 2. Measured constants (CPU, this host)

### 2.1 Hashing and grinding (`logs/micro-sha-grind-ext.log`)

**SHA-512 compression** with the `sha2` crate 0.10.9 (the crate the backend uses):

| threads | rate | per thread |
|---:|---:|---:|
| 1 | 3.44 M/s (291 ns) | 3.44 M/s |
| 8 | 17.1 M/s | 2.14 M/s |
| 16 | 29.4 M/s | 1.84 M/s |
| 32 (SMT) | 45.1 M/s | 1.41 M/s |

* Multi-block (64 blocks per call), 1 thread: 3.90 M/s (500 MB/s).
* `openssl speed sha512` (8 KiB): 769 MB/s = **6.0 M compressions/s per core**. So the Rust crate is 1.7×
  slower than OpenSSL.
* PERF's 9.9 M/s per core is not reproduced on this Zen 5, which has no SHA-512 instructions.

**T\* grind.** One attempt is one compression of a 105-byte PoW block, through the hasher API.

| threads | attempts/s | mean time for 2³² attempts |
|---:|---:|---:|
| 1 | 1.9–2.1 M/s | — |
| 8 | 13.3 M/s | **322 s** |
| 32 | 34.3 M/s | **125 s** |

The grind is exponentially distributed:
* P(T < 0.2·mean) = 18 %. The quoted 65.5 s at 8 threads (pq-native-hermetic log) was one draw.
* For a layer's 4 grinds, p99 / mean = 2.51 (Gamma(4)).
* Over the 22 grinds of a full chain at z = 32, p99 / mean = 1.56.

### 2.2 Field arithmetic

**Ext12** = p3 `BinomialExtensionField<BabyBear, 12>`, generic schoolbook:
* mul throughput **388 ns** (2.58 M/s); dependent-chain latency 356–513 ns;
* Ext12 × base: 13 ns;
* 32 threads: 36.9 M/s;
* BabyBear scalar mul: 570–640 M/s (1.6–1.75 ns).

So an Ext12 mul costs ≈ 220 base muls on this code path, against 144 products in the schoolbook. An
optimised CPU Ext12 (delayed reduction, AVX-512 lanes) would be ≈ 5–10× faster. **This is why the CPU NV
prover is slow.** It is not a property of the protocol.

### 2.3 NTT (`logs/micro-ntt.log`)

This is `odd_domain::rs_encode`, which is what `rs_code_matrix_odd` calls per column: a fresh
`Radix2DitParallel` (twiddles recomputed) for each column.

| size | 1 thread | 32 threads |
|---|---|---|
| 2²⁰, 1 column | 92 ns/point | 153 ns/point |
| 2²⁰, 16 columns | 45 ns/point | 85 ns/point |
| 2²², 16 columns | 68 ns/point | 22 ns/point |
| 2²⁴, 16 columns | 92 ns/point | **13.6 ns/point (74 M points/s)** |
| ×15 domain, 15 × 2²⁰ | 49 ns/point | 60 ns/point |
| Ext12 2²⁰ | 3.4 µs/point | 0.81 µs/point |

This path is far from an efficient CPU NTT. A batched AVX-512 NTT runs at ≈ 1–3 ns/point/core. These
numbers calibrate the CPU port only. The GPU model uses roofline and cited figures instead (§3).

### 2.4 Commit: RS encode plus SHA-384 Merkle, 42-B digests (`logs/micro-commit.log`)

`stacked_commit_odd`, 32 threads unless stated:

| shape | LDE cells | RS encode | Merkle | whole commit |
|---|---:|---:|---:|---:|
| W 32, 2¹⁸ rows, b 3, k₁ 1, ×15, coset leaf | 1.0·10⁹ | 22–32 ns/cell | **4.1 ns/cell (1.03 ns/byte)** | 20.3 ns/cell |
| same, k 3 | 1.0·10⁹ | 36 | 3.8 | 41.9 |
| same, 48 B, row leaves | 1.0·10⁹ | 22 | 5.0 | 40.0 |
| W 32, 2²¹ rows, b 3, c = 1 | 5.4·10⁸ | 23 | 4.8 | 49.2 |
| W 16, 2¹⁶ rows, b 3, ×15, **1 thread** | 1.3·10⁸ | 54 | 72 (18 ns/byte) | 123 |

* Single-threaded, the Merkle path spends ≈ 2.3 µs per 128-byte block, against 0.29 µs for a raw
  compression. The rest is per-leaf allocation: `Vec<Vec<F>>` rows, `felt_bytes`, framing.
* The first-call RS figure includes page faults.

### 2.5 One NV layer at the real settings (`logs/nv-layer-s16.log`, `logs/nv-layer-s17.log`)

**Settings** (`run_nv_layer.sh`):
* 268 / z = 32, run as 236 query bits without grinding (the grind is measured separately);
* 42 B, coset leaf, T\*, ×15, k₁ = 1, k = 4, m = 3, multiproof, keep-domain, Gruen GKR and zerocheck,
  derived claims, next mask, WHIR-Y, tight heights, wide PoW;
* n_stack = 18, b = 1. b = 1 so that it fits in ≤ 16 GB. The final layer's b = 6–8 is modelled.

The traces are padded to fixed heights (`NV_FIXED`): NvAir 2¹⁸ × 73, SHA AIR 2¹⁶ × 171 (s16) or 2¹⁷
(s17), byte table 2¹⁶.

| phase (32 threads) | s16 (2^24.87 cells) | s17 (2^25.32 cells) |
|---|---:|---:|
| main commit (`stacked_commit_odd`, ×15, b = 1) | 9.7 s | 8.6 s |
| `prove_zerocheck_and_logup` | **1,124 s (93.7 %)** | **1,754 s (96.8 %)** |
| └ of which zerocheck MLE rounds | 917 s | 1,534 s |
| └ of which fractional sumcheck (GKR) | 89 s | 72.5 s |
| stacked opening reduction | 2.9 s | 2.5 s |
| WHIR + rest (self time) | ≈ 63 s | ≈ 47 s |
| total wall time (keygen + tracegen + prove + verify) | 1,200 s, peak RSS 9.9 GB | 1,812 s, peak RSS 10.0 GB |

**Conversion.** Zerocheck + GKR on CPU equals 1,124 s × 36.9 M Ext12 mul/s = 4.15·10¹⁰ Ext12-mul
equivalents. That is **12.0×** the bottom-up count of §4.2 (3.44·10⁹). s17 gives 1,754 s × 36.9 M/s = 6.47·10¹⁰
against a bottom-up 5.40·10⁹, i.e. **12.0×** again.

**Per-AIR split** (s17 − s16): one extra 2¹⁶ SHA rows cost +630 s.
* SHA AIR: 9.6 ms per row (CPU, 32 threads).
* NvAir: 1.9 ms per row.
* Measured ratio 5.1. The bottom-up count predicts 5.3 (29.9k against 5.6k Ext12-mul equivalents per
  row).

So the bottom-up law has the right shape, and only its constant (12× on this CPU code) is calibrated.

For comparison, the earlier chain logs:
* T = 20, 8 threads: A2 (2^25.9) took 2,130 s;
* T = 268, b = 1: A1 took 1,048 s, of which ≈ 4 × 65–322 s is z = 32 grinding.

The same zerocheck dominance holds in both.

## 3. H200 constants

| quantity | low / mid / high | basis |
|---|---|---|
| SHA-512 compressions, grind | 3.5 / **4.5** / 5.4 G/s | **C**: hashcat v6.2.6 mode 1700 (SHA2-512) on H100 80GB HBM3 SXM, 5,408.6 MH/s per GPU, 43.2 GH/s for 8 ([gist](https://gist.github.com/laluka/2ee80e40ad485adc26934109f4ab75ef)). See the notes below. |
| SHA-512 compressions, Merkle leaves and nodes | 2.7 / **3.5** / 4.6 G/s | A: operands from HBM, digest writes, framing |
| BabyBear LDE points / s | 3 / **6** / 12 ·10¹⁰ | D roofline: 4.8 TB/s, 3 passes × 8 B ⇒ 2·10¹¹; 16.7 T int32 IMAD/s ÷ ~130 ops/point ⇒ 1.3·10¹¹. Sustained share A. |
| Ext12 mul / s | 0.8 / **1.5** / 2.5 ·10¹⁰ | D: 144 MACs (IMAD.WIDE) + 12 Montgomery reductions + W-fold ≈ 400 int ops ⇒ 4.2·10¹⁰ at peak (132 SM × 64 int32/clk × 1.98 GHz). Sustained 20–60 % A. |
| one proof over N GPUs: efficiency | intra-node 0.75 / 0.85 / 0.92; 4 nodes 0.55 / 0.70 / 0.85 | A |
| per-layer serial overhead | 0.12 / 0.06 / 0.03 s | A: ≈ 300–600 sumcheck/GKR rounds × (transcript + all-reduce), launches |
| memory / link | 141 GB HBM3e, 4.8 TB/s, NVLink 900 GB/s, PCIe 5 128 GB/s | C: [H200 datasheet](https://openzeka.com/en/wp-content/uploads/2024/12/h200-gpu-datasheet.pdf) |

Notes on the SHA-512 rates:
* H200 is the same GH100 die, with the same SMs and clocks as H100 SXM; only HBM differs. So
  compressions/s carry over (D).
* Other cards for reference:
  * H100 PCIe: 4,054 MH/s ([gist](https://gist.github.com/Chick3nman/e1417339accfbb0b040bcd0a0a9c6d54));
  * A100 SXM4: 3,147 MH/s ([gist](https://gist.github.com/Chick3nman/d65bcd5c137626c0fcb05078bba9ca89));
  * RTX 5090: ≈ 9,985 MH/s ([forum](https://hashcat.net/forum/post-62344.html)).
* SHA-512 on NVIDIA GPUs is 64-bit-op heavy:
  * every 64-bit add is two 32-bit adds with carry;
  * every rotate is two funnel shifts (SHF);
  * so one compression is ≈ 2,700–3,000 int32 instructions.
* That is why the per-GPU rate is ≈ 3× lower than SHA-256 (16.2 GH/s in the same gist).
* A grind attempt is one compression of a fixed, mostly constant block, which is hashcat's case.
  Hashcat's early-exit and precomputation tricks are worth ≈ 10 %, hence a mid of 4.5 G/s: **2³² takes
  0.95 s on one H200**.

## 4. Per-stage latency and memory model

### 4.1 Hash work per layer

D, from `commit_work()`. Each leaf is ⌈(2^k₁·W·4 + 58)/128⌉ compressions, plus one node per leaf. Rounds
≥ 1 commit Ext12 codewords on the same domain (keep-domain), in 2^k-value leaves.

| layer (adversarial, design G) | shape | LDE | commit compressions | grind compressions (z = 32 / 24) |
|---|---|---:|---:|---:|
| base | b = 1, m = 16, W ≤ 24 per 2²⁴ slice (DESIGN-BASE) | 2× main | (in the base cell-eq) | 5 × 2³² / 5 × 2²⁴ |
| L1 | c = 1, b = 3, log_h 22, W 107 | 0.014 TB | 2.2·10⁸ | 5 × 2³² / 5 × 2²⁴ |
| T1 | c = 15, b = 6, log_h 19, W 282 | 0.59 TB | 5.8·10⁹ | 4 × 2³² / 4 × 2²⁴ |
| T2 | c = 15, b = 6, log_h 19, W 148 | 0.31 TB | 3.8·10⁹ | 4 × 2³² / 4 × 2²⁴ |
| FINAL | c = 15, b = 6, log_h 21, W 36 | 0.29 TB | 6.5·10⁹ | 4 × 2³² |
| FINAL at b = 8 | log_h 19, W 141 | 1.14 TB | 1.5·10¹⁰ | 4 × 2³² |

* At 3.5 G/s, the Merkle work of a ×15 layer is 1.1–1.9 GPU-s.
* At z = 32, the grinds of a layer are 3.8–4.8 GPU-s. **Grinding costs as much as all of a layer's
  Merkle hashing.**
* At z = 24 it is 0.02 GPU-s.

### 4.2 Field work per layer: NTT and zerocheck

**NTT.** Base-equivalent points = c·2^(log_h+b)·W, plus 12 × the domain for each Ext12 round.
* Final at b = 6: 1.5·10¹¹ points, i.e. 2.4 GPU-s.
* Keep-domain makes each of the 3 Ext12 rounds as large as the base LDE of one 12-column polynomial on
  the full domain. That is about half of the final layer's NTT. Without keep-domain the rounds would
  shrink 2× each: ≈ −1 GPU-s, at a proof-size cost that `ext.py` does not model.

**Zerocheck + LogUp-GKR, bottom-up count (D).**
* Round 0 uses the univariate skip in the base field, l_skip = 2.
* After that, each AIR's DAG is evaluated in Ext12 at (d + 1) points over N/4 rows in total.
* A DAG node is ≈ 0.42 Ext12-mul equivalents (A).
* The DAG node counts are measured by NV itself (`NV_DAG`): NvAir 3,637, SHA AIR 12,718.
* GKR is ≈ 40 Ext12 muls per fraction (A).

That gives:

| layer | padded rows (NvAir / SHA) | bottom-up Ext12 muls | GPU-s at 1.5·10¹⁰/s × 4 (mid) / × 1.5 (optimistic) |
|---|---|---:|---:|
| L1 (2^28.7) | 2²¹ / 2²¹ | 7.5·10¹⁰ | 19.9 / 4.5 |
| T1 (2^27.1) | 2²⁰ / 2²⁰ | 3.7·10¹⁰ | 9.9 / 2.2 |
| T2, FINAL (2^26.2) | 2¹⁹ / 2¹⁹ | 1.9·10¹⁰ | 5.0 / 1.1 |

* The SHA AIR is ≈ 80 % of this, through its factor (d + 1) = 22 × 12,718 nodes.
* The CPU calibration (12× bottom-up) is the pessimistic case. A GPU port that is "as wasteful as the CPU
  code" would make every layer 3× slower than the mid case.
* Padding to powers of two doubles L1's cost: 1.8M rows are padded to 2²¹. A zerocheck over tight heights
  would recover ≈ 1/3 of it.

### 4.3 Per-layer GPU-seconds on one H200

Adversarial, design G, mid case. The last column is in DESIGN-BASE's unit: work cell-eq per NV cell at
7.1 G/s.

| layer | NTT | SHA | ZC + GKR | grind (z = 32) | GPU-s | cell-eq / NV cell |
|---|---:|---:|---:|---:|---:|---:|
| L1 | 0.09 | 0.06 | 19.9 | 4.8 | 24.8 | 396 |
| T1 | 2.67 | 1.65 | 9.95 | 3.8 | 18.1 | 871 |
| T2 | 1.54 | 1.01 | 4.97 | 3.8 | 11.3 | 1,043 |
| FINAL (b = 6) | 2.42 | 1.73 | 4.97 | 3.8 | 12.9 | 1,247 |

* The optimistic case gives 8.5 / 8.0 / 5.8 / 6.8 GPU-s, i.e. 136–658 cell-eq per NV cell.
* **DESIGN-BASE's A-4 (4–30) is 1–2 orders of magnitude too low.** The three contributors:
  1. the ×15 · 2⁶ = 960× LDE of the inner shape;
  2. the degree-21 Ext12 zerocheck;
  3. the 2³² grinds.

### 4.4 Memory and streaming

| layer | trace (coefficients) | LDE if materialised | Merkle digests (42 B, 2× leaves) | Ext12 round codeword |
|---|---:|---:|---:|---:|
| L1 | 1.8 GB | 14 GB | 1.4 GB | 1.6 GB |
| T1 | 0.6 GB | 590 GB | 21 GB | 24 GB |
| T2 | 0.3 GB | 310 GB | 21 GB | 24 GB |
| FINAL b = 6 | 0.3 GB | 290 GB | 2.8 GB | 97 GB |
| FINAL b = 8 | 0.3 GB | 1,135 GB | 84 GB | 97 GB |

* **The LDE is never materialised.** Each GPU keeps the coefficients (≤ 2 GB) and produces its share of
  the c·2^s sub-coset chunks.
* Each chunk goes from NTT to the fused leaf hash to digests. Only the digests are kept: 1/N of the tree,
  ≤ 3 GB per GPU at N = 32.
* The 2^k₁·W opened values per query are re-derived by direct evaluation:
  * q₀·2^k₁ points × W columns, ≈ 10⁶ mult-adds, which is free;
  * or by re-encoding only the queried chunks.
* Ext12 round codewords go through the same treatment, so per-GPU memory stays ≤ ≈ 10 GB.
* HBM traffic for the final at b = 6 is 0.29 TB of NTT output written once and read once by the hasher,
  if not fused. That is ≈ 0.12 s at 4.8 TB/s, spread over 32 GPUs: about 4 ms.
* Interconnect traffic per layer is small:
  * sumcheck messages, roots and PoW nonces are KBs;
  * the WHIR round codewords need no all-to-all. The folded round polynomial has only
    2^(log_h − k₁ − k(i−1)) Ext12 coefficients, ≤ 2²⁰ × 48 B = 48 MB. It is all-gathered, and each GPU
    evaluates and hashes its own cosets.
  * A naive distributed NTT of the 97-GB final codeword would instead cost ≈ 0.1 s per round across
    4 nodes.

## 5. Levers: proof size against latency (adversarial, mid, design G)

### 5.1 Final-layer blowup b

FINAL only, 268 / z = 32.

| b_final | final proof | LDE | FINAL GPU-s (NTT + SHA) | FINAL at 8 / 32 H200 |
|---:|---:|---:|---:|---:|
| 3 | 350,605 B | 0.04 TB | 11.2 (2.4) | 1.62 / 0.51 s |
| 4 | 338,883 B | 0.07 TB | 11.4 (2.6) | 1.65 / 0.52 s |
| 5 | 330,609 B | 0.15 TB | 11.9 (3.1) | 1.73 / 0.54 s |
| **6** | **324,927 B** | 0.29 TB | 12.9 (4.1) | 1.88 / 0.59 s |
| 7 | 322,147 B | 0.57 TB | 15.0 (6.2) | 2.18 / 0.68 s |
| 8 | 323,877 B | 1.14 TB | 19.0 (10.2) | 2.77 / 0.86 s |
| 9 | 345,887 B | 2.26 TB | 24.4 (16.6) | 3.58 / 1.11 s |

* The size minimum is **b = 7, at 322.1 KB**, not b = 8: the stacking term 48·W grows with W.
* b = 6 costs +2.8 KB against b = 7, and halves the LDE.
* b = 8, the recursion lane's current final shape, is dominated by both b = 6 and b = 7.

### 5.2 Final-layer grinding z

b = 6, 268 − z query bits.

| z | final proof | grind GPU-s (mean) | FINAL at 8 / 32 H200 |
|---:|---:|---:|---:|
| 0 | 354,093 B | 0 | 1.40 / 0.47 s |
| 16 | 338,673 B | ≈ 0 | 1.40 / 0.47 s |
| 24 | 332,583 B | 0.01 | 1.40 / 0.47 s |
| 28 | 327,951 B | 0.24 | 1.43 / 0.47 s |
| **32** | **324,927 B** | 3.8 | 1.88 / 0.59 s |
| 36 | 321,753 B | 61 | 9.04 / 2.38 s |

* Each bit above 28 doubles the grind for ≈ 0.75 KB.
* z = 32 costs 0.12 s at 32 GPUs and 0.48 s at 8 GPUs, with a p99 of 2.5× that.
* z = 36 is never worth it.

### 5.3 Inner and base grinding

Final at z = 32.

| z_inner = z_base | tail at 8 / 32 H200 | final proof |
|---:|---:|---:|
| 0 | 8.34 / 2.67 s | 327,471 B |
| 16 | 8.29 / 2.66 s | 326,623 B |
| **24** | **8.23 / 2.64 s** | **324,927 B** |
| 32 | 9.76 / 3.02 s | 324,927 B |

* Inner layers gain nothing in size from z > 24: the extra query bits only shrink the next verifier
  slightly.
* **Recommendation: z = 24 everywhere except the final layer.**
* For tree designs, z_base = 32 is prohibitive. Each of the 146 independent segment proofs grinds 5 × 2³²
  on its own GPU: **697 GPU-s, 7.4× the base proving work** of 94 GPU-s. That is 23.6 s of base latency on
  32 H200. At z_base = 24 it is 3 GPU-s.

### 5.4 Recursion depth

| chain | tail at 8 / 32 H200 | final proof |
|---|---:|---:|
| L1 → T1 → T2 → FINAL (DESIGN-BASE G) | 8.23 / 2.64 s | 324,927 B |
| L1 → T1 → FINAL (one level fewer) | 7.09 / 2.25 s | 326,623 B |

* One level fewer saves ≈ 0.4 s at 32 GPUs (1.1 s at 8) for +1.7 KB.
* It needs FINAL to bind T1's program, which is not at the fixed point. That is a binding-design
  question (final-soundness §7.1). It is a protocol change, so it is not adopted here.
* Deeper chains only add ≈ 0.4–0.7 s per level, and buy nothing once T2 is at the fixed point.

### 5.5 SHA AIR zerocheck cost

The cost driver here is (d + 1) × DAG nodes. Tail at 32 H200, mid (optimistic):

| SHA AIR | tail |
|---|---:|
| today: degree 21, 12,718 nodes | 2.64 s (0.80 s) |
| degree 9 (k = 2 digits), same DAG and rows | 1.84 s (0.65 s) |
| half the DAG nodes | 1.91 s (0.66 s) |

* This is the largest latency lever that does not touch the proof's security parameters.
* The S lane's air2 trades degree for columns. Columns cost final-proof bytes (96 B each, two Ext12
  openings), so the trade must be scored jointly. The degree-9 variant's row and column counts are not
  measured.

### 5.6 The frontier around 300 KB

Design G, adversarial, z_inner = z_base = 24. Tail = L1 + T1 + T2 + FINAL. Final proof sizes come from
the lane's measured laws.

| final target / z / b | final proof | tail at 32 H200, mid (optimistic) | tail at 8 H200, mid |
|---|---:|---:|---:|
| 268 / 32 / 7 | 322,563 B | 2.73 s (0.85) | 8.53 s |
| **268 / 32 / 6 (recommended)** | **324,927 B** | **2.64 s (0.80)** | **8.23 s** |
| 268 / 28 / 6 | 327,951 B | 2.53 s (0.71) | 7.78 s |
| 268 / 32 / 5 | 330,609 B | 2.59 s (0.78) | 8.08 s |
| 268 / 24 / 6 | 332,583 B | 2.52 s (0.70) | 7.75 s |
| 268 / 24 / 5 | 338,181 B | 2.47 s (0.68) | 7.60 s |
| 268 / 32 / 3 | 350,605 B | 2.56 s (0.76) | 7.97 s |
| 268 / 0 / 6 | 354,093 B | 2.52 s (0.70) | 7.75 s |
| 258 / 32 / 7 | 313,215 B | 2.73 s (0.85) | 8.53 s |
| 258 / 32 / 6 | 315,663 B | 2.64 s (0.80) | 8.23 s |
| 258 / 28 / 6 | 318,687 B | 2.53 s (0.71) | 7.78 s |

* **The frontier is flat in latency and steep in bytes.** From 313 to 354 KB the tail moves by
  ≤ 0.26 s (mid, 32 GPUs) or ≤ 0.9 s (8 GPUs). The tail is zerocheck-bound, and size levers act on the
  commit and the grind.
* The two size levers that cost latency are z ≥ 29 and b ≥ 7.
* **300 KB is not reached at 268 bits** with today's NV circuit. Getting there needs non-latency levers
  (pq-native-hermetic): weak-binding digests, fewer or slimmer columns, a smaller fixed point.
* For latency, the levers that matter are not size levers. They are the SHA AIR's (d + 1) × DAG (§5.5)
  and the GPU zerocheck efficiency.

## 6. GPU mapping

### 6.1 What exists

* **OpenVM stark-backend v2.0.1, `crates/cuda-backend`**: this is the pinned d667af5, "release: v2.0.1",
  in the tree this lane builds on. It is a CUDA prover for exactly this protocol family (SWIRL), about
  12.5k lines of CUDA. It contains:
  * NTT (sppark/"supra" derived), batched small NTT, MLE interpolation;
  * LogUp-GKR (`gkr.cu`, `gkr_input.cu`), zerocheck round 0 and MLE rounds (`zerocheck_round0.cu`,
    `batch_mle*.cu`);
  * stacked reduction, WHIR, sumcheck;
  * Merkle trees, sponge transcript and grinding, for **Poseidon2 over BabyBear and BN254 only**.

  It has these limits:
  * the extension field is hard-coded to degree 4 (`cuda-common/include/fpext.h`, `FpExt { Fp elems[4] }`);
  * one GPU per proof: no NCCL, no sharded proof;
  * it has a `GpuMerkleHash` trait (`hash_scheme.rs`) that a SHA-384 hasher can implement.

  OpenVM reports real-time Ethereum with it, at 100 bits, Poseidon2/Ext4, proof < 300 KB:
  * 16 × RTX 5090: average 3.9 s, p99 6.3 s;
  * 8 × RTX 5090: average 5.4 s
  ([OpenVM 2.0 production](https://blog.openvm.dev/2.0-production); 2.1 preview: 16 GPUs p99 3.7 s,
  [blog](https://blog.openvm.dev/2.1)).

  That is the existence proof that SWIRL recursion runs at second scale on GPUs, at roughly 9× cheaper
  extension arithmetic and a much lighter hash AIR than ours.
* **NVIDIA cuPQC SDK v0.6.0, cuPQC-Hash** ([features](https://docs.nvidia.com/cuda/cupqc/libraries/cupqc_hash/cupqc_hash_feature.html),
  [Merkle blog](https://nvidia.github.io/cuPQC/blogs/merkle/)):
  * device-side SHA2-224/256/384/512, SHA3, SHAKE, and Poseidon2 (BabyBear/KoalaBear);
  * Merkle trees with SHA2-256/512 (not 384) up to 2²⁴ leaves.

  It is usable as the compression core. Our framing, 42-B truncation, coset leaves and the ×15 tree join
  need custom kernels around it.
* **hashcat** SHA-512 kernels: the throughput reference, 5.4 GH/s on H100 SXM.
* **ICICLE v3** (Ingonyama): BabyBear NTT and Poseidon2 Merkle. Not needed given OpenVM's backend; no
  SHA-2 Merkle was found in its documented hash list.

### 6.2 What has to be written

Ordered by effect on latency:

1. **Ext12 on GPU.**
   * `FpExt12` with delayed reduction (144 64-bit MACs, 12 reductions) or Karatsuba.
   * Every EF kernel re-templated on the extension degree: zerocheck MLE rounds and round 0, GKR, sumcheck,
     WHIR fold, stacked reduction.
   * Register pressure triples (48 B per element), so occupancy tuning is needed.
   * This decides optimistic vs mid. Effort is the largest: every kernel.
2. **A compiled constraint evaluator for the degree-21 SHA AIR.**
   * 12.7k DAG nodes at 22 evaluation points: CSE and register allocation.
   * Today `dag_entry.cuh` interprets rules.
3. **SHA-384 kernels:**
   * leaf hashing for v6 framing, coset leaves (tag 6) and 42-B truncation, fused into the NTT epilogue;
   * node compression;
   * T\* PoW grind (tag 7, wide witness, B₁ word test), spread over all GPUs with nonce ranges;
   * the transcript stays on the host (≈ 2k compressions per layer).
4. **The ×15 odd-domain LDE:** 15 coset NTTs with shift ζ^a. Reuses the coset NTT, plus the tree join over
   the c blocks.
5. **The protocol levers in the GPU prover:**
   * k₁ per round;
   * keep-domain;
   * Gruen GKR and Gruen zerocheck, plus derived claims;
   * next-row masks;
   * tight heights;
   * WHIR-Y;
   * multiproof, which is encoding only.
6. **Streaming commits** for 0.3–1.1 TB codewords, with opened rows re-derived (§4.4).
7. **One proof over 8–32 GPUs** (NCCL):
   * row-sharded zerocheck and GKR with per-round all-reduce;
   * coset-sharded commits;
   * distributed Ext12 NTT for WHIR rounds;
   * a distributed base phase B (design G).

   Nothing like this exists in OpenVM, which scales by segments.
8. **NV trace generation** at ≤ 50 ms per level, on the host or on GPU. Its current speed is not measured
   here. Per level it executes the ≈ 174k-instruction verifier program and fills ≈ 300k SHA rows. It is on
   the critical path between levels.

### 6.3 H200 count for real time

See §0. With the mid assumptions the recursion tail alone is ≈ 2.6 s at 32 H200, and does not shrink
past 32 GPUs per proof. If items 1–2 reach the optimistic case:

| target after execution | typical / mainnet-like | adversarial |
|---|---|---|
| ≤ 3 s | 8 H200 | 24 H200 |
| ≤ 2 s | 16 H200 | **32 H200** |
| ≤ 1 s | 32 H200 | 48 H200 |

## 7. End to end, and the critical assumptions

From chunk execution end to final proof. Design G; z = 24 on base and inner layers; final z = 32, b = 6;
324,927 B. Seconds; optimistic / **mid** / pessimistic.

| N H200 | typical | mainnet-like | adversarial | mid breakdown, adversarial (base / L1 / T1 / T2 / FINAL) |
|---:|---|---|---|---|
| 8 | 2.7 / **8.3** / 42 | 2.7 / **8.9** / 44 | 8.9 / **20.9** / 68 | 12.66 / 3.01 / 2.17 / 1.17 / 1.88 |
| 16 | 1.5 / **5.1** / 29 | 1.5 / **5.1** / 30 | 4.3 / **12.3** / 46 | 7.24 / 1.85 / 1.34 / 0.74 / 1.11 |
| 32 | 0.83 / **2.7** / 15 | 0.83 / **2.7** / 15 | 1.6 / **5.7** / 23 | 3.05 / 0.96 / 0.70 / 0.40 / 0.59 |

* From the start of execution, add 1.2 s.
* The grinding tail on top of these means, if z = 32 everywhere: p99 = 1.56 × the mean over 22 grinds.
  The mean is 0.66 s at 32 GPUs and 2.6 s at 8.

**Critical assumptions, in order of effect:**
1. GPU zerocheck/GKR efficiency in Ext12: 1.5× / 4× / 12× the bottom-up count. **This is the whole spread.**
2. Base work 546 cell-eq per adversarial op at 7.1 G/s per H200 (DESIGN-BASE A-2/A-3), and execution
   overlap.
3. Efficiency of one proof sharded over 8 GPUs (0.85) and over 32 GPUs (0.70). These are unmeasured, and
   nothing like this exists in OpenVM.
4. The node-cell sizes (L1 2^28.0–28.7) and the fixed point 2^26.1 [L].
5. Grind rate 4.5 G/s per H200, from hashcat on H100. The exponential variance is modelled.
6. NTT at 6·10¹⁰ points/s and Merkle at 3.5 G compressions/s, streamed.

**What to measure first on an H200** (this sharpens PERF §9.3):
1. Port the OpenVM CUDA zerocheck to Ext12 and run the NV SHA AIR at 2¹⁹ rows. This collapses assumption 1.
2. A SHA-512 grind kernel and a fused coset-leaf hash kernel.
3. A two-GPU sharded sumcheck.
