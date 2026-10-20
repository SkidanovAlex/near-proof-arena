# V3-PERF-DESIGN: a performance-first architecture for PQ real-time proofs of NEAR chunks up to 1 Pgas

Status: **design, 2026-10-14**, lane `lane/v3-perf-design` (from main `ee1bbc71`). Commissioned by the user
("before doing any H200s, let's design this as performant as possible first"; "and test on CPU first on a few
instruction sets").

Scope: the PQ real-time track fixed by decisions U-1…U-9 (`V3-D3A-STUDY.md` §D):
* SHA-384 throughout (Merkle commitments, Fiat–Shamir, recursion circuits);
* failure ≤ 2⁻¹²⁸ against 2⁶⁴ quantum hash queries;
* **proven** soundness bounds only;
* recursion allowed;
* proof target 0.5–1 MB (300 KB stretch);
* prover hardware "a few H200 machines" (2–4 × 8 H200).

This lane changes nothing in `nearAirV3`, the D0a/D1 code paths, spec, challenges, `oracle/v3` or pinned
files. Every relation, spec, challenge, protocol or profile change below is a **PROPOSAL**.

Labels:
* **M**: measured in this lane (CPUs 9,25 under `nice -n 19`; contended, indicative only);
* **MR**: measured earlier in this repo (file cited);
* **C**: cited publication or vendor figure, not reproduced;
* **D**: derived by arithmetic from stated inputs;
* **A**: ASSUMPTION (each has a spike in §9).

Artifacts:
* `tools/perf-design/model.py`: the end-to-end model (§7). Every number in §7 comes from it.
* `tools/perf-design/wasmchip/`: spike #1, a CPU prototype of the hottest chips on the existing prover (§9.2).
* `docs/logs/v3-perf-design-2026-10.md`: the lane log.

---

## D. User decisions (2026-10-14, binding for this design)

| id | decision | consequence |
|---|---|---|
| **P-PERF-6** | Latency targets are measured **after execution ends** | The native run of the chunk (≈ 1–1.2 s per Pgas) is outside the target. The worst-case target is ≤ 2 s after execution on the P-PERF-7 hardware. |
| **P-PERF-7** | The worst-case 1 Pgas class targets **4 × 8 H200 (32 GPUs)** | All worst-case figures are given at 32 GPUs; 16-GPU figures are informational. |
| **P-RT-1'** | **No cap on distinct contract code bytes.** Keep the full domain; size the design and hardware for register copies and many distinct contracts | The worst case now includes ≈ 0.88 GB of distinct contract code per 1 Pgas chunk (§3.4) and register-heavy chunks (§3.2). There is no deploy-time PREP registry. |
| P-PERF-1…5 | Adopted as the **design baseline**: register-form translation, logUp buses, rate-1/2 inner layers with constraint degree ≤ 3, the shared distributed proof, stack-temporary channels | Each needs its soundness lemma. They are tracked in §8.1. |

---

## 0. Answers in one page (updated after the decisions, spikes 3–4 and the clean CPU runs)

**Verdict for the decided target.** The target is a worst-case 1 Pgas chunk, ≤ 2 s after execution ends, on 4 × 8
H200. Assuming the GPU kernels sustain ≈ 35 % of peak INT32 (**A**, `model.py`):

| 1 Pgas chunk (PQ, SHA-384, E = 10, proven-bound query counts, no code cap) | 32 H200: after execution / from start | 16 H200 (informational) |
|---|---|---|
| typical (measured synthetic mix: 3.4 % WASM gas) | 0.59 s / 1.79 s | 0.77 s |
| mainnet-like (**A**: 30 % WASM gas, memory-heavy mix) | 0.76 s / 1.96 s | 1.10 s |
| **adversarial WASM** (unaligned `i32.load` chain, worst *measured* operator, 281 work cell-eq per gas unit) | **1.75 s** / 2.95 s | 3.2 s |
| adversarial **contract loading** (≈ 0.88 GB of distinct code; SHA-256 **M** + PREP D; early PREP sub-proof) | 1.28 s / 2.48 s | 3.4 s |
| final proof | ≈ 0.84 MB (FRI, Johnson; final layer at rate 1/32) or 0.74 MB at 1/64 (+0.14 s) | |

The 32-GPU worst case meets ≤ 2 s after execution only if the GPUs sustain **≥ 30 % of peak INT32**
(≈ 7.1 G work-equivalent cells/s per GPU ≈ 25 M worst-case WASM operators/s per GPU). That is **plausible, not yet
measured** (spike H1). ≤ 1 s after execution would need ≈ 68 % of peak, which is not plausible on 32 GPUs.

**Three things dominate (sensitivity, `model.py`):**
1. GPU efficiency: 20–60 % of peak moves the worst case 3.03 → 1.10 s.
2. Contract-preparation (PREP) cost per code byte, which became a worst-case path under the no-code-cap decision.
   × 1–3 the estimate gives 1.75 → 2.89 s. PREP must stay ≤ ≈ 420 work cell-eq per code byte. It is **not yet
   prototyped** (spike P1).
3. Extension degree E: 8 → 12 gives 1.36 → 2.19 s.

**What changed since the first draft** (all in this lane):
* **Spike 4 measured the remaining hot chips.** These are v1 layouts on the existing prover, end to end, with honest
  proofs verified and code, initial memory and io bound to public inputs. Unaligned load/store, call/return, i64
  div, bulk copy, stack-temporary channels and single-lookup timestamps are all measured.
  * Measured mix: **9.4 main cells and 4.4 fractions per WASM op** (40 committed cells at E = 10).
  * Worst operator: 32/19 per op (281 work cell-eq per gas unit). §2.4 and §9.2b have the details.
* **Forged proofs are rejected by the deployed verifier.** A forging prover was built: an env-gated copy of the
  prover with the verifier byte-identical. Constraint, bus and public-claim forgeries, including OOD-consistent
  forgers and bus-balancing ones, were all rejected (§9.2b).
* **The in-circuit SHA-384 compression measures ≈ 38.9 k work cell-eq.** The draft assumed 20 k. The SHA-256 code
  hash measures 323 per byte.
  * The extra recursion cost was absorbed by raising L3's rate to 1/16, distributing L2/L3 over all GPUs, and
    running the final layer at rate 1/32 (§5.3).
* **No code cap (decision D).** Distinct-contract loading is the costliest operation per gas: 1.45× the worst
  operator. Every executed contract is known at chunk start, so PREP and the code hash become **early sub-proofs**
  overlapping execution (P-PERF-8, §3.4).
* **Register copies were re-costed.** `read_register` into memory pays `write_memory_byte` as well. Register bytes
  used as host inputs are consumed by reference, and the remaining no-fee path (`value_return`) is bounded by the
  witness (§3.2).
* **Clean CPU calibration** on 7 dedicated Zen 5 cores:
  * rate-1/2 LDE + SHA-384 Merkle: **22.9 ns per trace cell on one thread, 4.4 ns on 14 threads (227 M cells/s)**;
  * SHA-512 compression: 9.9 M/s per core;
  * whole prover at today's parameters: 18.7 M W_eq/s.

**Architecture (unchanged in shape; §1–§6).**
* Native execution with checkpoints, then parallel tracing; phase A streams during execution.
* Register-form WASM chips on shared buses (STATE, FETCH, MEM with timestamps and channels, RANGE/RANGE-T/PAIR).
* BabyBear with a degree-10 extension, committed logUp, rate 1/2 at the base with constraint degree ≤ 3.
* One shared-transcript proof across all GPUs, then L1/L2/L3 distributed and the final layer on one node.

**Decisions needed (§10):**
* P-PERF-8 (early PREP sub-proofs);
* the Johnson regime for L1–L3 (it is now on the latency path);
* the final-layer rate (size vs latency);
* the minimum E from research M3;
* an H200 for spike H1.

---

## 1. Execution and witness generation

### 1.1 The floor

* NEAR prices gas at ≈ 1 ps of reference execution, so 1 Pgas ≈ 1 s native (**A**, from NEAR's fee
  calibration: 1 Tgas ≈ 1 ms).
* Receipts in a chunk apply sequentially in nearcore, and a function call's WASM run is sequential. The native run
  is therefore a hard serial floor of ≈ 1 s per Pgas.
* The model adds 20 % for checkpoint recording (`exec_slowdown` 1.2, **A**).
* Sensitivity to it is nil *after* execution, but it adds one-for-one *from start*.
* No GPU count removes this floor. Every latency below is reported both *from execution start* and *after
  execution ends*.

### 1.2 Two-pass execution

**Pass 1: native run with checkpoints (serial, ≈ native speed).** The validator's ordinary execution engine (the
compiled WASM runtime) runs the chunk and records:

| record | when | size (D) |
|---|---|---|
| segment checkpoint: pc, frame stack (fp chain), operand stack, gas counters, globals, table | every `S_seg` ≈ 2²⁰–2²² WASM ops (an instrumented counter that the gas metering already maintains) | ≤ 1 KB plus the stack (≤ 256 KiB by `maxStackHeight`) |
| linear-memory pages touched since the last checkpoint (copy-on-write page snapshot, 64 KiB pages) | at a checkpoint | ≤ pages written × 64 KiB. A pure-store adversary writes ≤ 2²² × 8 B per segment, i.e. ≤ 512 pages |
| host-call results: register contents, storage read values, promise ids, `input` | per host call | the witness bytes (already bounded by the state-witness limit) |
| storage reads and writes (key, value, trie path) | per host call | as D0a/D1 (trie tables) |

The checkpoint cost is a page-table dirty-bit scan plus memcpy of dirty pages. At ≤ 512 pages per 4 M ops, that is
≤ 32 MB per segment, < 5 ms at memory bandwidth (**D**).

**Pass 2: parallel segment re-execution with tracing.**
* Each GPU node's host cores (2 × 64–96 cores per node) re-execute segments from checkpoints in a
  **register-form tracing interpreter**: the same translator as PREP (§2.2), emitting chip rows directly in the
  GPU's column layout.
* Segments are independent once their checkpoint exists, so ≈ 600 host cores across 4 nodes trace in parallel.
* At ≈ 20 M ops/s per core (**A**; spike #1 measures the register machine at the rate in §9.2), 1.22·10⁹ ops take
  ≈ 0.1 s of wall time when spread over the cores.
* Trace generation is therefore **not** on the critical path, except for the last segment (`seg_tail_s` 0.05 s,
  **A**).

**Parallelism across receipts and function calls.**
* Each function call is its own family of segments, and its machine state starts from the call's prepared state.
* Storage overlays between calls are bound by the trie buses (as D0a/D1), not by execution order.
* So receipts trace in parallel as soon as pass 1 has produced their inputs.
* This is the study's lever L3 and needs no relation change. The relation already folds segments
  (`Wasm/Segment.lean`: `run (Σks + n) s = foldSegments ks s >>= run n`).

**Overlap of proving with execution (streaming).**
* As soon as a segment's rows exist, its GPU computes the LDE and SHA-384 leaf digests of the main trace
  (**phase A**, ≈ 30–70 % of base work; `model.py` `t_A`).
* Phases that need global challenges (bus fractions, quotient, DEEP, FRI) wait until the last main root is in the
  transcript (**phase B**).
* Consequence: the post-execution latency is phase B + the compression tail, not the whole proof. Phase B is
  dominated by bus fractions. That is why §2/§4 minimise fractions.

**Bus challenges cannot be drawn per segment.**
* A logUp sum over segments must use one α drawn after *all* messages are committed. Drawing α per segment
  breaks the global multiset argument.
* This is the structural reason phase B exists. It is the same in the multilinear backend: the zerocheck and GKR
  run after the main commitment.

---

## 2. The WASM machine AIR, designed for minimum cells *and* fractions per instruction

### 2.1 Cost metric

* Each **chip row** has `m` main base cells and `f` bus fractions (logUp terms: sends, receives, lookups).
* Committed cells per row depend on the backend (§4).
* Prover **work** is the sum of:
  * ≈ 704 INT32 ops per committed cell at rate 1/2 (NTT 306, SHA-384 leaves 180, DEEP 120, constraint
    evaluation 98; **D**, `model.py int_ops_per_cell`);
  * ≈ 4.4 k ops per fraction for committed logUp (fingerprint, batched inverse, aux constraint) plus its E/2 = 5
    committed aux cells;
  * ≈ 13 k ops per fraction for GKR at E = 10 (28 extension multiplications per leaf over all layers, **D**).

"Work-equivalent cells" (cell-eq) = work / 704. The target the user set (≤ 100–150 cells per instruction) is met
by *committed* cells for every mix and backend except U-logUp in the adversarial case (168). In *work* the
adversarial case is ≈ 308 cell-eq/op. §2.6 explains why that is the honest number.

### 2.2 Register-form translation (PREP; PROPOSAL P-PERF-1)

WASM validation fixes the operand-stack height at every pc. So every stack slot is a static frame offset:

```
local i      ↦ frame slot fp + i            (i < nlocals)
stack slot h ↦ frame slot fp + nlocals + 1 + h
zero         ↦ frame slot fp + nlocals      (never written)
```

The translator walks each basic block with an abstract stack of *pending operands*
(`Local i | Const c | Temp h | Eqz h`). Rules, implemented and differential-tested in spike #1
(`wasmchip/src/wasm.rs`):

| WASM | register form | rows |
|---|---|---|
| `local.get i`, `i32/i64.const c` | push a pending operand | 0 |
| `local.set i` / `local.tee i` after a producing row | retarget that row's `dst := i` | 0 |
| `local.set i` otherwise | `mov`; pending `Local i` operands below the top are materialised first (WAR hazard) | 1 |
| binary ALU op | `dst = A op B` with A, B ∈ {slot, imm}; commutative constants go to the imm field | 1 |
| `i64.eqz; br_if L` | `brz A → L` | 1 |
| `br_if L` on a non-eqz value | `brnz A → L` | 1 |
| `br L` | folded into the preceding row's `next` field (code-table column) | 0 |
| `block`/`loop`/`end` | none (structured control resolved statically) | 0 |
| gas charge point (finite-wasm block-level) | `fee` field of the block's first row | 0 |
| `call f` | `call` row; the callee frame base = caller fp + caller stack height. Params already sit in the callee's first slots (overlapping frames), and results land in the caller's stack slots: **zero-copy** | 1 + 1 (`return`/`end`) |

* **Measured synthetic mix:** local.get/const/set/br/eqz are 56 % + 13 % + 6.9 % + 6.4 % of instructions and
  vanish. Rows per op = 0.29 (**D**). The spike measures 4 rows per 14-op iteration = 0.286 (**M**).
* **Mainnet-like (A):** ≈ 0.63 rows per op (memory ops and calls do not fuse).
* **Adversarial:** the adversary avoids fusion. A `local.get b; i64.div_u` pair is 1 row per 2 gas units; an
  `i32.load` pointer chase is 1 row per unit.

Soundness of the translation is a *static* property of the code. PREP proves "code table = translate(code)" once
per contract per chunk, in-AIR (or, PROPOSAL, once at deploy time with a cross-chunk code commitment; §3.3).
Lean proves `run_register (translate c) ≈ run_wasm c` as a simulation lemma per block (§8).

### 2.3 Chips and buses

**Buses:**
* `STATE (pc, ts, fp, u)`: each row receives and sends once;
* `FETCH (pc, cls, dst, a, b, imm₀..₃, fee, next, tgt, pol)`: the per-contract code table answers with a
  multiplicity column;
* `MEM (space, addr, v₀..v₃, t)`: offline memory checking;
* `RANGE16` / `RANGE-T` (2²⁴-entry timestamp-difference table) / `PAIR8` (byte pairs) / `BYTEOP` (8-bit and/or/xor);
* `CALL` (frame records);
* `HOST` (host-call dispatch to host chips, §3);
* the NEAR plumbing buses of `nearAirV3` (trie, receipts).

**Value representation.**
* BabyBear p ≈ 2³¹, so a u32 needs two 16-bit limbs and an i64 needs four.
* Multiplication uses **byte** limbs, because a 16×16-bit product exceeds p. That is why `mul` is the widest
  hot chip.
* Memory values are always 4-limb records (i32 slots have zero upper limbs as message constants). Only values
  *produced* by ALU rows are range-checked; reads inherit the invariant.

**State.**
* `pc`, `ts` (row clock), `fp` (frame base) and `u` (WASM gas in `regular_op_cost` units) are 4 cells. `fee` and
  `next` come from the fetch: 2 cells.
* Every non-bulk WASM operator costs a multiple of `regular_op_cost` (`FiniteWasm.lean`: regular, linear base =
  32 regular, linear unit = regular; prologue ⌈frame/8⌉ regular). So `u < 1.22·10⁹ < p`.

**Gas folded into fetch (lazy check).**
* Remaining WASM gas is monotone non-increasing within a call. So "no out-of-gas before the end" needs **one**
  comparison per call (at the return or trap row), not one per charge point.
* The out-of-gas trap row itself checks `remaining < fee`.
* Charge points cost 0 rows and 2 cells per row (`u`, `fee`).
* The `fee` column is the spec's own `gasTable` (`FiniteWasm.lean`), computed by PREP.

**Memory argument.**
* An access in row `ts` at sub-slot `k ∈ {0..3}` happens at time `4·ts + k`. It receives `(a, v_prev, t_prev)`,
  sends `(a, v, 4ts+k)`, and range-checks `4ts + k − t_prev − 1`.
* Time is local per GPU slice. Cross-slice records carry `(slice, t)` and compare lexicographically, with a flag
  selecting which difference to range-check. This is needed because 4 × 1.22·10⁹ > p.
* **Single lookup** per access into a 2²⁴-entry `RANGE-T` table (per GPU slice of ≤ 2²² rows).
* Boundary table: one row per touched address, sorted by key, with strict-increase range checks. Its `init`
  values come from the checkpoint (pages) or from the previous slice. Untouched pages of the 64 MiB initial
  memory cost nothing (lazy zero-init).
* Cost: **1 cell + 3 fractions per RW access**, plus 4 cells of previous value per write.

**Stack temporaries as channels (PROPOSAL P-PERF-5).**
* A temporary slot written by row p and read by row c (stack discipline: no other write between them) is a
  *channel*. The producer sends `(slot, v, t_p)` (1 fraction, 0 cells). The consumer receives it and
  range-checks `t_c − t_p` (2 fractions, 1 cell).
* There is no read-back and no previous value. Discarded values (`drop`, `br` unwinding) are consumed by an
  explicit kill in the row that discards them.
* Soundness sketch, to be proved:
  * Per slot, executed produce/consume events alternate in time, by WASM validation and induction over a
    correct prefix of the execution.
  * Given multiset equality and `t_p < t_c`, Hall's condition forces each consumer onto its own producer.
  * The first wrong match would leave an earlier consumer without a valid producer.
* Saving: 6 → 3 fractions and 9 → 1 cells per temporary.

**Instruction fetch.**
* The per-contract code table is a *preprocessed* commitment, fixed per (code hash, translation version).
* Each row pays 1 fraction. The table pays one multiplicity column.
* With P-PERF-1, PREP proves the table once per contract version, at deploy time (§3.3).

### 2.4 Per-class costs (v1 layouts; **M** = measured in spike 4, `wasmchip run1`)

m = main cells per row, f = bus-fraction slots per row. Committed and work figures are at E = 10 with committed
logUp (`model.py row_cost`). Operand forms: d/a/b ∈ L(ocal) / T(emp channel) / I(mm).

| chip (form) | m | f | committed U-logUp | U-GKR | ML | work cell-eq (U-logUp) | label |
|---|---:|---:|---:|---:|---:|---:|---|
| `alu_ri[LLI]` (i64 add/sub, local ← local op imm) | 33 | 13 | 133 | 53 | 33 | 214 | M |
| `alu_ri[LTI]` / `[TLI]` / `[L_I]` (li) | 33 | 12 | 123 | 53 | 33 | 198 | M: 33/12, 28/11, 32/10 |
| `alu_rr[LLL]` | 34 | 16 | 144 | 54 | 34 | 244 | M |
| `mul[TLL]` (byte limbs) | 44 | 30 | 224 | 64 | 44 | 412 | M |
| `divu[LLL]` (q·b + r = a, r < b) | 65 | 40 | 295 | 85 | 65 | 545 | M |
| `divu[TTL]` (adversarial chain form) | 60 | 37 | 280 | 80 | 60 | 512 | D from M |
| `brz[_L]` (eqz + br_if fused, local operand) | 21 | 6 | 81 | 41 | 21 | 119 | M |
| `ld_gen[TT]` (unaligned i32.load: two words + byte select) | 32 | 19 | 162 | 52 | 32 | 281 | M (`[TL]` 32/20, `[LT]` 37/21, `[LL]` 37/22) |
| `st_gen[_LL]` (unaligned i32.store: two RW words) | 37 | 24 | 187 | 57 | 37 | 337 | M (`[_LI]` 38/21) |
| `call` + `ret` (frame record in memory space 3) | 30 | 12 | 120 | 50 | 30 | 195 | M: 16/6 + 14/6 |
| `bulk16` (memory.copy / register↔memory, 16 B per row) | 39 | 27 | 209 | 59 | 39 | 378 | M (`bulk_start[_TLT]` 24/14 per copy) |
| `mbound` (per touched address; sorted, with `has_init`) | 16 | 5 | 76 | 36 | 16 | 107 | M |
| `bitwise` / `shift` / `clz` / `cmp` / `conv` / `global` / `select` | | | | | | | D (unchanged from the first draft: 36/16, 40/18, 30/12, 28/12, 18/8, 16/7, 26/10) |

Compared with the first draft's D estimates:
* `alu_ri` came in at 33/13 against 32/13;
* `mul` at 44/30 against 49/32;
* `ld_gen` at 32/19 against 37/19;
* `callret` at 30/12 against 35/20;
* `bulk16` at 39/27 against 60/24;
* `divu` at 60–65/37–40 against 75/45.

The v1 savings over spike #1's v0 layouts are measured on the same measured-mix program: 10.6 → 9.4 main cells and
5.1 → 4.4 fractions per WASM op. They come from channels, single-lookup timestamps, `brz` reading locals directly,
and register-form `li`.

### 2.5 Mix-weighted averages (per WASM op; `model.py`)

| mix | rows/op | main m | fractions f | committed: U-logUp / U-GKR / ML | work cell-eq (U-logUp / GKR / ML) | measured end to end |
|---|---:|---:|---:|---:|---:|---|
| measured synthetic | 0.31 | 9.7 | 4.6 | 42 / 16 / 10 | **71** / 101 / 96 | loop with the corpus mix: **9.4 main, 4.4 fractions, 40 committed** per op (M) |
| mainnet-like (**A**) | 0.63 | 20.0 | 10.0 | 90 / 33 / 20 | **153** / 217 / 207 | unaligned store/load mix: 11.0 main, 5.2 fractions, 50 committed per op (M) |
| adversarial WASM (unaligned load chain, 1 op/row) | 1.00 | 32 | 19 | 162 / 52 / 32 | **281** / 403 / 387 | 16-load chain program: 22.1 main, 12.6 fractions, 109 committed per op (M; loop overhead and boundary included) |

Adversarial candidates per gas unit (work cell-eq, U-logUp; `model.py`):

| candidate | cell-eq per gas unit |
|---|---:|
| unaligned `i32.load` chain | 281 |
| `local.get b; i64.div_u` chain | 256 |
| `i64.mul` chain | 203 |
| call of an empty function | 195 |
| `popcnt` (D) | 195 |
| memory.copy | 24 |
| `read_register` → memory | 7 |
| **distinct-contract loading** (SHA-256 **M** + PREP D) | **406**, proved during execution (§3.4) |

Gas prices WASM operators within ±20 % of this design's costs, so no single operator is a cliff.

### 2.6 Comparison with published zkVM per-cycle costs

| system | figure | kind |
|---|---|---|
| ZKsync Airbender | 21.8 M RISC-V cycles/s on one H100; SP1 Turbo 3.45 MHz; RISC Zero 1.1 MHz (same comparison) | **C** (Airbender page / blockeden summary; not reproduced) |
| implied Airbender work per cycle | at 16.7 T INT32/s and 30–40 % efficiency: ≈ 230–300 k INT32 ops per cycle ≈ 330–430 cell-eq per cycle (≈ 100-bit, conjectured, Blake2s, M31 with a degree-4 extension) | **D**, uncertain |
| wasmi interpreted in SP1 / RISC Zero | ≈ 29 / 25 RISC-V cycles per WASM op | **MR** (`checker-recommendations.md` §5) |
| WASM compiled to RISC-V | ≈ 1.5–3 cycles per WASM op | **A** |
| **this design** | 73 / 153 / 308 cell-eq per WASM op (typical / mainnet-like / adversarial) at PQ-128, SHA-384, E = 10 | **D** |

So a direct WASM AIR is ≈ 2–4× cheaper per WASM op than compiled RISC-V on an Airbender-class prover, and ≈ 30×
cheaper than an interpreter in a zkVM. The constraints are much heavier: PQ queries, E = 10, SHA-384. The
planning throughput 8.3 G cell-eq/s/GPU (35 % of peak) is consistent with Airbender's implied per-cycle work, but
it is **A** until an H200 measures it (§9.3).

---

## 3. Host functions and the NEAR runtime

### 3.1 Placement

| host family | chip | reuse |
|---|---|---|
| `storage_read/write/remove/has_key` | trie walk/update tables, `TrieAccounting` | nearAirV3 `node/head/val/walk/uniq/ups/sizeA7` on the trie buses (23 of 25 D0a tables verbatim) |
| `sha256`, `keccak256/512`, `ripemd160` | hash tables (SHA-256 L5; a new Keccak-f table; RIPEMD table) | L5 |
| `ed25519_verify` | shared non-native field chip (D1-S) | D1-S plan |
| `ecrecover`, `alt_bn128_*`, `bls12381_*` | non-native field/curve chips (D3γ/δ) | new |
| register ops, `read/write_memory`, `input`, `value_return`, `log_*` | `memcpy16` between the register space and linear memory, UTF-8/16 decoder | new, small |
| promise/receipt creation (`promise_*`, actions) | action-dispatch bus → `rcptV3D3` | D2/D3 action bus (study §5) |
| context getters (`block_timestamp`, `account_balance`, …) | public-input lookups | — |

### 3.2 Gas vs proving cost (gas costs from `spec/lean/v3/NearSpecV3/Wasm/Machine.lean`)

Proof cost is in work cell-eq. SHA-256 is **M** at 319 work cell-eq per byte (spike 3); the other rows are **D**.
The reference row is the worst *measured* WASM operator: the unaligned `i32.load` chain at 281 work cell-eq per
822,756 gas = **3.4·10⁻⁴ cell-eq per gas**.

| op | gas | proof cost | cell-eq/gas (approx.) | vs worst WASM |
|---|---|---|---:|---|
| storage_write base (trie update, ≈ 8 node hashes) | 64.2 G | ≈ 100 SHA-256 blocks × 20 k = 2.0 M | 3.2e-5 | 10× cheaper |
| touching a trie node | 2.28 G | ≈ 8 blocks × 20 k = 160 k | 7.0e-5 | 5× |
| storage_read value byte | 5.61 M | ≈ 319/B (SHA of the value) | 5.7e-5 | 6× (bounded by the witness size) |
| sha256 byte | 24.1 M | 319 (**M**) | 1.3e-5 | 25× |
| keccak256 byte | 21.5 M | ≈ 735 (bit-level Keccak-f, 136 B per block; **A**) | 3.4e-5 | 6× |
| ed25519_verify | 210 G | ≈ 3.6 M (study §2.4) | 1.7e-5 | 12× |
| read_memory / write_memory byte | 3.8 / 2.7 M | `bulk16` ≈ 23 per byte | 7e-6 | 50× |
| read_register into memory, per byte | 98,562 + 2,723,772 (`write_memory_byte`) = 2.82 M | `bulk16` (**M**) ≈ 23 per byte | 8e-6 | ≈ 45× cheaper (**corrected**: an earlier draft counted only `read_register_byte` and called it on par) |
| **contract loading byte** (`contract_loading_bytes`) | **1,089,295** | SHA-256 (319, **M**) + PREP (≈ 218, D) = 537 | 4.9e-4 | **1.45× the worst op**, proved during execution (§3.4) |
| memory.copy/fill byte (linear unit = regular) | 822,756 | `bulk16` (**M**) ≈ 23 per gas unit | 2.8e-5 | 12× |
| `memory.grow` per page | 822,756 | 0 until touched (lazy zero-init) | — | — |

**Registers used as host-function inputs** (`memOrReg`: `ptr = register id`, `len = u64::MAX`). These pay only
`read_register_byte` = 98,562 gas/B plus the host function's own fee.
* Rule: host chips consume register bytes **by reference**, i.e. register space is a memory space read through the
  memory argument, and there is no copy.
* Per-byte proving work then happens only where the host function's own per-byte fee pays for it (hashing, storage,
  logs, action arguments).
* The one exception is `value_return` with no receivers, which has no per-byte fee. Its value is hashed once per
  call into the execution outcome. The bytes it can return come from:
  * `input` (paid by `function_call` action bytes, 2.2 Mgas/B);
  * `promise_result` (paid by `new_data_receipt_byte` when the data receipt was created);
  * storage reads (bounded by the witness);
  * sha256 outputs or other 32-byte results.
* All of these are in the incoming witness or the chunk's own receipts, so their total is bounded by the witness
  size, not by gas.
* `input` and `promise_result` write registers without a per-byte charge (`chargeBytes := false`). That is the same
  argument: the bytes are already in the witness.

**Cheap-gas / expensive-proof operations.** None found above the worst WASM operator, given four conditions:
1. Register copies go through the `bulk16` chip.
2. Registers are consumed by reference.
3. Storage-read value bytes stay bounded by the state-witness limit (as D0a's A7).
4. Contract preparation stays within the budget of §3.4.

### 3.3 Is a proving-weighted gas bound (P-RT-1) still needed?

**No, for the decided target** (≤ 2 s after execution on 32 H200; decisions P-PERF-6/7):
* the worst WASM operators measure 195–281 work cell-eq per gas unit;
* contract loading is 406, but it is proved during execution (§3.4).

So the bound follows from total gas. A weighted budget is needed only for 16 GPUs or for ≤ 1 s after execution.
P-RT-1' (a code-byte cap) was **declined** (decision D).

### 3.4 Many distinct contracts at 1 Pgas (no code cap)

**Volume.**
* Loading charges 1,089,295 gas per code byte.
* Each call also costs at least the function-call receipt fees (≈ 0.22 Tgas: `new_action_receipt` 108 Ggas send +
  exec, plus `function_call` base).
* With 4 MiB contracts (the protocol maximum) a 1 Pgas chunk loads ≈ **0.88 GB of code from ≈ 210 distinct
  contracts** (D).
* Repeated calls of the same code pay loading every time but are prepared once (deduplicated by code hash).
* Code does not travel in nearcore's state witness, so the prover's witness carries it.

**What the proof must do per code byte (no registry, decision D):**

| part | cost per byte | label |
|---|---:|---|
| SHA-256 code hash (binds the code to the account's `code_hash`) | 163 main cells, ≈ 319 work cell-eq | **M** (spike 3, SHA-256 layout) |
| decoder: byte stream → instruction records (LEB128, opcode classes); one row per byte | 16 main / 3 fractions | D |
| validator + finite-wasm gas/stack analysis + register-form translator; ≈ 0.5 instructions per byte | 50 / 14 per instruction | D |
| code-table rows emitted (≈ 0.2 per byte) | 20 / 2 | D |
| **total** | **≈ 537 work cell-eq per byte ≈ 406 per gas unit** | M + D |

The total is ≈ 1.45× the worst WASM operator per gas.

**Design: an early PREP sub-proof (PROPOSAL P-PERF-8).**
* Every contract a chunk executes is known at chunk start: receivers of incoming, delayed and local receipts and of
  the chunk's transactions, plus code deployed by `DeployContract` actions in those receipts.
* PREP plus the code hash therefore run as **separate proofs with their own transcripts, started at t = 0**. They
  overlap the ≈ 1.2 s native execution.
* Each PREP proof outputs the Merkle root of the code table it built. The main proof commits the same code table as
  a preprocessed table with that root. L1 verifies both proofs and checks that the roots are equal.
* Soundness: both statements are about the same committed table. The main proof's bus challenge α is drawn after
  that root is in its transcript.
* Split PREP into batches of contracts, each its own sub-proof. That keeps memory per GPU below HBM: one proof over
  the whole 0.88 GB would need ≈ 142 GB per GPU at 32 GPUs.

Model (32 H200, 35 % efficiency):
* the code-loading chunk lands **1.26 s after execution**;
* without early PREP it would be 1.98 s (sensitivity);
* PREP must stay ≤ ≈ 420 work cell-eq per code byte (≈ 1.9× the D estimate) to keep this case ≤ 2 s.

PREP's in-AIR cost is therefore **the second-largest open risk** (spike P1, §9.1).

---

## 4. Proof system for throughput under PQ and proven bounds

### 4.1 Field

| field | element | 2-adicity | ext for \|K\| ≥ 2²⁹⁰ (PQ, U-6) | GPU/SIMD | WASM fit | Lean |
|---|---|---|---|---|---|---|
| **BabyBear** (current) | 31 bit | 27 | **degree 10** (2³¹⁰; X¹⁰ − W exists since 10 \| p − 1) or 12 | 32-bit Montgomery, packed AVX2/512, CUDA mature | u32 = 2 limbs; mul needs bytes | L1 exists |
| KoalaBear | 31 bit | 24 | degree 10 | same | same | new L1 (small) |
| M31 (circle STARK, Stwo) | 31 bit | (circle group 2³¹) | degree 10 (QM31⁵ is not a tower in use) | fastest CPU reduction | same | **new**: circle FFT, circle FRI, new L3 |
| Goldilocks | 64 bit | 32 | degree 5 (2³²⁰) | 64-bit mults are emulated on GPU (≈ 3–4× per element) | i64 nearly 1 limb, mul with 32-bit limbs | new L1 |

**Choice: BabyBear with degree 10.**
* Degree 10 is the smallest that meets 2²⁹⁰ (degree 12 if the M3 constants need slack).
* Goldilocks halves the extension degree, but doubles bytes per base cell (hashing and NTT are per byte) and
  costs ≈ 3× per GPU multiplication. That is net worse at our hash-dominated cost (D).
* The 2-adicity of 27 caps LDE at 2²⁷. That is not binding with per-GPU tables of ≤ 2²⁴–2²⁶ rows at rate 1/2.

**The extension degree is the second-largest sensitivity:**
* E = 8 → 12 moves the adversarial post-execution latency 1.50 → 2.38 s;
* every bus fraction and quotient/DEEP cell scales with E or E².

So keep E at the minimum the PQ M3 analysis allows. Do not trade it for "safety margin" without a number.

### 4.2 Low-degree test, rate and queries

PQ per-round target ≈ 260 bits (`t²·ε_rbr` loss at t = 2⁶⁴; study §11.2). Grinding z buys only z/2 bits (Grover).
Per-query bits:

| rate | UDR −log₂((1+ρ)/2) | Johnson ½log₂(1/ρ) − 0.1 | queries (z = 16) | prover LDE + hash cost vs rate 1/2 |
|---|---:|---:|---:|---:|
| 1/2 | 0.415 | 0.40 | **608** | 1× |
| 1/4 | 0.678 | 0.90 | 280 (Johnson) / 372 (UDR) | ≈ 1.6× |
| 1/8 | 0.830 | 1.40 | 180 / 304 | ≈ 2.8× |
| 1/16 | 0.912 | 1.90 | 133 / 277 | ≈ 5× |
| 1/64 | 0.977 | 2.90 | 87 / 258 | ≈ 19× |

* **Base layer: rate 1/2.** Queries only cost recursion work. With a distributed base proof and global trees
  (§5) the L1 verifier is ≈ 5–10 % of the worst-case base work, so prover LDE cost wins: rate 1/4 is +0.4 s in
  the sensitivity table.
* At rate 1/2, **UDR (proved in Lean today) and Johnson give the same query count**. The base layer needs no
  Johnson proof.
* **L1/L2: rate 1/4** (280 queries, Johnson). **L3: rate 1/16** (133 queries, Johnson); this makes the final
  verifier cheaper. **Final layer: rate 1/32, Johnson** (102 queries at z = 32) ⇒ **≈ 0.84 MB** (SHA-384,
  arity-16 FRI, `model.py size_final`, which reuses `pqsize.py`'s formula).
  * A final layer at rate 1/64 gives 0.74 MB but costs +0.14 s.
  * Both are within U-9's 0.5–1 MB.
* **The Johnson regime is therefore needed for L1–L3 and the final layer.**
  * With UDR only (rate 1/4: 372 queries; 1/16: 277), the tail grows by ≈ 0.3 s and the proof to ≈ 2 MB (study
    §11.4).
  * The research-branch M2 proof (study S4) is on the latency path as well as the size path.
* STIR/WHIR (C: eprint 2024/390, 2024/1586) reduce the final layer to ≈ 0.3–0.5 MB (study §11.4). They are a size
  lever and also shrink the final verifier.

### 4.3 Merkle commitments with SHA-384

* **Leaves are row digests.** `leaf_i = H(0x01 ‖ row_i)` over all columns of all tables of a height class on one
  GPU. For a distributed proof the global leaf is `H(0x03 ‖ d_{1,i} ‖ … ‖ d_{N,i})` (§5.2).
* Node: `H(0x02 ‖ l ‖ r)` = 97 B = **one** SHA-512 compression (≤ 111 B fits one block). Arity 2 is optimal per
  compression. Arity 4 costs 2 compressions per node, i.e. the same per level.
* **Caps** at log₂(q) levels (top 2⁹–2¹⁰ digests, ≈ 25–50 KB) cut every in-circuit path by 9–10 compressions. The
  proof-size cost is included in the final-layer model.
* Native hashing per committed cell at rate 1/2 is 8 B, i.e. 1/16 compression. That is ≈ 180 INT32 ops at the
  hashcat-derived 2,750 ops per SHA-512 compression (A). Hashing is ≈ 26 % of per-cell work. Without SHA-512
  instructions it is ≈ 2–3× the per-byte cost of SHA-256 with SHA-NI on CPU (spike, §9.2).

### 4.4 Buses: logUp vs grand products vs GKR

| argument | committed aux per fraction | prover work per fraction (E = 10) | proven soundness | Lean |
|---|---|---|---|---|
| per-interaction grand product (today, `auxGroup` g = 1; degree 4 → q = 3) | E (one ext column per interaction) plus chain columns for multi-bit multiplicities | ≈ 4.4 k + 10 cells | yes (L3/L4 today) | done |
| **logUp, 2 fractions per helper column (degree 3)** | E/2 + E per table running sum | ≈ 4.4 k + 5 cells ≈ **7.9 k ops** | yes: Haböck, eprint 2022/1530; error ≈ (total fractions + multiplicity bound)/\|K\| per challenge, fine at \|K\| = 2³¹⁰ | **new L3/L4 lemma, 8–15 k lines** (P-PERF-2) |
| LogUp-GKR (Papini–Haböck, eprint 2023/1284) | 0 (plus an MLE-evaluation bridge to a univariate commitment, ≈ 2E per height) | ≈ 13 k (28 extension multiplications per leaf over layers; D) | yes: sumcheck soundness | 25–45 k (sumcheck, GKR, MLE bridge) |

**Choice: committed logUp (k = 2)** for prover work. GKR saves committed cells and proof bytes (no aux openings),
but at E = 10 its per-fraction arithmetic is ≈ 3× the committed variant's.

The "bits as multiplicities" layout of today's prover (chain columns 2(k−1)·E per multi-bit interaction) is
replaced by a base-field multiplicity column. It costs 1 cell instead of ≈ 2(k−1)·8.

### 4.5 Quotient and constraint degree

* **Constraint degree ≤ 3** (including selectors and logUp helpers). Then the quotient domain (2n) equals the
  rate-1/2 commitment domain: no extra LDE, and q = 2 quotient chunks.
* Today's degree-4 tables need a 4n evaluation domain and q = 3.
* **One quotient per height** (PROPOSAL inside P-PERF-3). All tables of the same height on a GPU combine with α
  powers into one composition polynomial. That is exactly "one wider table", so soundness is unchanged. Today's
  prover already shares FRI by class.

### 4.6 Multilinear/sumcheck backend: honest evaluation

Option ML: zerocheck sumcheck over the AIR, LogUp-GKR for the buses, a multilinear PCS (Basefold- or WHIR-style;
C: SP1 Hypercube and Jolt follow this pattern).

* Committed cells: only main (10 / 21 / 38 per op). No quotient, no aux. Memory per GPU drops ≈ 2×.
* Prover work at E = 10: **higher** than U-logUp (98 / 207 / 455 vs 73 / 153 / 308 cell-eq per op). GKR fractions
  dominate, and zerocheck rounds run in the extension.
* The advantage reverses only if E falls. With a QROM analysis that admitted E = 5–6, ML would win by ≈ 1.3×. Or
  if fractions per op fall below ≈ 3.
* Proof size: polylogarithmic without the AIR openings. It still needs the same PQ query counts at the PCS.
* **Lean:** sumcheck (portable from ArkLib's proved sumcheck, not importable, since it needs Mathlib), GKR, the
  multilinear PCS (proximity gaps for the folded code), rbr knowledge soundness. ≈ 60–120 k lines, overlapping
  research M2. The univariate path reuses L3.

**Verdict:** keep the univariate STARK for the PQ real-time track. Re-evaluate ML if M3 pins E ≤ 6.

---

## 5. Segmentation, distribution, recursion and aggregation

### 5.1 Why the study's tree was expensive

* Verifying one segment proof in-circuit costs q × (≈ 150 compressions) × 20–30 k cells. At q ≈ 250–600 that is
  0.8–3 G cells per *child*.
* An arity-4 tree over hundreds of segments pays that at every node, on the critical path: ≈ 0.3–1 s per level ×
  4–6 levels.

### 5.2 Shared-transcript distributed base proof (PROPOSAL P-PERF-4)

The chunk's whole trace is **one STARK**. GPU g owns a slice of execution and holds one table per chip class
(segments concatenated, ≤ 2²⁴ rows).

1. Every GPU commits its main trace. GPU g computes row digests `d_{g,i}`. An **all-to-all of digests**
   (2²⁵ × 48 B ≈ 1.6 GB per GPU at 2²⁴ rows) gives each GPU a range of global leaves
   `H(d_{1,i} ‖ … ‖ d_{N,i})`. GPUs build their subtrees and the root combines them.
   * Traffic: ≈ 32 ms at 50 GB/s per GPU over IB, overlapped with execution.
2. The transcript absorbs the global root, so α and γ are the same everywhere.
   * Each GPU computes its fractions and aux columns, then commits them the same way.
   * Global bus balance = Σ over GPUs of the logUp finals: a few extension elements per GPU.
3. Quotients are per GPU (constraints are row-local), committed globally.
4. DEEP, then **FRI per GPU**: N independent FRI instances with shared challenges, with no all-reduce of
   codewords.
   * Soundness is a union bound over instances (+log₂N bits; 5 bits at N = 32, absorbed in the 260-bit target).
5. Queries open one global path per tree plus each GPU's FRI path.

* Soundness: this *is* a multi-table STARK with mixed heights and global buses, which L3/L4 already prove.
  * The deltas are the two-level leaf hash (a FORMATS change) and the N FRI instances.
* Lean: ≈ 5–10 k lines (§8).
* Cross-segment memory and state continuity become ordinary global-bus terms. There are no per-segment memory
  images and no boundary proofs.

### 5.3 Compression chain (PQ, SHA-384 in-circuit; U-7)

The worst case below is the measured unaligned `i32.load` chain at 1 Pgas on 32 H200 (`model.py`).

| layer | proves | on | rate | queries | time |
|---|---|---|---|---|---|
| base | the chunk | 32 GPUs | 1/2 | 608 | phase B 1.20 s after the last root |
| L1 | verifier of base: each GPU verifies its own openings and FRI; global paths shared | 32 GPUs, distributed the same way | 1/4 | 280 | 0.14 s |
| L2 | verifier of L1 | 32 GPUs (P-PERF-4; not transmitted) | 1/4 | 280 | 0.08 s |
| L3 | verifier of L2 (fixed point ≈ 2²¹ rows × 400) | 32 GPUs | **1/16** | 133 | 0.07 s |
| final | verifier of L3 | **one node** (one FRI instance: the transmitted proof) | **1/32** | 102 | 0.17 s; **proof ≈ 0.84 MB** |

* Totals: recursion is 7.6 of 42.5 GPU-s (18 %); the tail is 0.46 s.
* Per in-circuit SHA-384 compression: **≈ 38 k work cell-eq (M**, spike 3: 25.7 k main cells, 764 fraction slots;
  E = 10 logUp projection). The first draft assumed 20 k.
* Raising L3's rate to 1/16 and distributing L2/L3 recovered the cost: the tail went from 1.04 s to 0.46 s.
* Sensitivity of the in-circuit SHA-384 cost: 20 k → 50 k moves the worst case 1.57 → 1.86 s.

### 5.4 Hash-based accumulation (Arc, WARP)

* **Arc** (Bünz, Mishra, Nguyen, Wang; eprint 2024/1731, C): accumulation for Reed–Solomon proximity claims.
  Hash-based, unbounded depth, **proven in the ROM** (classical). Plausibly PQ, but **no QROM proof**.
* **WARP** (eprint 2025/753, C): linear-time accumulation for any linear code. Same status: ROM-proven,
  "plausibly post-quantum".
* Both replace "verify a full FRI per child" by an accumulation step whose verifier opens far fewer Merkle paths.
  That would shrink L1–L3 by several times.
* In this design the compression tail is already ≈ 0.5 s and ≈ 10 % of work. Accumulation would save ≈ 0.2–0.3 s.
  It would also add a new protocol needing a QROM knowledge-soundness proof (research M3/M4), which neither paper
  provides.
* **Not recommended for the real-time track now.** Revisit if the research branch proves a QROM extractor for an
  RS accumulation scheme.

### 5.5 Pipeline (critical path)

```
t=0 ─ native execution with checkpoints (≈1.2 s/Pgas) ──────────────┐
      ├─ segment k traced on host cores → GPU phase A (LDE + leaf digests) ─ streaming
      └─ digest all-to-all per class (overlapped)                     │
                                                       last root ─────┴─► α, γ
phase B (all GPUs): fractions + aux commit → quotient + commit → DEEP → per-GPU FRI → openings
L1 (all GPUs) → L2 (all GPUs) → L3 (all GPUs) → final (one node) → proof
PREP + code-hash sub-proofs: start at t=0 (code known at chunk start), verified in L1
```

Worst case (unaligned load chain), 32 H200, 35 % efficiency (`model.py`):
* exec 1.20 s;
* phase A done during execution (0.13 s of work);
* phase B 1.20 s;
* tail 0.46 s;
* ⇒ **2.94 s from start, 1.74 s after execution**.

In the code-loading worst case, the PREP sub-proofs run from t = 0 and finish ≈ 1.9 s after the start. The main
proof is small, and the tail (L1 now also verifies the PREP proofs) is 0.52 s, giving **1.26 s after
execution**.

---

## 6. GPU mapping (design only)

**Memory per GPU (D, `model.py mem_gb_per_gpu`).**
* Trace 4 B and LDE 8 B per committed cell. Worst case at 32 H200: ≈ 80 GB of 141 GB; 16 H200: ≈ 160 GB.
* Mitigation on 16 H200: keep only coefficients and recompute LDE blocks for phase B (+≈ 25 % NTT work), or spill
  to the 2 TB host RAM over PCIe 5 (≈ 50 GB/s).
* Typical chunks need 26–64 GB.

**Kernels.**
* **Phase A:**
  * iDFT (coefficient form, kept for phase B);
  * coset DFT to the 2n domain;
  * SHA-384 leaf digests;
  * Merkle subtree.

  NTT is memory-bound at ≈ 3 passes of radix-2⁸ in shared memory. Leaf hashing is fused into the DFT output
  epilogue, so LDE values are hashed while in registers and LDE rows are not re-read.
* **Phase B:**
  * fraction denominators: fingerprints in Fp10, base × extension products;
  * batched inversion (Montgomery trick per thread block);
  * logUp helper columns;
  * quotient evaluation: constraint DAG compiled to CUDA from the Lean-exported layout, as the study proposes;
  * DEEP linear combination;
  * per-GPU FRI folding (arity 16);
  * opening extraction.
* **Extension arithmetic.** Fp10 multiplications as 100 Montgomery products with lazy reduction (BabyBear
  products accumulate in 64 bits): ≈ 450 INT32 ops (D).

**Multi-GPU and multi-node.**
* Data parallel by execution slice. There is no cross-GPU NTT: tables are per GPU.
* Communication:
  * digest all-to-all per tree: ≈ 1.6 GB per GPU per class, 3 trees, ≈ 0.1 s total on IB, overlapped except the
    last;
  * transcript roots and logUp finals: KB;
  * L1 inputs are local;
  * L1 → L2: the L1 proof (tens of MB) to one node: ≈ 10 ms.

**Interconnect.**
* Within a node, NVLink 4 (900 GB/s per GPU) is ample.
* Between nodes, 4 × 400 Gb/s per node (study §3.3) suffices, since the digest all-to-all is the only bulk traffic.
* Worst case it is 32 × 1.6 GB × 3 trees ≈ 150 GB per proof spread over ≈ 1.2 s of execution: ≈ 125 GB/s
  aggregate, i.e. ≈ 4 GB/s per GPU.

**Host side.**
* Pass 2 tracing needs ≈ 150 cores per node (A: 20 M ops/s/core).
* Trace upload over PCIe 5 at ≈ 50 GB/s per GPU: the worst case is ≈ 2.7 G cells × 4 B ≈ 11 GB per GPU over
  1.2 s ≈ 9 GB/s.

---

## 7. End-to-end model (`tools/perf-design/model.py`)

Parameters and labels are printed by the script. Chip and SHA costs are **M** (spikes 3–4), PREP is D, and GPU
efficiency (35 % of peak INT32) is **A**. The adversarial row is the maximum-latency candidate.

| scenario (1 Pgas) | backend | GPUs | WASM ops | committed cells/op | cell-eq/op | GPU-s | recursion share | latency from start / after exec | proof | GB/GPU |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| typical-measured | U-logUp | 16 | 4.1e7 | 42 | 71 | 8.6 | 58 % | 1.97 / 0.77 s | 844 KB | 53 |
| typical-measured | U-logUp | 32 | 4.1e7 | 42 | 71 | 8.6 | 71 % | 1.79 / 0.59 s | 844 KB | 26 |
| mainnet-like | U-logUp | 16 | 3.6e8 | 90 | 153 | 13.1 | 40 % | 2.30 / 1.10 s | 844 KB | 64 |
| mainnet-like | U-logUp | 32 | 3.6e8 | 90 | 153 | 13.1 | 49 % | 1.96 / 0.76 s | 844 KB | 32 |
| **adversarial (load chain)** | U-logUp | 32 | 1.22e9 | 162 | 281 | 42.5 | 18 % | **2.95 / 1.75 s** | 844 KB | 78 |
| adversarial (code loading) | U-logUp | 32 | — | 314 | 409 | 61.2 | — | 2.48 / 1.28 s | 844 KB | (PREP split into batches, §3.4) |
| adversarial (code loading) | U-logUp | 16 | — | 314 | 409 | 61.2 | 14 % | 4.59 / 3.39 s | 844 KB | 295 |
| adversarial | U-GKR | 32 | 1.22e9 | 52 | 403 | 60.4 | 10 % | 3.45 / 2.25 s | 844 KB | 85 |
| adversarial | ML | 32 | 1.22e9 | 32 | 387 | 58.0 | 10 % | 3.37 / 2.17 s | 844 KB | 76 |

Per-candidate latency at 32 GPUs (after execution):

| candidate | after execution |
|---|---:|
| load chain | 1.75 s |
| div chain | 1.63 s |
| mul chain | 1.40 s |
| empty calls | 1.34 s |
| code loading | 1.28 s |
| memory.copy | 0.60 s |
| `read_register` copies | 0.52 s |

**What 1 Pgas worst case needs** (adversarial, U-logUp; `model.py required`):

| target | 16 H200 | 32 H200 |
|---|---|---|
| proof ≤ 2 s after execution | 56 % of peak INT32 ≈ 13.3 G cell-eq/s/GPU | **30 % ≈ 7.1 G cell-eq/s/GPU ≈ 25 M worst-case ops/s/GPU** |
| proof ≤ 1 s after execution | 126 %: impossible | 68 % ≈ 16.1 G cell-eq/s/GPU: not plausible |

**Sensitivity** (adversarial, U-logUp, 32 H200, latency after execution; base 1.75 s):

| parameter | low → latency | high → latency | swing |
|---|---|---|---:|
| **GPU efficiency** (0.2 / 0.6) | 3.03 s | 1.10 s | **1.92 s** |
| **PREP cost scale** (1× / 3× the D estimate) | 1.75 s | 2.89 s | **1.14 s** |
| **extension degree E** (8 / 12) | 1.36 s | 2.19 s | **0.83 s** |
| base rate (1/2 / 1/4) | 1.75 s | 2.22 s | 0.47 s |
| native SHA-512 cost on GPU (2,000 / 5,500 ops) | 1.68 s | 2.00 s | 0.32 s |
| NTT ops per cell (200 / 450) | 1.62 s | 1.93 s | 0.31 s |
| in-circuit SHA-384 (20 k / 50 k; measured 38.8 k) | 1.57 s | 1.86 s | 0.29 s |
| L2/L3 distributed (off / on) | 2.03 s | 1.75 s | 0.28 s |
| early PREP sub-proof (off / on) | 1.99 s | 1.75 s | 0.25 s |
| rbr bits, table height, witness, grinding, exec slowdown | | | ≤ 0.13 s |

**CPU calibration (clean, M).**
* 7 Zen 5 cores: 227 M trace cells/s for rate-1/2 LDE + SHA-384 Merkle.
* The model counts 486 INT32 ops per cell for that phase, so ≈ 1.1·10¹¹ model-ops/s against ≈ 1.2·10¹² peak
  32-bit AVX-512 lane-ops/s. That is ≈ 9 % "efficiency" on CPU.
* The 35 % GPU assumption is ≈ 4× the CPU figure, consistent with GPU NTT/hash kernels being far closer to peak than
  this prover's CPU path. Spike H1 must confirm it.

## 8. Formal-admission impact

| component | content | reuse | Lean est. (lines) |
|---|---|---|---|
| L3/L4: logUp buses (P-PERF-2) | helper columns, running sum, base-field multiplicities; soundness vs \|K\| | L3 FS/IOP skeleton, L4 `HoldsP` | 8–15 k |
| L3: rate 1/2, degree-3 quotient domain, one quotient per height | parameter change and a "union of tables" lemma | L3 UDR (rate-generic?), DESIGN §5 | 3–8 k |
| degree-10 extension | re-instantiate Fp8 lemmas (keep them generic, study §11.6) | L1 | 2–5 k |
| distributed proof (P-PERF-4) | two-level leaf hash (FORMATS), N FRI instances, union bound | L2/L3 MMCS | 5–10 k |
| register-form PREP (P-PERF-1) | `translate` as a Lean function; block simulation `run_reg (translate c) ≈ Wasm.Exec.run c`, including gas (`gasTable` fees) and traps; PREP AIR ⇒ table = translate(code) | `NearSpecV3.Wasm.{Exec,FiniteWasm,Validate}` | 25–45 k |
| chips (≈ 20 classes) | `TableLocal → View` per chip, protocol-independent | v1 `DEP`-row byte arithmetic, D1 `txV3` | 40–70 k |
| memory argument (timestamps, slices) and stack-temp channels (P-PERF-5) | multiset + timestamp ⇒ read-latest; channel matching lemma | D1 `MEM`/`AKMEM` pattern | 12–25 k |
| gas folding (lazy check) | monotonicity ⇒ one check per call | `FiniteWasm` | 3–6 k |
| host chips | trie (reuse), SHA-512 family (shared with D1-S), Keccak, memcpy, register space | L5, L6 | 20–40 k (excluding curves) |
| recursion AIR vs `npVerifierP` (SHA-384, Fp10, logUp) | study §2.3 table, re-parameterised | L5 SHA-512 table, L4 `Expr` | 80–165 k (study) |
| PQ: Johnson for the final layer only; rbr + QROM FS | research branch M2–M4 | — | research |

**Total new (excluding research and recursion): ≈ 120–230 k lines.**

### 8.1 Soundness lemmas the adopted baseline needs (tracking)

| decision | lemma (statement sketch) | depends on | status | spike evidence |
|---|---|---|---|---|
| P-PERF-1 register form | `run_reg (translate c) s ≈ Wasm.Exec.run c s` per basic block (operand stack ↔ pending operands, fees = finite-wasm `gasTable`, traps preserved), lifted to whole calls | `NearSpecV3.Wasm.{Exec,FiniteWasm,Validate}` | open | translator differential-tested on 6 programs (locals, memory, gas equal to the reference) |
| P-PERF-1 PREP | PREP AIR ⇒ code table = `translate(decode(code))` ∧ SHA-256(code) = `code_hash`; P-PERF-8: PREP proof root = main proof's code-table root | L5 (SHA-256), decoder spec | open | SHA-256 layout measured; PREP not built |
| P-PERF-2 logUp | Σ over all tables of `m/(γ − fp(msg))` = 0 at random γ ⇒ multiset equality, with error ≤ (total fractions + max multiplicity)·deg/\|K\| per challenge; helper-column constraints of degree ≤ 3 | L3/L4 FS skeleton | open (the prover today uses grand products) | spike runs on grand products; logUp is projected in the cost model |
| P-PERF-3 rate 1/2, degree ≤ 3, one quotient per height | rate-generic UDR bound (L3); "tables of equal height = one wide table" composition lemma | L3 | open | — |
| P-PERF-4 shared distributed proof | two-level leaf hash (row digest per GPU, then global) is a vector commitment; N FRI instances with shared challenges ⇒ union bound (+log₂N bits); global bus = Σ per-GPU finals | L2/L3 MMCS | open | — |
| P-PERF-5 stack-temporary channels | if every channel slot's produce/consume events alternate (WASM validation + induction over a correct prefix), then multiset equality with `t_p < t_c` forces each consumer onto its own producer | memory-argument lemma | open | channel discipline asserted in all 6 runs; tamper of a consumed value caught on the bus |
| memory argument (timestamps `8·ts + k`, single lookup) | read-latest: multiset (recv prev, send new) + boundary table + `t − t_prev − 1 ∈ [0, 2^R)` ⇒ each read sees the last write; slice-local time with cross-slice flag | D1 `MEM` pattern | open | all runs balanced; T2-style tamper caught |
| public binding | code / initial memory / io records are public-segment messages consumed exactly once (code act flags, `mbound` strict order, `has_init`) | L4 `HoldsP` with `pubSegs` (exists) | spike done | honest proofs verify; claim edits rejected |
| P-PERF-8 early PREP sub-proof | two proofs bound to one committed table root; the main transcript absorbs the root before α | L2 | open | — |

 Recursion adds 80–165 k, as in the study.

**Judge budget.**
* D0a is 8,734 s single-core for 3,964 modules (V3-D1-DESIGN §6.3). This adds ≈ 1,500–3,000 modules.
* It fits only under **P-RT-3** (parallel elaboration, N = 16, 4 h wall).
* Requirements:
  * small modules, one per chip constraint family;
  * no large `decide` tables: range/byte tables are generated and proved by a fold lemma, not enumerated;
  * the critical path measured by S7.

**Soundness claims tied to bounds:**
* every committed-layer claim uses UDR (proved) or Johnson (research M2, final layer only);
* the logUp claim uses its \|K\| bound;
* the distributed proof adds log₂N to the union bound;
* nothing uses a conjectured regime.

**Base layer at rate 1/2 needs no Johnson proof** (§4.2). This removes the Johnson dependency from every layer
except the final one.

---

## 9. Spikes

### 9.1 Plan and status (CPU now; H200 later)

Next spikes, in priority order:

| # | spike | measures | replaces assumption | status |
|---|---|---|---|---|
| 1 | hottest chips, v0 layouts | rows/op, m and f, prove/verify, CPU commit throughput | first-draft chip widths | **done** (§9.2) |
| 2 | extension-degree cost | ext multiplications and logUp fraction compute at E = 8/10/12 | `frac_ops` | **done**: clean 78 ns per E = 10 ext mul (generic); a fraction ≈ 8.6 cell-eq on CPU vs 11.3 in the model |
| 3 | SHA-512-family (SHA-384) and SHA-256 chips | cells and fractions per compression; prove/verify; forged proof | `sha384_cells`, code hash | **done**: 38.9 k / 20.7 k work cell-eq (§9.2b) |
| 4 | v1 chips: channels, single-lookup timestamps, unaligned ld/st, call/ret, div_u, bulk copy; public binding; forged proofs | m, f per form; claim binding; verifier rejection | §2.4 D rows | **done** (§9.2b) |
| **P1** | **PREP prototype**: decoder (LEB128, opcode classes) + validator/finite-wasm analysis + register-form translator in AIR, on real contracts | work cell-eq per code byte (budget ≤ ≈ 420) | `PREP_ROWS_PER_BYTE` (D); second-largest sensitivity | **next** |
| 5 | tracing interpreter vs native (wasmtime) on corpora and mainnet contracts | ops/s/core, checkpoint cost | 20 M ops/s/core (the spike machine does 8–30 M ops/s/thread) | next |
| 6 | logUp in the prover (committed helper columns) and a degree-3 refactor of the chips | real E = 10 aux cost | logUp projection | after P1 |
| 7 | mainnet replay (study S1) | real mix, WASM gas share, distinct code bytes per chunk | `MIX_MAINNET`, `wasm_share_mainnet` | needs data access |
| 8 | judge parallel elaboration (study S7) | critical path at `-j 16` | P-RT-3 | CPU |
| H1 | H200: fused coset DFT → SHA-384 leaf kernel; Fp10 fraction kernel; end-to-end `eff` on a 2²⁴ × 150 slice | sustained fraction of peak INT32 | `eff` (largest sensitivity; ≥ 30 % needed) | needs an H200 |
| H2 | 2 nodes: digest all-to-all, phase B end to end | sync overheads, interconnect | `sync_s`, §6 | needs 2 nodes |

### 9.2 Spike #1 results (CPU; contended, indicative only; clean re-runs in §7 and `clean.log` supersede the throughput rows)

Setup:
* Binary `tools/perf-design/wasmchip`, release build, `RUSTFLAGS` x86-64-v3 + SHA-NI.
* `nice -n 19 taskset -c 9,25`, `RAYON_NUM_THREADS=2`, `NPUDR_MEM_GB=8`. CPUs 9,25 are one Zen 5 core with SMT,
  shared with the refreeze lane.
* Raw output: `docs/e2e-results/v3-perf-design/spike1.log`.

**What was built.**
* A WASM subset: local.get/set/tee, i32/i64.const, i64.add/sub/mul/eqz, br, br_if, aligned i32.load/store.
* Its reference stack interpreter.
* The register-form translator of §2.2 (block-level gas fees, local/const folding, set-retargeting, eqz+br_if
  fusion, br folding).
* The register machine that records memory accesses.
* Chips as `npudr` tables on the **unchanged** np-udr-stark-v2 prover: `alu_ri`, `alu_rr`, `mul`, `brz`, `ld`,
  `st`, plus `mbound` (sorted, strictly increasing touched addresses), `code`, `io`, `range16` and `pair`.
* Buses: STATE, FETCH, MEM, RANGE, PAIR.
* These are the **v0** layouts: every slot is RW memory, timestamp differences use 2 × 16-bit lookups, and
  multiplicities are bit-encoded grand products, because that is what the existing prover supports.

**Correctness and soundness self-check (M).**
* For every program and size:
  * final locals and memory of the register machine equal the reference interpreter's;
  * Σ block fees = executed WASM ops;
  * 0 failing constraints and 0 unbalanced bus messages on the honest trace;
  * the deployed-parameter proof verifies (Rust verifier).
* T1: +1 on a result limb is caught by the constraint check (1 failing constraint). The prover refuses: "ALI
  identity fails".
* T2: the operand read is changed with the arithmetic kept consistent. There are 0 failing constraints but 8
  unbalanced memory-bus messages. The prover refuses: "bus products differ".
* T3: 1-bit flips at 16 spread offsets of an honest proof: **16/16 rejected by the verifier**.
* Limitation: the prover is read-only here and refuses dishonest traces, so T1/T2 show that the AIR detects the
  tamper, not that a forged proof is rejected. T3 covers the verifier side.
* The spike AIR leaves initial memory and io state unbound to public inputs. This is spike-only.

**Cells and fractions (M; per WASM op; chips + memory boundary; fixed tables excluded).**

| program | ops | rows | ops/row | main cells/op | fractions/op | committed/op U-logUp / U-GKR / ML (E = 10) | prover-actual W_eq/op (Fp8, GP, degree 4, padded) |
|---|---:|---:|---:|---:|---:|---|---:|
| measured-mix loop (`acc = acc·x + K; i -= 1` while i ≠ 0) | 917,507 | 262,145 | 3.50 | **10.6** | **5.1** | 46 / 16 / 11 | 65.8 |
| adversarial `i32.load` chain (16 per iteration, plus loop) | 425,987 | 294,913 | 1.44 | 21.3 | 11.9 | 102 / 35 / 21 | 137.5 |
| store/load loop (`mem[p] = v; v = mem[p+4]; p += 4`) | 1,179,651 | 327,681 | 3.60 | 9.3 | 4.3 | 42 / 16 / 9 | 61.1 |

Per chip row as built (v0):

| chip | m | f | v1 target (§2.4) m / f |
|---|---:|---:|---|
| `alu_ri` | 36 | 15 | 32 / 13 |
| `alu_rr` | 40 | 19 | 36 / 16 |
| `mul` | 55 | 35 | 49 / 32 |
| `brz` | 21 | 7 | 19 / 6 |
| `ld` | 31 | 18 | 20 / 12 |
| `st` | 29 | 18 | — |
| `mbound` (per touched address) | 15 | 4 | — |

The v1 savings (channels, single-lookup timestamps) are **D**, not yet measured (spike 4).

`model.py` reproduces the measured per-op cells and fractions from these layouts exactly for the two loops. The
store/load loop is within 0.8 cells/op: the model omits its 65 k memory-boundary rows.

**Today's prover on these AIRs (M, contended, 2 threads).** Blowup 16, 216 queries, SHA-256 WH, Fp8.
* 104 / 83 / 97 M committed W_eq per proof, proved in 17.8 / 16.5 / 16.6 s: **5.0–5.9 M W_eq/s**.
* Proofs are 2.2–2.3 MB. The fixed range16/pair tables (65,536 rows each) are ≈ 40 % of W_eq at these small sizes.
* Peak RSS ≈ 1 GB.

**CPU micro-benchmarks (M, 1 thread unless noted).**

| measurement | result |
|---|---|
| SHA-512/384 compression | 9.0 M/s per thread (1.15 GB/s); 9.7 M/s on 2 SMT threads |
| SHA-256 compression (SHA-NI) | 38 M/s (2.4 GB/s) |
| rate-1/2 LDE (cache-blocked `CosetDft`) + SHA-384 Merkle, 2²⁰ × 64 | **27.5 ns per trace cell** (iDFT 0.29 s, coset DFTs 0.40 s, leaves 0.86 s, nodes 0.29 s): hashing 62 % |
| same, 2 threads, at rate 1/2 / 1/4 / 1/16 | 21.7 / 40.0 / 151.6 ns per cell (hashing 68 / 74 / 78 %) |
| ext multiplication, generic schoolbook, E = 8 / 10 / 12 | 61 / 87 / 200 ns |
| Plonky3 Fp8 multiplication | 8.6 ns (7.1× the generic) |
| logUp fraction compute (generic) E = 8 / 10 / 12 | 532 / 633 / 1,391 ns |

Implications:
1. **On CPU, SHA-384 dominates commitment (62–78 %).** x86 has no SHA-512 instructions here, and 4-column leaf
   padding wastes up to 33 %. On GPU the model's derived split is NTT 43 %, hashing 26 % (A, hashcat-derived).
   H1 must measure it.
2. **A fraction costs ≈ 8 cell-eq on CPU** (Plonky3-grade extension arithmetic, D): 633 ns / 7.1 = 89 ns
   ≈ 3.2 cells + 5 committed aux cells. The model's GPU estimate of 11.3 is therefore conservative by ≈ 25 %.
3. **E = 12 costs 2.2× E = 10** in the generic code. E = 10 should be the target unless M3 forces more.
4. Rate 1/4 costs 1.84× rate 1/2 per cell on CPU, and rate 1/16 7×. This confirms rate 1/2 for the base layer.
5. Our register machine with access recording runs at 7–8 M rows/s ≈ 12–27 M WASM ops/s on one thread
   (0.036–0.043 s for 0.26–0.33 M rows; HashMap-based, unoptimised). Trace build adds 0.02–0.08 s. That is
   consistent with the 20 M ops/s/core pass-2 assumption, which spike 5 settles against native.

**Core count for clean measurements.** These numbers are on one contended SMT core.

| purpose | request |
|---|---|
| spike 4 and multi-threaded scaling | 8 dedicated physical cores (16 threads), e.g. 10–15,26–31 after the D1 lane |
| prover runs at 2²⁰–2²² rows | ≥ 4 cores, ≥ 32 GB RAM |

### 9.2b Spikes 3 and 4: v1 chips, public binding, forged proofs, SHA chips

Raw output: `docs/e2e-results/v3-perf-design/spike4.log` (single SMT core 9,25) and `clean.log` (CPUs 9–15,25–31).

**What was built** (`tools/perf-design/wasmchip/src/v1.rs`):
* A multi-function WASM subset: locals, consts, i64 add/sub/mul/div_u/eqz, br/br_if, unaligned i32.load/store,
  call/end with params and results, memory.copy.
* Its reference interpreter, the register-form translator with typed operands, and the register machine.
* Chips on the **unchanged** np-udr-stark-v2 protocol: every chip form plus `mbound`, `minit`, `code`, `io`,
  `range16`, `rangeT` (2²¹) and `pair8`.
* Timestamps `8·ts + k` with one `rangeT` lookup per access; stack temporaries as channels.
* **Code, initial memory (non-zero words) and the initial/final state are public-segment records** received by the
  tables.

**Correctness (M, every program).**
* Entry locals, the full linear memory and the gas units equal the reference interpreter's.
* Channel discipline (every temporary produced once and consumed once) holds.
* 0 failing constraints, and 0 unbalanced bus messages including the public segments.
* The honest proof verifies (Rust verifier).

**Measured per WASM op (chips + `mbound`; fixed tables excluded):**

| program | ops | rows | ops/row | main/op | fractions/op | committed U-logUp/op | prove (2 threads) | proof |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| measured-mix loop | 458,755 | 131,074 | 3.50 | 9.4 | 4.4 | 40 | 120–130 s | 3.2 MB |
| unaligned i32.load chain (16/iter) | 212,995 | 147,458 | 1.44 | 22.1 | 12.6 | 109 | 136 s | 3.9 MB |
| i64.div_u chain (8/iter) | 720,899 | 180,226 | 4.00 | 13.8 | 8.1 | 62 | 141 s | 3.7 MB |
| call chain (8 empty calls + 1 call with a result per iter) | 196,611 | 204,802 | 0.96 | 20.1 | 7.8 | 91 | — | — |
| unaligned store/load mix | 688,131 | 196,610 | 3.50 | 11.0 | 5.2 | 50 | 130 s | 3.7 MB |
| memory.copy 256 B/iter | 98,307 (2.45 M gas units) | 172,034 | — | 2.5 per gas unit | 1.6 per gas unit | — | 145 s | 3.4 MB |

**Forged proofs (M).**
* Setup: a dishonest prover, `tools/perf-design/forge`, is a generated copy of the deployed prover with
  environment-gated hooks. It skips the prover's own checks and optionally rewrites the OOD quotient values and the
  bus finals. The **verifier is the deployed one, byte-identical**: `gen.sh` checks it with `cmp`.
* Results on the measured-mix program:

| test | dishonest content | verifier |
|---|---|---|
| F1 | +1 on a result limb (constraint violation); naive forger | **rejects** (ALI identity fails) |
| F2 | same; forger patches the OOD quotient so the ALI identity holds | **rejects** (bus products differ) |
| F3 | operand value lie with consistent arithmetic (bus-only violation); naive | **rejects** (bus products differ) |
| F4 | same; forger rewrites a final so the bus products balance **and** patches OOD | **rejects** (final polynomial mismatch: the FRI/DEEP layer) |
| F5 | honest trace proved against a claim with a different final gas (public-binding forgery); finals balanced, OOD patched | **rejects** (final polynomial mismatch) |
| SHA chips | one working-state bit flipped; OOD patched | **rejects** (final polynomial mismatch), for SHA-256 and SHA-384 |
| B | honest proof checked against an edited claim (code byte, initial memory word, final gas) | rejects (Fiat–Shamir binding: openings no longer parse) |

* These are spot checks of the deployed verifier against specific forgery strategies. They are not a soundness
  proof, which is the Lean side's job.

**SHA chips (spike 3, M):** `wasmchip sha {256,384}`.
* Layout: two rounds per row; bit-words for a/e with a 3-word sliding window; message schedule rows with σ0/σ1 as
  committed limbs, exchanged over the bus.
* Every compression is checked against `sha2::compress256/512`.

| chip | per compression | main cells | fraction slots | committed (E = 10 logUp) | work cell-eq | per byte |
|---|---|---:|---:|---:|---:|---:|
| SHA-512 family (SHA-384 Merkle node: 1 compression) | 128 B | 26,347 | 764 | 34,037 | **38,850** | 304 |
| SHA-256 (contract code hash) | 64 B | 10,675 | 612 | 16,845 | **20,701** | 323 |

* The first draft assumed 20 k for SHA-384; the measurement is 1.9× that.
* The design absorbs it with the L3 rate change and distributed L2/L3 (§5.3).
* Further cuts are possible: a schedule window inside the round rows would remove ≈ 500 fraction slots, ≈ −15 %.

**Observation (prover completeness, not soundness).**
* A first SHA-384 layout sent σ0/σ1 as degree-3, 4-limb bus messages (table degree 6). Its honest proof failed the
  ALI identity even though the constraint and bus checks passed.
* The 2-limb (SHA-256) variant of the same layout proved fine.
* Committing σ as limbs (degree 4) fixed it.
* `nearAirV3` has no such messages. For the prover lane: **a possible completeness bug in np-udr-stark-v2 for
  high-degree, wide interaction messages**. Not investigated further.

**Measured vs model.**
* `model.py` reproduces the measured per-op main cells and fractions from the per-chip layouts. The differences
  are the loop-overhead rows and `mbound` rows of the test programs.
* The adversarial candidates in the model use the measured per-row (m, f) of the adversarial form, with 1 row per
  gas unit (or 0.5 for `local.get; op` pairs).

### 9.3 What to measure on an H200 first

1. The phase-A fused kernel (coset DFT → SHA-384 leaf digest) in cells/s.
2. Phase-B fraction throughput at E = 10 (fingerprint, batched inverse, helper column).
3. End-to-end `eff` on one slice of 2²⁴ rows × 150 columns.

These three numbers decide whether 32 H200 meet ≤ 2 s after execution.

---

## 10. Decisions needed (all PROPOSALS)

Decided on 2026-10-14 (section D): P-PERF-1…7 and P-RT-1' (declined). Still open:

1. **P-PERF-8 (protocol, new).** Contract preparation and code hashing as separate early sub-proofs, started at
   chunk start. They are bound to the main proof by the code-table root and verified in L1. They take the code
   cost (1.45× the worst WASM op per gas) off the post-execution path.
2. **Johnson regime for L1–L3 as well as the final layer.** This puts research-branch M2 on the latency path: UDR
   only costs ≈ +0.3 s and ≈ 2 MB.
3. **Final-layer rate**: 1/32 (≈ 0.84 MB, 1.74 s) or 1/64 (≈ 0.74 MB, +0.14 s). STIR/WHIR for ≤ 0.5 MB.
4. **Extension degree.** Ask research M3 for the minimum E with explicit constants; E = 8 → 12 moves the worst case
   1.35 → 2.19 s.
5. **CPU allocation.** For clean measurements this lane wants **8 dedicated physical cores (16 threads)**, e.g.
   10–15,26–31 after the D1 lane, plus ≥ 32 GB RAM. All numbers so far are on one Zen 5 core with SMT.
6. **An H200** for spike H1 (sustained efficiency). This is the largest sensitivity; ≥ 30 % of peak meets the
   target.

## Sources (cited, not reproduced)

* ZKsync Airbender: 21.8 MHz on one H100; SP1 Turbo 3.45 MHz; RISC Zero 1.1 MHz:
  <https://zksync.io/airbender>, <https://blockeden.xyz/blog/2026/01/30/zksync-airbender-fastest-risc-v-zkvm-ethereum-proving/>
* Arc, accumulation for Reed–Solomon codes: <https://eprint.iacr.org/2024/1731>
* WARP, linear-time accumulation: <https://eprint.iacr.org/2025/753>
* logUp: Haböck, eprint 2022/1530. LogUp-GKR: Papini and Haböck, eprint 2023/1284.
* STIR: eprint 2024/390. WHIR: eprint 2024/1586. FRI concrete security: eprint 2024/1161. BCIKS20 proximity gaps:
  eprint 2020/654.
* QROM: Chiesa–Manohar–Spooner, eprint 2019/834; Block–Garreta–Tiwari–Zając, eprint 2023/1256; Don–Fehr–Majenz,
  eprint 2020/282.
* H200/GH100 INT32 throughput: derived from public SM counts and clocks (132 SMs × 64 INT32 lanes × 1.98 GHz).
* SHA-512 GPU rate: hashcat RTX 4090 benchmark (recollection, ≈ 7.5 GH/s; study §11.3 flags the same figure as
  unverified).
