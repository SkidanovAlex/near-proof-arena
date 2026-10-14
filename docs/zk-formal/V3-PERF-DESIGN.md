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

## 0. Answers in one page

**Verdict.** The study's "thousands of H200s" for a worst-case 1 Pgas chunk was driven by three pessimistic
factors:
* 494–995 committed cells per WASM op;
* 2.0–3.8× recursion overhead from an arity-4 tree of segment proofs, each verified in-circuit with SHA-384;
* 0.5–2 G cells/s/GPU.

A design that removes those factors gives (**D/A**, `model.py`):

| 1 Pgas chunk (PQ, SHA-384, E = 10, proven-bound query counts) | 16 H200 | 32 H200 |
|---|---|---|
| typical (measured synthetic mix: 3.4 % WASM gas) | ≈ 2.0 s from execution start, ≈ 0.8 s after it ends | ≈ 1.9 s / 0.7 s |
| mainnet-like (**A**: 30 % WASM gas, memory-heavy mix) | ≈ 2.3 s / 1.1 s | ≈ 2.0 s / 0.8 s |
| **adversarial** (every gas unit spent on the costliest-to-prove op) | ≈ 4.4 s / 3.2 s | **≈ 3.1 s / 1.9 s** |
| final proof | ≈ 0.74 MB (FRI, Johnson regime at 2⁶, SHA-384) | same |

These hold at a sustained **35 % of peak H200 INT32 throughput (A)**. Measured from the end of execution, the
adversarial chunk needs:
* ≥ 33 % of peak on 32 H200 (≈ 7.8 G work-equivalent cells/s/GPU) to land ≤ 2 s after execution;
* ≥ 75 % (17.7 G/s/GPU) to land ≤ 1 s after execution;
* on 16 H200, 59 % (≤ 2 s) and 133 % (≤ 1 s, i.e. impossible).

**Plain answer.**
* Worst-case 1 Pgas in ≈ 2 s *after execution* (≈ 3 s from the start) on 32 H200 is **plausible but not
  certain**. It needs GPU kernels at roughly a third of peak.
* ≈ 1 s after execution needs ≈ 64 H200, or ≈ 75 % efficiency on 32. That is not plausible.
* ≈ 2 s *including* the ≈ 1.2 s native execution is not achievable on any GPU count. The execution floor plus the
  post-execution phases need ≈ 0.6 s even with infinite GPUs.
* Typical chunks are execution-bound: ≈ 0.7–1.1 s after execution ends.

The biggest uncertainty is GPU efficiency (sensitivity swing 2.0 s). Then come the extension degree E (0.9 s) and
the in-circuit SHA-384 cost (0.6 s). The chip widths themselves matter less.

**Architecture** (§1–§6):
1. **Execution.** A native run records checkpoints: per-segment register/stack/memory-page snapshots, host results
   and storage reads. Parallel re-execution of segments then emits chip rows. Main-trace commitment streams
   while execution continues.
2. **Register-form WASM machine.** A static per-contract translation (PREP) turns the stack code into 3-address
   rows:
   * `local.get`, `*.const` and `br` disappear;
   * `local.set/tee` retarget the producing row;
   * `i64.eqz; br_if` fuse into one row.

   The measured mix needs **0.29 rows per WASM op** (spike #1: 3.5 ops/row).
3. **Opcode-class chips** on shared buses, all costed in §2.4:
   * execution state `(pc, ts, fp, u)`;
   * instruction fetch from a per-contract code table;
   * offline memory checking with timestamps (single-lookup range check per access);
   * stack temporaries as write-once channels;
   * gas folded into fetched fees with one lazy check per call.

   Results: main cells ≈ 10 per op (measured mix), 20–40 (mainnet-like), ≤ 75 per row.
4. **Proof system.**
   * BabyBear with a **degree-10 extension** (PQ);
   * univariate STARK at **rate 1/2** with constraint degree ≤ 3, so the quotient domain equals the commitment
     domain;
   * **logUp** buses with 2 fractions per aux column, replacing per-interaction grand products;
   * one quotient per height;
   * SHA-384 Merkle trees whose leaves are row digests;
   * FRI.

   A multilinear backend (zerocheck + LogUp-GKR + WHIR/Basefold) cuts committed cells 4× but, at E = 10, **not
   prover work**. GKR fractions cost ≈ 3× committed-logUp fractions. It is not worth its Lean cost for the
   prover. Its value is proof size; §4.6 has the evaluation.
5. **Distribution instead of a recursion tree.**
   * The whole chunk is **one STARK** proved by all GPUs under a shared transcript: per-GPU tables, global buses,
     global Merkle trees over row digests.
   * There is no aggregation tree. A compression chain follows: L1 distributed, then L2/L3 and final on one node.
   * Recursion is ≈ 5–10 % of the work in the worst case (≈ 30–40 % for small typical chunks), against 100–280 %
     in the study.
6. **Work, not cells, is the metric.**
   * At E = 10 one bus fraction costs ≈ 7.9 k INT32 ops (committed logUp), ≈ 11 committed cells' worth.
   * Bus fractions are **55–75 % of all prover work**.
   * Hence the design minimises fractions per op (6–32 per row).
   * The real per-op figures are 73 (measured), 153 (mainnet-like) and 308 (adversarial) work-equivalent cells.
   * Committed cells per op are 43 / 91 / 168 (U-logUp) and 10 / 21 / 38 (multilinear).

**Host functions (§3).**
* NEAR's gas schedule tracks proving cost to within ≈ 3× for every host family examined. Storage, trie nodes,
  hashes and signatures are cheaper per gas than the worst WASM op.
* `read_register` copies (98,562 gas/B) and distinct-contract loading (1,089,295 gas/B) are on par with the worst
  WASM op, *given* a 16-byte bulk-copy chip and a bounded PREP.
* **P-RT-1** (a proving-weighted gas cap) **is no longer required** for a ≈ 3 s worst case on 32 H200. It is
  needed only to promise ≤ 1–2 s *after execution* on 16 H200. §3.3 gives a narrower PROPOSAL.

**Formal impact (§8).**
* What stays: field (L1), FS (L2), AIR DSL (L4), SHA-2 tables (L5), trie/receipt tables, the WASM semantics.
* What changes: L3 for logUp, the degree-10 extension, rate-1/2 quotient domains, row-digest leaves and
  multi-instance FRI.
* What is new: the register-form PREP simulation proof and per-chip views.
* Estimate ≈ 120–230 k Lean lines on top of D0a/D1. The judge budget needs P-RT-3 (parallel elaboration).

**Spike #1 (§9.2, measured on CPU).**
* Six chips (ALU reg-imm / reg-reg, MUL, BRZ, aligned LD/ST) plus memory boundary, code, range and byte-pair
  tables, run on the **existing** np-udr-stark-v2 prover.
* The register machine matches the reference interpreter on every program, and block-level gas units equal the
  executed op count.
* Per WASM op: measured-mix loop **10.6 main cells, 5.1 fractions** (3.50 ops/row); `i32.load` chain 21.3 / 11.9;
  store/load loop 9.3 / 4.3.
* The model reproduces these from the per-chip layouts to within the memory-boundary rows.
* Honest proofs verify: 83–104 M committed W_eq per proof, 16.5–17.8 s at today's parameters, ≈ 5–6 M W_eq/s on 2
  contended threads.
* Constraint and bus tampers are caught by the AIR checks, and 16 of 16 proof bit-flips are rejected by the
  verifier.
* CPU rate-1/2 LDE + SHA-384 Merkle: **27.5 ns per trace cell on one thread, 62 % of it hashing**.
* Extension cost E = 8 / 10 / 12: ×1 / ×1.4 / ×3.3 per multiplication.

**Decisions needed (§10).**
* P-PERF-1: register-form PREP.
* P-PERF-2: logUp instead of grand products.
* P-PERF-3: rate-1/2 inner layers with constraint degree 3.
* P-PERF-4: shared-transcript distributed proof (row-digest leaves, multi-instance FRI).
* P-PERF-5: stack-temp channel memory argument.
* P-PERF-6: the latency contract (after execution vs from start).
* P-PERF-7: hardware sizing (32 H200).
* P-RT-1': distinct-code cap.
* Core count for clean CPU measurements.

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

### 2.4 Per-class costs (v1 design; `model.py CHIPS_V1`; spike-built layouts in §9.2)

Committed cells use E = 10. "work cell-eq" includes the fraction work.

| class | WASM ops covered | m | f | committed U-logUp | U-GKR | ML | work cell-eq (U-logUp) |
|---|---|---:|---:|---:|---:|---:|---:|
| `alu_ri` (i64 add/sub, reg + imm) | add/sub + folded get/const/set | 32 | 13 | 132 | 52 | 32 | 213 |
| `alu_rr` | | 36 | 16 | 146 | 56 | 36 | 246 |
| `mul` (byte limbs) | i32/i64.mul | 49 | 32 | 239 | 69 | 49 | 439 |
| `divrem` | div/rem s/u | 75 | 45 | 335 | 95 | 75 | 617 |
| `bitwise` (byte-op table) | and/or/xor | 36 | 16 | 146 | 56 | 36 | 246 |
| `shift`/`rot` | | 40 | 18 | 160 | 60 | 40 | 273 |
| `clz`/`ctz`/`popcnt` | | 30 | 12 | 120 | 50 | 30 | 195 |
| `cmp` | lt/gt/le/ge/eq/ne | 28 | 12 | 118 | 48 | 28 | 193 |
| `brz` | eqz + br_if, br_if, if | 19 | 6 | 79 | 39 | 19 | 117 |
| `brcmp` | cmp + br_if fused | 30 | 12 | 120 | 50 | 30 | 195 |
| `conv` | wrap/extend | 18 | 8 | 88 | 38 | 18 | 138 |
| `global` | global.get/set | 16 | 7 | 86 | 36 | 16 | 130 |
| `select` | | 26 | 10 | 106 | 46 | 26 | 169 |
| `mov` | unfusable set/tee | 20 | 7 | 90 | 40 | 20 | 134 |
| `ld_al` (aligned i32) | | 20 | 12 | 110 | 40 | 20 | 185 |
| `ld_gen` (unaligned / sub-word / i64; two words + byte select) | | 37 | 19 | 167 | 57 | 37 | 286 |
| `st_gen` | | 40 | 22 | 180 | 60 | 40 | 318 |
| `callret` (call row + return row) | call / call_indirect + return | 35 | 20 | 165 | 55 | 35 | 290 |
| `memcpy16` (16 B per row) | memory.copy/fill, register↔memory | 60 | 24 | 210 | 80 | 60 | 360 |
| `prep_b` (contract preparation per code byte, excluding SHA) | | 30 | 2 | 70 | 50 | 30 | 83 |

All rows are **D** (layout counts). The spike builds the v0 versions of `alu_ri`, `alu_rr`, `mul`, `brz` and
`ld_al`, without channels and with 2-limb timestamp checks, and measures their exact widths and interactions
(§9.2).

### 2.5 Mix-weighted averages (per WASM op; `model.py`)

| mix | rows/op | main m | fractions f | committed: U-logUp / U-GKR / ML | work cell-eq (U-logUp / GKR / ML) |
|---|---:|---:|---:|---:|---:|
| measured synthetic (§1 of the study) | 0.30 | 10.8 | 5.2 | 43 / 16 / 10 | **73** / 103 / 98 |
| mainnet-like (**A**) | 0.63 | 21 | 10.4 | 91 / 33 / 21 | **153** / 217 / 207 |
| adversarial (max over candidates; §3.2) | 0.5–1.0 | 37.5 | 22.5 | 168 / 48 / 38 | **308** / 463 / 455 |

* Adversarial candidates per gas unit (work cell-eq, U-logUp): `local.get; i64.div_u` 308; `call` of an empty
  function 290; unaligned `i32.load` chain 286; `read_register` copies 188; distinct-contract loading 220;
  `i64.mul` 220; `popcnt` chain 195.
* They sit within ±15 % of each other. Gas prices WASM ops roughly in proportion to this design's costs, so no
  single op is a cliff.

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

### 3.2 Gas vs proving cost (D; costs from `spec/lean/v3/NearSpecV3/Wasm/Machine.lean`)

Cells are committed cells in the design. Work cell-eq ≈ 1.5–2× that for hash-heavy chips (few fractions). The
reference row is the worst WASM op: 168 committed / 308 cell-eq per 822,756 gas = **2.0·10⁻⁴ committed /
3.7·10⁻⁴ cell-eq per gas**.

| op | gas | proof cost (D) | committed cells/gas | vs worst WASM |
|---|---|---|---:|---|
| storage_write base (trie update, ≈ 8 node hashes) | 64.2 G | ≈ 100 SHA-256 blocks × 12 k = 1.2 M | 1.9e-5 | 10× cheaper |
| touching a trie node | 2.28 G | ≈ 8 blocks × 12 k = 96 k | 4.2e-5 | 5× |
| storage_read value byte | 5.61 M | ≈ 190 cells/B (SHA of the value) | 3.4e-5 | 6× (bounded by the witness size) |
| sha256 byte | 24.1 M | 190 | 7.9e-6 | 25× |
| keccak256 byte | 21.5 M | ≈ 735 (bit-level Keccak-f, 136 B per block; **A**) | 3.4e-5 | 6× |
| ed25519_verify | 210 G | ≈ 3.6 M (study §2.4) | 1.7e-5 | 12× |
| read_memory / write_memory byte | 3.8 / 2.7 M | ≈ 13 cells/B (`memcpy16`) | 3.5e-6 | 60× |
| **read_register byte** | **98,562** | ≈ 13 committed / 22 cell-eq per byte | 1.3e-4 | **≈ on par** |
| **contract loading byte** (`contract_loading_bytes`) | **1,089,295** | PREP ≥ 1 row/B (30 cells) + SHA-256 of the code (190/B) | 2.0e-4 | **on par** |
| memory.copy/fill byte (linear unit = regular) | 822,756 | 3.75 cells/B | 4.6e-6 | 40× |
| `memory.grow` per page | 822,756 | 0 until touched (lazy zero-init) | — | — |

**Cheap-gas / expensive-proof operations.** None found beyond the worst WASM op, *provided* three things hold:
1. **`read_register` copies use a wide bulk chip.** With byte-granular rows they would be ≈ 16× worse than the
   worst op. 1 Pgas of `read_register` into memory copies ≈ 10 GB.
2. **Contract preparation is bounded.** 1 Pgas of loads of distinct 4 MiB contracts is ≈ 0.92 GB of code
   (≈ 2·10¹¹ PREP cells): on par per gas but large in absolute terms. Cross-chunk deploy-time PREP removes it from
   the per-chunk proof (§3.3).
3. **Storage-read value bytes are bounded by the state-witness limit**, as D0a's A7 already is.

### 3.3 Is a proving-weighted gas bound (P-RT-1) still needed?

* **For a ≈ 3 s (from start) / ≈ 2 s (after execution) worst case on 32 H200: no.**
  * The worst case per gas is uniform within ≈ ±15 % across WASM ops, register copies and code loading.
  * So the latency bound follows from total gas, not from a weighted budget.
* **For ≤ 1 s after execution, or for 16 H200: yes.** Either a weighted budget (P-RT-1 as in the study) or a
  smaller worst-case gas class.
* **Narrow replacement, P-RT-1' (PROPOSAL, domain).**
  * Cap distinct contract-code bytes prepared per chunk (e.g. ≤ 16 MiB), or prove PREP at deploy time and bind
    each contract's code table as a *preprocessed commitment* in a cross-chunk registry (a relation change:
    the claim references the registry root).
  * Keep the witness-size bound (A7) for storage reads.
  * Everything else needs no cap.

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
* At rate 1/2, **UDR (proved in Lean today) and Johnson give the same query count**. The Johnson-regime Lean
  proof is not needed for the base layer, only for the final, size-setting layer.
* **Compression layers: rate 1/4. Final layer: rate 1/64, Johnson**, 87 queries ⇒ **≈ 0.74 MB** (SHA-384,
  arity-16 FRI, `model.py size_final`, which reuses `pqsize.py`'s formula). That is within U-9's 0.5–1 MB.
* STIR/WHIR (C: eprint 2024/390, 2024/1586) reduce the final layer to ≈ 0.3–0.5 MB (study §11.4). They matter only
  for the size-setting layer. They are a size lever, not a throughput lever.

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

| layer | proves | on | rate | queries | in-circuit cost (32 GPU, adversarial) |
|---|---|---|---|---|---|
| base | the chunk | N GPUs | 1/2 | 608 | — |
| L1 | verifier of base (each GPU verifies its own openings and FRI; global paths shared) | N GPUs, distributed the same way | 1/4 | 280 | q₀ × (3 paths × (25 − 9) + leaves Σcols/32 + N digest blocks + FRI) ≈ 0.6 M compressions ≈ 12 G cells: ≈ 0.1 s |
| L2 | verifier of L1 | one node (8 GPUs, NVLink, one logical prover) | 1/4 | 280 | ≈ 2–4 G cells: ≈ 0.15 s |
| L3 | verifier of L2 (fixed point ≈ 2²¹ rows × 400) | one node | 1/4 | 280 | ≈ 0.9 G: ≈ 0.05 s |
| final | verifier of L3 at rate 1/64, Johnson | one node | 1/64 | 87 | ≈ 0.9 G × 32/2: ≈ 0.2 s; **proof ≈ 0.74 MB** |

* Model totals: recursion ≈ 10 % of worst-case work; tail ≈ 0.5 s (`t_L1 + t_L2 + t_L3 + t_final`).
* Per in-circuit SHA-384 compression: 20 k cells (A: an optimised SHA-512-family AIR with 2 rounds per row and bit
  columns; the L5-style estimate is 25–40 k). Sensitivity: 15 k → 40 k moves latency 1.80 → 2.39 s.

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
L1 (all GPUs) → L2 (node) → L3 (node) → final (node) → proof
```

Worst case, 32 H200, 35 % efficiency (`model.py`): exec 1.20 s, phase A done during exec (0.15 s of work), phase B
1.31 s, tail 0.52 s ⇒ **3.10 s from start, 1.90 s after execution**.

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

Parameters and labels are printed by the script.

| scenario (1 Pgas) | backend | GPUs | WASM ops | committed cells/op | cell-eq/op | GPU-s | recursion share | latency from start / after exec | proof | GB/GPU |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| typical-measured | U-logUp | 16 | 4.1e7 | 43 | 73 | 8.6 | 40 % | 1.96 / 0.76 s | 740 KB | 53 |
| typical-measured | U-logUp | 32 | 4.1e7 | 43 | 73 | 8.6 | 43 % | 1.86 / 0.66 s | 740 KB | 26 |
| mainnet-like | U-logUp | 16 | 3.6e8 | 91 | 153 | 13.1 | 27 % | 2.29 / 1.09 s | 740 KB | 64 |
| mainnet-like | U-logUp | 32 | 3.6e8 | 91 | 153 | 13.1 | 29 % | 2.02 / 0.82 s | 740 KB | 32 |
| **adversarial** | U-logUp | 16 | 1.22e9 | 168 | 308 | 46.5 | 9 % | **4.44 / 3.24 s** | 740 KB | 161 |
| **adversarial** | U-logUp | 32 | 1.22e9 | 168 | 308 | 46.5 | 10 % | **3.10 / 1.90 s** | 740 KB | 80 |
| adversarial | U-GKR | 32 | 1.22e9 | 48 | 463 | 69.2 | 5 % | 3.77 / 2.57 s | 740 KB | 94 |
| adversarial | ML | 32 | 1.22e9 | 38 | 455 | 68.0 | 5 % | 3.73 / 2.53 s | 740 KB | 90 |

The typical and mainnet-like chunks spend most work on host functions (storage, promises) and the witness, not on
WASM (`host_celleq_per_gas` 6·10⁻⁵, **D/A**).

**What 1 Pgas worst case needs** (adversarial, U-logUp; `model.py required`):

| target | 16 H200 | 32 H200 |
|---|---|---|
| proof ≤ 2 s after execution (≈ 3.2 s from start) | 59 % of peak INT32 ≈ 14.0 G cell-eq/s/GPU | **33 % ≈ 7.8 G cell-eq/s/GPU** |
| proof ≤ 1 s after execution (≈ 2.2 s from start) | 133 %: impossible | 75 % ≈ 17.7 G cell-eq/s/GPU: not plausible |

At 308 cell-eq per op, 7.8 G cell-eq/s/GPU is ≈ 25 M worst-case WASM ops/s per GPU.

**Sensitivity** (adversarial, U-logUp, 32 H200, latency after execution; base 1.90 s):

| parameter | low → latency | high → latency | swing |
|---|---|---|---:|
| **GPU efficiency** (0.2 / 0.6) | 3.18 s | 1.19 s | **1.99 s** |
| **extension degree E** (8 / 12) | 1.50 s | 2.38 s | **0.87 s** |
| **in-circuit SHA-384 cells** (15 k / 40 k) | 1.80 s | 2.39 s | **0.58 s** |
| base rate (1/2 / 1/4) | 1.90 s | 2.33 s | 0.42 s |
| native SHA-512 cost (2,000 / 5,500 ops) | 1.83 s | 2.19 s | 0.36 s |
| NTT ops per cell (200 / 450) | 1.76 s | 2.10 s | 0.34 s |
| rbr bits (200 / 290) | 1.81 s | 1.97 s | 0.16 s |
| grinding, witness size, exec slowdown | | | ≤ 0.04 s |

The three dominant parameters are GPU efficiency, E and the in-circuit SHA-384 AIR. Chip widths enter through
cell-eq per op, which is linear: −20 % cell-eq ≈ −0.26 s.

---

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

**Total new (excluding research and recursion): ≈ 120–230 k lines.** Recursion adds 80–165 k, as in the study.

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

### 9.1 Plan (CPU now; H200 later)

| # | spike | measures | replaces assumption | status |
|---|---|---|---|---|
| **1** | hottest chips on the existing prover (`tools/perf-design/wasmchip`) | rows/op, m and f per class, honest/tamper self-check, CPU prove time, CPU commit throughput (SHA-384, rate 1/2) | chip widths (§2.4), constraints/cell, int ops per cell | **run, §9.2** |
| 2 | Fp10 arithmetic + logUp vs GKR fraction cost on CPU | ns per fraction at E = 10, both variants | `frac_ops` (4.4 k / 13 k) | next |
| 3 | optimised SHA-512-family AIR | cells per compression (target ≤ 20 k) | `sha384_cells` (third-largest sensitivity) | next (shared with D1-S) |
| 4 | v1 chips: stack-temp channels, single-lookup timestamps, `ld_gen`/`st_gen`, `callret`, `divrem` | m and f of the remaining classes | §2.4 D rows | after 1 |
| 5 | tracing interpreter speed vs native (wasmtime) on the corpora | ops/s/core for pass 2; checkpoint cost | 20 M ops/s/core | CPU |
| 6 | mainnet replay (study S1) | real mix, WASM gas share, distinct code bytes per chunk | `MIX_MAINNET`, `wasm_share_mainnet` | needs data access |
| 7 | judge parallel elaboration (study S7) | critical path at `-j 16` | P-RT-3 | CPU |
| H1 | H200: NTT, SHA-384 leaf hashing, Fp10, logUp kernels | sustained fraction of peak INT32 | `eff` (largest sensitivity) | needs an H200 |
| H2 | 2 nodes: digest all-to-all, phase B end to end | sync overheads, interconnect | `sync_s`, §6 | needs 2 nodes |

### 9.2 Spike #1 results (CPU; contended, indicative only)

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

### 9.3 What to measure on an H200 first

1. The phase-A fused kernel (coset DFT → SHA-384 leaf digest) in cells/s.
2. Phase-B fraction throughput at E = 10 (fingerprint, batched inverse, helper column).
3. End-to-end `eff` on one slice of 2²⁴ rows × 150 columns.

These three numbers decide whether 32 H200 meet ≤ 2 s after execution.

---

## 10. Decisions needed (all PROPOSALS)

1. **P-PERF-1 (relation-neutral, PREP design).** The register-form translation as the WASM AIR's execution model,
   proved by a simulation lemma against `NearSpecV3.Wasm`.
2. **P-PERF-2 (protocol).** logUp buses with base-field multiplicities replace per-interaction grand products for
   new (D3/PQ) AIRs. D0a/D1a stay on today's protocol.
3. **P-PERF-3 (protocol parameters).** Rate-1/2 inner layers, constraint degree ≤ 3, one quotient per height.
   Final layer at rate 1/64 in the Johnson regime.
4. **P-PERF-4 (protocol/format).** A shared-transcript distributed base proof with two-level (row-digest) leaves
   and per-GPU FRI instances, followed by a 3-layer compression chain.
5. **P-PERF-5 (AIR).** A stack-temporary channel memory argument (needs its Lean lemma before use; spike 4 tests
   it adversarially).
6. **P-PERF-6 (latency contract).** State real-time targets *after execution ends*: the native run of a 1 Pgas
   chunk is ≈ 1–1.2 s and is a floor. Proposed:
   * worst case ≤ 2 s after execution on 32 H200;
   * typical ≤ 1 s after execution on 16 H200.
7. **P-PERF-7 (hardware).** 4 × 8 H200 for the worst-case class; 2 × 8 for typical-only. GPU judge worker as in the
   study's P-RT-4.
8. **P-RT-1' (domain).** Drop the general weighted gas bound. Instead cap distinct prepared code bytes per chunk,
   or adopt deploy-time PREP with a code-table registry. Keep the witness-size bound.
9. **Extension degree.** Ask research M3 for the minimum E with explicit constants; every unit of E is worth
   ≈ 0.2 s of worst-case latency.
10. **CPU allocation.** For clean CPU measurements (spikes 1, 2, 4, 5) this lane wants **8 dedicated physical
    cores (16 threads)**, e.g. 10–15,26–31 after the D1 lane, plus ≥ 32 GB RAM. At least 4 cores for prover
    end-to-end runs at 2²⁰ rows.

---

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
