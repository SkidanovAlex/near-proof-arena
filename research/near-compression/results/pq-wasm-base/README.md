# pq-wasm-base: first slice of the post-quantum direct-Wasm base-layer prover

Lane `lane/pq-wasm-base` (branched from `lane/pq-base-aggregation` @ 364aa29b3), 2026-10-18/19.

This is the narrow first slice agreed for the checkpoint: one instruction family, end to end, on the
pinned base envelope of `../pq-base-aggregation/DESIGN-BASE.md` §3. It is the template for the full
instruction set. Nothing here touches signed challenges, `oracle/v3` or pinned files.

| piece | where |
|---|---|
| Lean AIR model (single source of truth), checker, proofs | `research/near-compression/wasm-base-lean/` (package `WasmBase`, imports only `NearSpecV3.Wasm` and `ZkFormal.Algebra.Fp`) |
| Rust prover/verifier (interprets the Lean-exported AIR) | `research/near-compression/native/wasm-base/` |
| test programs, Python reference interpreter | `native/wasm-base/programs/` |
| logs of the runs quoted below | `logs/` |

## 1. Status at a glance

* **AIRs**: 12 AIRs (limit 32), max degree 8 (limit 8), every interaction weight 1, messages ≤ 8 fields.
  Proved and verified with the native SWIRL verifier at the seg-v1 shape (42-byte digests, T\*,
  coset leaves, z = 24, c = 1, b = 1, m = 16, k₁ = 1, k = 4, keep-domain, WHIR-Y, multiproof,
  268-bit target; soundness calculator 268.2 bits). No preprocessed or cached traces, one common-main
  commitment, every trace ≥ 4 rows: the shape NV can verify today.
* **Lean ↔ Rust**: generated, not hand-copied. The Lean value `WasmBase.wasmBaseAir` is exported as
  JSON and the Rust `Air::eval` replays it through the openvm `AirBuilder`/`InteractionBuilder`
  (`src/air.rs`). Independently, `difftest.py` evaluates the Lean expressions (in Lean) and the
  verifying key's symbolic DAG (in Rust) at random points. On the fixed AIR: 384 points, 7,296
  constraint values and 6,336 interactions (bus, signed count, message) agree (`logs/difftest.log`).
* **Tests**: 47 known-answer programs (Python reference = Lean spec = Rust trace generator + full
  constraint/bus check), real proofs of 5 programs, 29/29 tamper cases rejected by the native verifier. All re-run after the SHIFT fix
  (`logs/kat.log`, `logs/tamper-hashloop8.log`).
* **Lean base-faithful: proved end to end.** `WasmBase.wasm_base_sound` (`WasmBase/Main/Final.lean`):
  `check` accepts the function ∧ `Holds (wasmBaseAir nloc ncode) pub tr` (the relation the SWIRL PIOP
  enforces, mod-p LogUp balance) ∧ the public inputs are the checker's (`PubOK`) ∧ explicit,
  decidable statement conditions ⇒ from function entry the spec `NearSpecV3.Wasm.run` finishes after
  exactly `N − 1` steps, having charged `R · S` gas, with the operand stack equal to the public result.
  No `sorry`, no new axioms (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`), §5.
* **A soundness bug found by the proof, fixed.** v1 of SHIFT range-checked `w·q` instead of `q`. `q`
  is a free column, so `w·q` can hit any small residue mod p and `b0 = k + w·q` stopped pinning
  `k = b0 mod w`. Example: `b0 = 5`, claimed count `k = 3`, `q = 2·32⁻¹ = 1887436801`, and then
  `w·q mod p = 2` passes the check. Fix: `r16(q)`. Column and interaction counts are unchanged, so
  every cost figure below holds. All tests, proofs and the pinned run were redone after the fix.
* **Cost** (§6): 28.5 committed cells and 12.6 LogUp fractions per executed op (active rows, mixed
  hash-loop workload, 38k steps) ⇒ **349 work cell-eq/op at E = 12** (529 with power-of-two padding).
  Per-op worst chips: SHIFT 886, MUL 799 cell-eq at E = 12, against the 546 model; univariate
  estimates 520 / 411.

## 2. The family and why locals are in it

Family F1: `i32/i64.{add, sub, mul, and, or, xor, shl, shr_s, shr_u, rotl, rotr}`,
`i32/i64.{eqz, eq, ne, lt/gt/le/ge _s/_u}`, `i32/i64.const`, `drop`, `select`, `block`, `loop`,
`end`, `br`, `br_if`, `return`.

`local.get/set/tee` were added. Without them a loop cannot carry state between iterations (a Wasm
block cannot consume operands from outside it), so the requested "loop computing over i32/i64 for a few
thousand steps" is not expressible. Locals reuse the operand-stack channel (space 1), so they add one
chip and no new argument.

Semantics are **not** re-invented: the target relation is the D3α spec itself,
`NearSpecV3.Wasm.step` / `run` (`spec/lean/v3/NearSpecV3/Wasm/Exec.lean`, difftested three ways
against nearcore), including the NEAR gas charge at finite-wasm instrumentation points.

### Domain conditions (explicit, decidable: `WasmBase.check`)

* **D1 family**: no params; ≤ 64 locals (i32/i64); ≤ 1 result (i32/i64); every instruction in F1
  (+ locals, index in range).
* **D2 gas**: every gas entry is absent or a constant fee `fee.c = units · regular_op_cost`,
  `units < 2^16` (no linear fees in F1).
* **D3 no-discard branches**: at every `br`/taken `br_if` to an inner label, the static height equals
  `label.height + label.arity`; at every exit of the function it equals the result arity. Branches
  then never drop operands, so the channel needs no "kill" rows. (Compiled code that discards on a
  branch is outside this slice; lifting D3 needs a kill row or an orphan sink — §8.)
* **D4 dead code**: after an unconditional transfer the next instruction is `end`.
* **D5 sizes**: code < 2^20 instructions, static heights < 2^16.
* Statement-level (checked by the verifier on public values): `2 ≤ N`, `N · (maxFee + 1)` bounded
  (no wrap of the gas-units accumulator), `R · S_final ≤ g0`, `g0 < 2^64`, trace heights ≤ 2^24.

The checker computes the static label stack `L pc` and height `H pc` (`analyze`) and re-verifies every
local transition (`verifyAt`); proofs use only `verifyAt` (`check_sound`, proved).

## 3. Design

### 3.1 Buses (all global; design G)

| bus | message | producers / consumers |
|---|---|---|
| 0 STATE | `[pc, ts, S, halted]` | each instruction row receives its input state and sends its output state; BOUNDARY sends `(0, 1, 0, 0)` and receives `(pc_f, N, S_final, 1)` |
| 1 FETCH | `[pc, op, h, fee, x0..x3]` | instruction rows query; BOUNDARY answers with the public code records (count `first · mult_j`) |
| 2 CH | `[space, slot, tag, v0..v3, tp]` | value channel: operand stack (space 0, slot = static height index) and locals (space 1); producer sends with `tp = ts`, consumer receives and range-checks `ts - tp - 1` |
| 3 R16 | `[v]` | 16-bit range lookups into RANGE16 |
| 4 BYTE | `[kind, x, y, z]` | byte-pair range (0), and (1), or (2), xor (3) into BYTE |

Values are four 16-bit limbs (i32: two, uppers 0) plus a type tag; MUL, BIT and SHIFT work on bytes.
`S` counts gas in `regular_op_cost` units; the verifier checks `R · S_final ≤ g0` once (lazy gas,
PERF §2.3): gas is monotone, so no per-charge-point comparison is needed. `h` (the static operand-stack
height at `pc`) comes from the code record, so the state carries no stack pointer.

**Design G fit.** One shared-transcript proof: every cross-row dependency is a bus term. A GPU slice
of a table is just a range of rows; state continuity (STATE), operand/locals continuity (CH) and code
fetch are global multiset equalities, so slices need no boundary digests or per-segment statements.
The only per-slice caveat is the channel time check: `ts` is a global row clock here (≤ 2^30), which
is fine inside one proof; PERF's per-slice `(slice, t)` time is not needed for this design.

### 3.2 AIR list (`wasmBaseAir nloc ncode`, `WasmBase/Chips.lean`)

m = columns, f = interactions per row (LogUp fractions), deg = max constraint/interaction degree.

| # | AIR | ops | m | f | constraints | deg | notes |
|---|---|---|---:|---:|---:|---:|---|
| 0 | BOUNDARY | init/final state, final stack, locals in/out, code records | 2 + 6·nloc + ncode | 3 + 2·nloc + ncode | 0 | 2 | height 4; public-value messages |
| 1 | ADD | add, sub | 28 | 14 | 20 | 3 | 16-bit limbs, carry bits |
| 2 | BIT | and, or, xor | 37 | 18 | 19 | 2 | 8 BYTE lookups |
| 3 | MUL | mul | 43 | 30 | 26 | 3 | byte schoolbook, carries in RANGE16 |
| 4 | SHIFT | shl, shr_s, shr_u, rotl, rotr | 80 | 32 | 69 | 8 | `P = A·2^e mod 2^(2w)`, halves selected |
| 5 | CMP | eqz, eq, ne, lt/gt/le/ge s/u | 42 | 16 | 38 | 5 | borrow chain on msb-flipped operands, inverse zero test |
| 6 | CONST | i32/i64.const | 11 | 4 | 4 | 2 | immediate from the code record |
| 7 | STACK | drop, select | 28 | 13 | 13 | 3 | |
| 8 | CTRL | block, loop, end, br, br_if, return | 16 | 6 | 7 | 4 | labels static; no stack traffic except the `br_if` condition |
| 9 | LOCAL | local.get/set/tee | 23 | 11 | 10 | 2 | locals = channel space 1 |
| 10 | RANGE16 | — | 2 | 1 | 3 | 2 | committed, derived (`v = row`, height exactly 2^16) |
| 11 | BYTE | — | 20 | 4 | 19 | 2 | committed, derived from 16 bit columns, height 2^16 |

Keygen confirms the degrees and counts (`logs/prove-*.log`, `VK` lines).

### 3.3 No preprocessed or cached tables — and what a preprocessed version would change

| table | now (committed/derived/public) | with preprocessed tables |
|---|---|---|
| code (FETCH) | BOUNDARY row 0 has one interaction per code record whose message is public values; `ncode` multiplicity columns; `3 + 2 nloc + ncode` interactions on every BOUNDARY row (63 for a 54-instruction program). Does not scale beyond small programs: every record is a GKR leaf and a vk-changing AIR. | a per-contract preprocessed CODE table (vk-bound, or bound to the PREP side proof at L1 as DESIGN-BASE §2.2 proposes) with one multiplicity column; the BOUNDARY interactions disappear. Needs NV to verify a preprocessed child (lane/pq-e2e-slice). |
| RANGE16 | committed `v` column constrained `v_0 = 0, v_{r+1} = v_r + 1, v_last = 65535` + multiplicity | preprocessed `v`; only the multiplicity column committed (−1 column, −3 constraints) |
| BYTE | 16 committed bit columns, x, y and the and/or/xor results derived (degree 2), counter constraint | preprocessed (x, y, and, or, xor); 4 multiplicity columns only: 20 → 4 committed columns per 2^16 rows, −19 constraints |
| channel time check | two R16 lookups per consumed value (`lo`, `4·hi`) | one lookup in a preprocessed 2^24 RANGE-T table (PERF §2.3): −1 fraction per consumed value |

The fixed cost of the committed derived tables is 1.44 M cells (RANGE16 131 k + BYTE 1.31 M) per
proof; at 1 Pgas it is amortised away, but the per-op lookup traffic stays.

## 4. Tests

* **KAT** (`run_kat.sh`, 47 programs): one per binop/relop/eqz and width (24 random edge-value pairs
  each: 0, 1, ±2^(w−1), 2^w−1, shift counts w−1, w, w+1, 2w+3, random), `ctrl` (nested blocks with
  results, taken/untaken `br_if`, loop, select, drop, return from a nested block), hash loops (8 and 64
  iterations). Each: the Python reference (`programs/refinterp.py`, written from the Wasm spec), the
  Lean spec run (`wasmbase-tool prep`: real `prepare`, `check`, then `NearSpecV3.Wasm.step` from the
  post-`enter` state) and the Rust trace generator agree on value and step count, and the full
  constraint + bus pre-check passes. 47/47. Shift counts are masked (`b mod w`) and i32 ops wrap in
  all three; the family has no traps other than gas exhaustion, which is outside the proved domain
  (the prover refuses, §8).
* **Difftest** (`difftest.py`): Lean model vs Rust verifying key, see §1.
* **Tamper** (`nearproof-wasm-base tamper`, `logs/` via the run in this lane): 29 cases on `hashloop8`,
  each re-proved and checked by the native verifier: result/carry/borrow/inverse/limb/time/height/fee/
  gas cells of every chip, the code-table multiplicity, RANGE16/BYTE table cells, public N/S/result/
  record fields, swapped timestamps. **29/29 rejected.** (Two earlier "accepted" cases were free
  witnesses — the inverse of a zero condition — which do not change the statement; they were replaced
  by condition and value tampers.)
* **Real proofs** verified by the native SWIRL verifier: hashloop 16/64/256/1024 iterations
  (619 – 38,409 steps), `ctrl`, at the small shape; hashloop64 at the pinned 2^24 shape.

## 5. Lean: theorems and status

All modules are in `research/near-compression/wasm-base-lean/WasmBase/`. The package builds with no
`sorry` anywhere (139 jobs), and the axioms are only `propext`, `Classical.choice` and `Quot.sound`.
The Lean AIR is the one the prover uses: it is generated (JSON export, replayed by `src/air.rs`) and
also difftested (§1).

| module | statement | status |
|---|---|---|
| `Air` | `Holds A pub tr`: heights 4 ≤ h ≤ 2^24, every constraint on every row, **mod-p** bus balance for every message, the verifier's per-bus bound `busLoad < p` | definition (PIOP relation) |
| `Chips` | the 12 AIRs | definition (exported, interpreted by Rust) |
| `CheckFacts.check_sound` | `check … = some ck →` labels, heights, every `verifyAt`, records = `recordOf`, fees, types | proved |
| `Local.*_sound` (ADD, BIT, MUL, CMP, SHIFT, CONST/STACK/CTRL/LOCAL) | one row satisfying its constraints, plus the range facts its lookups give, ⇒ the produced value is the spec op (`Num.binop`/`relop`/…) of the consumed values | proved; SHIFT is hand-written and generic in the byte length (`ShiftBytes.chain_prod`, `byte_disjoint` for rotations) |
| `Step*`, `StepCtrl` | under the simulation relation `RelW`, each instruction class's `step` gives `.cont s'` with the relation at `t+1`, or `.fin` | proved |
| `Bus.lookup_sound`, `Bus.msgs_perm` | lookups and exact permutations from mod-p balance and bit counts | proved |
| `Chain.chain`, `Channel.ChanOK.*` | STATE ⇒ one path; channel soundness (P-PERF-5) | proved |
| `Main.Abstract.exec_of_rows` | per-row `RowFacts` + the two permutations ⇒ `run` finishes with the boundary's gas, stack and locals | proved |
| `Main.Lookups.looks_of` | FETCH query = a public record, R16 < 2^16, BYTE = `byteF` on bytes (the RANGE16/BYTE tables are exactly their intended contents) | proved |
| `Main.Row*` (9 chips) | an active row's constraints and lookups ⇒ `RowFacts` (spec step, timestamps, gas, channel times); count bits; inactive rows silent | proved |
| `Main.Exec` | the trace's STATE/CH messages = boundary + active rows; `wasm_base_exec` | proved |
| **`Main.Final.wasm_base_sound`** | the end-to-end theorem (§1) | **proved** |

Explicit domain conditions in the theorem: `check` (D1–D5); the publics are those derived from the
checker output (`PubOK`); `N · (maxFee + 1) < p`; `R · S ≤ g0`; `g0 < 2^64`; entry state with an
empty operand stack, zeroed locals and gas `g0`. The theorem is stated for `run` from the
post-`enter` state. The glue to `runCall` (prepare, link, instantiate, enter) exists for the older
families in `NearCompression.Prepared*` and is not repeated here.

## 6. Measurements (CPU, current SWIRL backend)

The z = 24 rows were re-run after the SHIFT fix (2026-10-19), so the timings reflect current host load. The z = 0 rows are from the pre-fix AIR, which has identical shape and costs. Host shared with other runs; 8 threads pinned to CPUs 8–15, nice 10,
`HEAVY_MEM=20G`. Prover: `Sha384RefEngine` (column-major CPU backend).

**Workload**: `hashloop<n>` (FNV-1a-style i64 mul/xor, rotl/shr_u, i32 shl/shr_s/xor/add, compare,
conditional block, select; ≈ 37.5 ops per iteration).

| run | steps | shape | proof bytes | prove (s) | verify (s) | peak RSS |
|---|---:|---|---:|---:|---:|---:|
| hashloop16, z = 24 | 619 | n_stack 18 (2^20) | 746,092 | 22.6 † | 0.016 | 0.80 GB |
| hashloop64, z = 24 | 2,444 | n_stack 18 | 747,310 | 23.0 | 0.016 | 0.80 GB |
| hashloop256, z = 24 | 9,614 | n_stack 18 | 745,798 | 21.4 | 0.016 | 0.83 GB |
| hashloop64, z = 24 | 2,444 | **pinned n_stack 22 (2^24)** | 948,706 | 239.9 | 0.019 | 9.9 GB |
| ctrl, z = 24 | 170 | n_stack 18 | 747,366 | 25.8 | 0.028 | 0.79 GB |
| hashloop64, z = 0 (work only) | 2,444 | n_stack 18 | 803,340 | 25.6 / 25.6 | 0.023 | 0.83 GB |
| hashloop256, z = 0 | 9,614 | n_stack 18 | 804,894 | 25.5 / 25.6 | 0.028 | 0.85 GB |
| hashloop1024, z = 0 | 38,409 | n_stack 18 | 817,376 | 32.2 / 31.6 | 0.034 | 1.25 GB |

† includes the 2^24-hash query-phase grinding (z = 24), whose time is random and dominates small
proofs; the z = 0 rows measure prover work (they need more queries, hence larger proofs).
Base proofs are not sent to V_d: their size only drives the NV cost of L1 (queries [536, 256, 83, 50]
at 2^20; [536, 256, 83, 50, 36] at 2^24).

**Per op** (`analyze.py`, marginal between 9,614 and 38,409 steps, z = 0 logs):

| | committed cells/op | fractions/op | work cell-eq/op E = 10 | E = 12 |
|---|---:|---:|---:|---:|
| active rows | 28.5 | 12.6 | 265 | **349** |
| power-of-two padded heights | 44.4 | 19.0 | 402 | 529 |

Formula (PERF §2.1, `tools/perf-design/model.py` ML/SWIRL backend, rate 1/2): cell-eq/row =
m + f·(42E + 28X)/C + 6X/C with X = 4.5E², C = 745.3 at E = 12 (25.0 per fraction, 5.2 per row).
Measured CPU marginal: (32.2 − 25.6) s / 28,795 ops ≈ 0.23 ms/op on 8 busy threads; prove time at
these sizes is dominated by the fixed stacked area (2^20 × 8 columns) and the 1.44 M-cell RANGE16/BYTE
tables.

**Against the models.** The 546 figure is PERF's draft adversarial op (div/rem) at E = 10 × 1.2; the
281 univariate figure is the measured unaligned load chain. Neither op is in F1. Same-kind chips:

| chip (1 row/op) | m | f | deg | SWIRL E = 12 | ML E = 10 | univariate E = 10 (est.) | PERF layout |
|---|---:|---:|---:|---:|---:|---:|---|
| ADD | 28 | 14 | 3 | 384 | 291 | 216 | alu_rr 34/16 (M) |
| BIT | 37 | 18 | 2 | 493 | 374 | 260 | bitwise 36/16 (D) |
| MUL | 43 | 30 | 3 | 799 | 601 | 411 | mul 44/30 (M) |
| SHIFT | 80 | 32 | 8 | **886** | 675 | 520 | shift 40/18 (D) |
| CMP | 42 | 16 | 5 | 448 | 342 | 272 | cmp 28/12 (D) |
| LOCAL | 23 | 11 | 2 | 303 | 230 | 172 | (register form: 0 rows) |
| CONST | 11 | 4 | 2 | 116 | 89 | 76 | (register form: 0 rows) |

Univariate estimate: committed = m + E(⌈f/2⌉ + 1) + E(deg − 1), work = committed + f·4410/C(E=10).
ADD and MUL land where PERF's measured layouts are; SHIFT and CMP are ≈ 2× PERF's drafts (degree-8
product construction, two-lookup time checks) and are the first optimisation targets. A sustained
adversarial stream cannot be all shifts (each pops two values and pushes one; producers cost 116–303),
so the realistic worst case per gas unit is ≈ 500–600 cell-eq at E = 12, about the 546 model, and
SHIFT/MUL rows alone are 1.5× it. The univariate alternative is ≈ 1.6–1.7× cheaper per op for this
family (e.g. MUL 799 → 411), consistent with 546 → 281 in DESIGN-BASE R1, but needs its own level-1
verifier circuit.

## 7. Checkpoint: open questions and the evidence produced

1. **Preprocessed tables.** Evidence: §3.3. The slice works without them and NV-verifiable as is, but
   (a) the code table is bound through public-value interactions that grow with the program (63
   interactions on BOUNDARY for 54 instructions; vk changes per program) — not viable for real
   contracts; (b) BYTE/RANGE16 cost 1.44 M committed cells per proof; (c) a 2^24 RANGE-T would remove
   one lookup per consumed value. **Recommendation:** preprocessed CODE (or PREP-linked main table at
   L1) is required before the full instruction set; BYTE/RANGE preprocessing is a cost lever only.
2. **Base backend (SWIRL Ext12 vs univariate).** Evidence: §6 per-chip table and the measured
   per-op mix (349 cell-eq/op active at E = 12 for the mixed loop; 886 for SHIFT). LogUp fractions
   are 70–90 % of the work at E = 12; the univariate estimate is 1.6–1.7× lower per op. The AIRs are
   backend-agnostic (written once in Lean, replayed through `AirBuilder`), so switching keeps them;
   SHIFT's degree 8 would cost quotient chunks on a univariate backend (recommend lowering it first).
3. **Memory / stack design.** Evidence: the channel design (operand stack and locals as producer →
   consumer channel, P-PERF-5) is implemented, measured (CH traffic is 3–5 fractions per binop incl.
   time checks) and **proved sound in Lean** (`Channel.lean`) under the no-discard domain condition
   D3; locals reuse it. Open for the decision: (a) D3 must be lifted for compiled code (kill rows or an
   orphan sink with a soundness argument); (b) linear memory needs offline memory checking with
   read-back (the channel does not fit long-lived random-access memory); (c) the time check should
   become a single RANGE-T lookup (needs a preprocessed 2^24 table, question 1).

## 8. Limits and next steps

* Gas exhaustion (the only trap of F1) is not provable: the AIR has no out-of-gas row; the verifier
  check `R · S ≤ g0` rejects such statements and the prover refuses. Adding an OOG terminal row is
  local.
* Register-form translation (PERF P-PERF-1: const/local/drop/br vanish) is not used; this slice
  executes one row per Wasm instruction, which is what the base-faithful proof follows directly.
* Lean: the base-faithful theorem is complete for this family. Extending to the full instruction set
  reuses `exec_of_rows`, `looks_of` and the `Main.Rows` infrastructure; each new chip needs a local
  soundness lemma and a `*_rowfacts` lemma.
