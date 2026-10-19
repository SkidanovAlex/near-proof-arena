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
| 0 STATE | `[pc, ts, S, halted, sb, cid]` | each instruction row receives its input state and sends its output state; BOUNDARY sends `(0, 1, 0, 0, 0, 0)` and receives `(pc_f, N, S_final, status, sb_f, cid_f)` (frame fields since refactor R, §10) |
| 1 FETCH | `[pc, op, h, fee, x0..x3]` | instruction rows query; BOUNDARY answers with the public code records (count `first · mult_j`) |
| 2 CH | `[space, slot, tag, v0..v3, tp]` | value channel: operand stack (space 0, slot = `sb + h − k`) and the locals of activation `cid` (space `16 + cid`); producer sends with `tp = ts`, consumer receives and range-checks `ts - tp - 1` |
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

(Widths as of v1. Since refactor R (§10) every instruction chip has two more columns `fr_sb, fr_cid`,
LOCAL also `inv_sp`, BOUNDARY `sbf, cidf`; CTRL and LOCAL have one more constraint each.)

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
| 9 | LOCAL | local.get/set/tee | 23 | 11 | 10 | 2 | locals = channel space 1 (since R: space `16 + cid`, +3 columns, +1 constraint) |
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

## 9. After the checkpoint (2026-10-19): decisions applied

The coordinator decided (a) to make CODE a cached table bound through the statement, (b) to keep
BYTE/RANGE16 committed, (c) to stay on SWIRL Ext12, and (d) to fan out the next instruction families.
`lane/pq-nv-preprocessed` @ 9761585a5 (which includes the G1 fix, `lane/pq-recursion-sha384` @ 717eb518e)
is merged.

### 9.1 (a) CODE cached, bound through the statement (`wasm-base-v2`)

See `STATEMENT.md`.
* The code records live in a cached CODE trace, and its commitment `code_root` is a statement
  component that V_d recomputes from the contract code. The vk no longer depends on the program,
  only on `nloc`.
* Lean: one new hypothesis `CodeOK` (the binding V_d's check provides). The FETCH soundness
  (`looks_of`) is re-proven from it.
* Tamper: a forged CODE row that no instruction fetches passes the AIR and the native verifier; only
  the `code_root` check rejects it.
* The base proof grows to 970–976 KB (small shape) and 1,263 KB (pinned 2^24 shape). Base proofs are
  not sent to V_d.

### 9.2 Family 1: i32/i64 `div_s`, `div_u`, `rem_s`, `rem_u`, with traps

**AIR.**
* DIV chip (table 10): 95 columns, 106 constraints, 45 interactions, degree 6.
* Magnitudes come from negation chains: `A + a ∈ {0, 2^w}` for signed operands. The byte product is
  `Q·B + R = A`, with the high convolution sums and the top carry forced to zero and the carries
  range-checked. `R < B` comes from a borrow chain.
* The result is `±Q` or `±R`, built by a negation chain with the result sign.
* Traps: `tz = [B = 0]` (an inverse test; the division is enforced only when `tz = 0`), and
  `tov = div_s · sign(a) · sign(b) · topbit(Q)`. For `div_s`, `Q ≤ 2^(w−1)` holds, with equality
  exactly when `a = MIN` and `|b| = 1`, so `tov` is exact.
* A trapping row ends the execution with `halted = 2`.
* There is a new public `status` (1 = return, 2 = trap). After a trap the result is not received, and a
  DRAIN table (table 14) consumes the leftover operand-stack messages, with count `act·(status − 1)`.

**A soundness hole found by the proof attempt, before any proof existed.** The product carries were
not range-checked, so the chain held only mod p. Example: `5 / 1` with `Q = 5 + p` passed every
constraint. Fix: 8 R16 lookups on the carries.

**Lean** (no `sorry`, standard axioms):
* `Local.Div.div_sound`: the row semantics, including the exact trap characterisation.
* `StepOps.step_binop_trap`: a trapping binop gives `.abort` with the fee charged.
* `Main.RowDiv`: `div_counts`, `div_inactive` and `div_rowfacts` (`RowFacts2`, a third outcome `hb = 2`).
* `Main.Abstract.exec_of_rows` handles the trap outcome.
* `Main.Final.wasm_base_sound`: with status 1 the run returns with the public result; with status 2
  it ends in `.abort` after `N − 1` steps with `R·S` gas charged.

**Tests.**
* KAT 63/63 (`logs/kat.log`): 8 div/rem programs × 30 operand pairs, including MIN/−1 for `rem_s` and
  `div_s` at MIN/1; 6 trap programs (division by zero for `div_u`/`rem_s`, `div_s` overflow,
  i32/i64), each with a value left on the stack to exercise DRAIN; plus all the earlier programs.
* Difftest: 480 points, 10,720 constraint values and 6,560 interactions agree.
* Tamper: 31/31 on hashloop8, 28/28 on `kat_i64_div_s` and 25/25 on `trap_i32_zero_u`. On a trap, the
  result public value is deliberately not a statement component.

**Cost** (`logs/prove-divloop*-small-z0.log`, marginal between 9,994 and 39,946 steps, about 15% of
ops are div/rem):

| | committed cells/op | fractions/op | cell-eq/op at E = 12 |
|---|---:|---:|---:|
| mixed div loop, active rows | 33.2 | 15.7 | **430** |
| mixed div loop, padded heights | 44.1 | 20.7 | 568 |

A DIV row alone (an adversarial div-only stream) costs **1,226 cell-eq at E = 12**, 2.2× the 546
model; the univariate estimate is 667. This is the costliest chip. The levers:
* The 45 fractions break down as 16 BYTE byte-pair checks (A, B, Q, R), 8 carry checks, 4 D, 4
  result, 3 pinning and 2×2 time checks.
* Halving the byte checks by checking A and Q only is possible if B and R are derived. Packing
  carries with a 2^12-wide lookup needs preprocessing, ruled out by (b).
* An i32-only DIV variant (half the bytes) and dropping the explicit `A` bytes (reconstructing them
  from limbs and range-checking only Q, R and B) are the next optimisation candidates. They are
  queued with the SHIFT/CMP work.

### 9.3 Not done yet (this lane, in the coordinator's order)

* Family 2 (linear memory with offline memory checking, lifting D3), family 3 (globals; locals are
  done) and family 4 (calls with a call stack) all need the simulation relation `RelW` to grow:
  * memory pages for family 2;
  * a globals view for family 3;
  * more than one frame for family 4.

  So they start with a refactor of `Event.RelW` and the generic step lemmas, after which the
  per-chip row lemmas carry over.
* SHIFT/CMP (and now DIV) optimisation.

Update: refactor R is done (§10.1), and families 2 (§11), 3 (§12) and 4 (§13.1) are done. The
DIV/SHIFT/CMP optimisation is next.


## 10. Design note: the simulation relation for families 2–4 (refactor R)

This note was written before the refactor so that another agent can continue it. The current
relation is `Event.RelW X s f tps tpl t pc S live`. It covers one frame (`s.frames = [f]`, base 0),
the operand stack, and one frame's locals: `live ↔ stackView ∨ localView`. Families 2–4 need memory,
globals and a call stack. The plan is to replace it once with **`RelV`**: same idea, more views. The
per-chip row lemmas only use the relation through a small API (`stack_dec`, `local_msg`, the
straight-line/control step lemmas), and that API keeps its shape.

**State message.** `[pc, ts, S, halted, sb, cid]`.
* `pc` is a *global* pc. All functions' code is concatenated, the CODE records are keyed by global pc,
  and branch and call targets in the records are global.
* `sb` is the current frame's stack base.
* `cid` is the current activation id: the `ts` of the call row, or 0 for the entry frame.
* Every chip's STATE in/out gets the two extra fields, with in = out except for calls and returns.

**Channel spaces** (all on bus CH, message `[space, slot, tag, v0..v3, tp]`):

| space | contents | slot | written by |
|---|---|---|---|
| 0 | operand stack | absolute index `sb + h − k` (`h` static, relative to the frame) | stack chips |
| 2 | globals | global index | GLOBAL chip; initial values from the statement (BOUNDARY) |
| 3 | linear memory, one message per touched aligned word (offline memory checking) | word address | LOAD/STORE; initial values by MEMINIT rows (one per touched word; uniqueness by a sorted-address range check; value = data segment, checked against a cached DATA table bound by `code_root`, or 0) |
| 4 | call records | callee `cid` | CALL produces `[4, cid', 0, retpc, sb, cid, 0, ts]`; RETURN consumes it |
| 16 + cid | locals of activation `cid` | local index | LOCAL; initialised by param moves and an LINIT row per declared local |

Dead activations' locals and memory words stay live until the end. A generalised DRAIN consumes any
message with `space ≠ 0` (`space·inv = act`) at the end; operand-stack messages are drained only after
a trap (as now). This is sound because every produced message is consumed exactly once: draining a
message that is still needed leaves its later consumer without a producer, so the bus is unbalanced.

**`RelV X s fs tps tpl tpg tpm T t pc S sb cid live`:**
* `s.frames = fs` (non-empty). Frame `k` has function, local pc, `base`, `cid_k`, labels and locals.
  The top frame matches `pc/sb/cid`, and each frame's labels and relative height come from that
  function's `check`.
* `live x ↔` one of:
  * `x ∈ stackView s.stack tps`: the whole stack, all frames, absolute slots;
  * `x ∈ localView (16 + cid_k) locals_k tpl_k` for some frame `k`;
  * `x ∈ callView fs`: one record per non-top frame, holding the return pc and the caller's `sb`/`cid`;
  * `x ∈ globalsView s.globals tpg`;
  * `x ∈ memView T s.pages tpm`: words in the touched set `T`, which is fixed for the whole run by the
    MEMINIT rows;
  * `x ∈ Dead`: messages of returned activations, whose space never equals a live `16 + cid`, since
    `cid` is unique.
* The invariants as now (`numS`, `numL`, times below `t`, gas), plus memory bounds
  (`memBytes = pages · 64 KiB`), and `T` ⊆ addresses below `memBytes`.

**What changes where.**
* `Event` and `Step`:
  * The straight-line step lemma `straight_rel` keeps its form; the frame stack, globals, memory and
    `Dead` are carried unchanged.
  * New lemmas for global get/set, load/store (consume and produce a word message), call (pushes a
    frame, produces a call record, moves params, initialises locals) and return (pops a frame,
    consumes the call record, adds the callee's locals to `Dead`).
* `Check`:
  * becomes per module: `check` of every function, global pcs, call targets, and the per-function
    `nloc`/arity;
  * domain conditions stay explicit: no `call_indirect` until the table is modelled, recursion depth
    and `cid` bounded by `N < 2^28`, the memory bound on touched words, and D3 kept for branches
    (calls only need a callee's height at return to equal its arity, which the checker already
    verifies per function).
* `Abstract` / `Exec`:
  * RowSpec quantifies over `RelV`;
  * `init` = boundary initial globals + entry frame's locals + MEMINIT words;
  * `fin` = boundary finals + DRAIN;
  * the end-of-run analysis (`final_stack`) uses the stack view only.
* Row lemmas:
  * mechanical edits: state messages get `sb, cid`, stack slots become `sb + h − k`, local spaces
    become `16 + cid`;
  * the proofs go through the unchanged API.

**Order.**
1. R1: the relation, the views and the step lemmas, with existing instructions re-proven.
2. R2: AIR state width, slots and DRAIN in Lean and Rust, with the row lemmas updated.
3. R3: `Exec`/`Final` (theorem re-proven, tests rerun). Commit.
4. Family 2: LOAD/STORE/MEMINIT/DATA.
5. Family 3: GLOBAL.
6. Family 4: CALL/RETURN, module-level `check`.

### 10.1 As implemented (R1–R3 done, 2026-10-19)

* **Relation.** `RelW X E s f tps tpl t pc S live` with a frame environment
  `E : Env = {sb, cid, rest, live}`. The design above listed every view in one structure. The
  implementation keeps only the current frame explicit. Caller frames' locals, call records and,
  later, globals, memory words and `Dead` form an outer predicate `E.live`, which lives in spaces
  other than 0 and `16 + cid` (`envSep`). Straight-line and control step lemmas carry `E` unchanged.
  Families 2–4 add their views as invariants on `E.live`.
  * Frame fields: `s.frames = f :: E.rest`; `f.base = E.sb`; `f.labels = shiftLabels E.sb ls`,
    where `ls` comes from `check`; the stored height is relative (`size − sb`).
  * `entry`: `cid = 0 → rest = [] ∧ sb = 0`.
  * `sbLt`, `cidLt`: `sb, cid < 2^28`. These are field-size domain conditions; family 4 must
    re-establish them at each call.
  * `Rel X s t pc S sb cid live` hides `E, f, tps, tpl` and fixes `E.sb = sb`, `E.cid = cid`.
* **Row lemmas.**
  * `RowSpec`/`RowSpec2` quantify over `E`. The input STATE is `stMsg pc t S 0 E.sb E.cid`, and the
    output may carry a different `sb', cid'` (for calls).
  * Normal return: the live set is the final stack, plus `localView 16` (the entry frame's locals),
    plus an outer part `G` in other spaces.
  * The per-chip proofs use the same API as before. The only new helper is `slot_toNat`
    (`sb + h − k` ↦ `size − k`).
* **AIR.** Lean is the source of truth; the Rust side follows through the JSON export.
  * Each instruction chip gets `fr_sb, fr_cid` as its last two columns, passed through unchanged.
  * Stack slots are `fr_sb + h − k`.
  * LOCAL:
    * uses space `16 + fr_cid`;
    * adds a column `inv_sp` with the constraint `act·((16 + cid)·inv_sp − 1) = 0`. This makes the
      produced local message and the produced stack message distinct, which the per-row `Nodup`
      needs; without it, a range check on `cid` would be required.
  * CTRL: HALT/HALTIF only at `cid = 0`, via `(f_halt + f_hif)·cid = 0`. A callee's return is
    family 4.
  * BOUNDARY:
    * sends `(0, 1, 0, 0, 0, 0)`;
    * receives `(pc_f, N, S, status, sb_f, cid_f)`, where `sb_f, cid_f` are free columns because a
      trap can happen in any frame;
    * initial and final locals use space 16.
  * Not yet: the generalised DRAIN. It arrives with family 2, the first source of non-stack
    messages that are still live at the end.
* **Evidence.**
  * `lake build`; `wasm_base_sound` axioms: `[propext, Classical.choice, Quot.sound]`.
  * KAT 63/63.
  * difftest: 480 points; 10,784 constraint values and 6,560 interactions agree.
  * Tamper suites, including the new frame columns: `logs/tamper-*.log`.

## 11. Family 2: linear memory (2026-10-19)

**Scope.** All 12 integer loads and 7 integer stores, with static offsets below 2^32 (`isLoadOp`,
`isStoreOp` in `Check`). Memory has the configuration's initial size for the whole run. These are
domain conditions:
* no `memory.grow` or `memory.size`;
* no bulk memory operations;
* `mem ≤ 2^27`;
* `dataEnd ≤ 2^27`.

An out-of-bounds access cannot be proved (like out-of-gas): the trace generator refuses it, and a
proof of it does not exist. **D3 (no-discard branches) is not lifted yet**; see "Not done" below.

**Design: offline memory checking through the value channel** (`Chips.lean`):
* Memory is CH space 3, with one message `[3, addr, 0, byte, 0, 0, 0, tp]` per touched byte.
* A LOAD consumes the address and the `w` byte messages at `ea + i`, and produces them again with
  time `ts`, followed by the result.
* A STORE consumes the value, the address and the old bytes, and produces the value's bytes.
* `ea = e0 + 2^16·e1` is exact:
  * `a0 + off0 = e0 + 2^16·c` and `e1 = a1 + off1 + c`;
  * R16 checks on `e0` and on `32·e1`;
  * only `32·e1` is used, as in the existing time check, so a free `e1` cannot wrap.
* Sign extension uses the top byte's bit: `top = 128·sbit + low7`, with an R16 check on `512·low7`.
* MEMINIT (one row per touched byte, time 0):
  * active rows come first;
  * addresses strictly increase (gap `glo + 2^16·ghi`);
  * each address is `< 2^27` and `< mem`;
  * the value comes from a DATA lookup (`zd = 0`), or is 0 beyond `dataEnd` (`zd = 1`).
* DATA is a second **cached** table: `(a, image[a])` for `a < dataEnd`. Its commitment `data_root` is
  a statement component that V_d recomputes, like `code_root`; the native statement check verifies
  both.
* DRAIN is generalised: it consumes any leftover message, but `space = 0` (operand stack) only after a
  trap (`act·(1 − space·inv)·(status − 2) = 0`).
* Public values gain `mem` (index 9) and `dataEnd` (index 10); the locals' tags start at 11.
* There are 19 AIRs: LOAD and STORE are instruction tables 11 and 12; MEMINIT is table 17 and DATA
  table 18.

**Lean** (`WasmBase.Mem`, `StepMem`, `Local/Mem`, `Main/MemInit`, `Main/RowLoad`):
* `HeapOK` is a new `RelW` field. The space-3 part of the outer live set is exactly
  `memView T s tpm`, with `T` the touched set (fixed for the run, in bounds) and `PagesOK s`.
* `readLE`/`writeLE` are characterised byte-wise (`readLE_eq`, `writeLE_facts`).
* `step_load` and `step_store`: from live byte messages, no trap, the spec value, and the heap update
  (`heap_update`). They are built on `straight_rel_env`, a straight step that also changes the outer
  live set.
* `load_sem`: the 12 loads' little-endian and sign-extension arithmetic, proved per op.
* Row lemmas `load_rowfacts` and `store_rowfacts`.
* MEMINIT: active rows and their decoded messages (`meminit_row`, `meminit_mono`, `meminit_init`:
  the messages are distinct, at time 0, and equal to the initial memory view).
* `wasm_base_sound` now needs these statement hypotheses on the initial state:
  * `PagesOK s0`;
  * `DataOK s0 tr` (the binding of the cached DATA table);
  * `pub.mem = memBytes s0 ≤ 2^27`, `pub.dataEnd ≤ 2^27`;
  * bytes at addresses `≥ dataEnd` are 0.

  Axioms: `[propext, Classical.choice, Quot.sound]`.

**Evidence.**
* KAT 66/66, including `memkat` (every load at aligned, unaligned and word-crossing addresses; every
  store, including at the page edge) and `memloop8` / `memloop64`. Each is checked as Python reference
  = Lean spec = Rust trace + AIR pre-check.
* difftest: 608 points; 12,256 constraint values and 9,760 interactions agree.
* Tamper suite on `memkat`, including memory cases (LOAD/STORE bytes, `ea`, sign bit, MEMINIT
  value / address / duplicate address, DATA byte vs `data_root`, DRAIN space):
  `logs/tamper-memkat.log`.

**Not done (next).**
* Lifting D3: discarding branches would need kill rows, or an orphan sink with the stale-slot argument.
* `memory.size`/`memory.grow`.
* Word-granular memory messages, to cut the ~32 interactions of an 8-byte access.

## 12. Family 3: globals (2026-10-19)

**Scope.** `global.get x` and `global.set x` on numeric (i32/i64) globals, `x < 2^16` (`Check`:
straight-line, records `op = 0x23 / 0x24`, `[x, 0, 0, 0]`). Domain conditions (`GlobOK`, explicit):
* the module has `ngl ≤ 2^16` globals, all numeric (reference-typed globals are out of the domain;
  the trace generator refuses them);
* the public values encode the initial globals.

Mutability is the spec's business: an immutable `global.set` is rejected by validation before `check`.

**Design** (`Chips.lean`):
* Globals are CH space 2, one message `[2, g, tag, l0, l1, l2, l3, tp]` per global.
* No new chip. LOCAL gets two flags, `f_gget` (col 26) and `f_gset` (col 27):
  * channel space `(1 − isG)·(16 + cid) + 2·isG`, with `isG = f_gget + f_gset`;
  * `rd = f_get + f_gget`, `wr = f_set + f_tee + f_gset`, stack push count `f_get + f_tee + f_gget`;
  * `op = 0x20 + f_set + 2·f_tee + 3·f_gget + 4·f_gset`;
  * the existing `space · inv_sp = 1` check now covers both spaces, so the produced variable message
    and the produced stack message always differ.
* BOUNDARY sends each initial global at time 0 from the public values `[tag, l0..l3]` at
  `pubLoc + nloc + 5g`. `numPub = pubLoc + nloc + 5·ngl`.
* The final globals are drained by DRAIN (space 2, so allowed after a normal return).
* `wasmBaseAir nloc ngl`: the second parameter, formerly unused, is now the number of globals.

**Lean:**
* `HeapOK.glob`: the space-2 part of the outer live set is exactly `globView s.globals tpg`, with
  every global numeric and produced before `t`. `straight_rel`/`ctrl_rel` carry `s'.globals = s.globals`.
* `step_globalGet` and `step_globalSet` (`StepMem`); `heap_glob_read`, `heap_glob`.
* `local_rowfacts` covers the five LOCAL ops; `local_sound` gives the five flag bits and
  `act = 1 → space ≠ 0`.
* `Exec`: `globRaw` (the boundary's global sends), `glob_view` (decoded, they are
  `globView s0.globals 0`), and the initial outer live set = globals ++ MEMINIT bytes.
  `meminit_init` now returns only the memory part.
* `wasm_base_sound` gains the hypothesis `GlobOK nloc ncode pub s0`. No `sorry`; axioms
  `[propext, Classical.choice, Quot.sound]`.

**Evidence.**
* KAT 68/68, including `globkat8` and `globkat64`. These cover i32 and i64 mutable globals updated in
  a loop, an immutable global read on every iteration, and a swap of two globals through the stack.
* difftest `wasmBaseAir 2 4`: 304 points, 6,160 constraint values and 4,912 interactions agree
  (`logs/difftest-globals.log`).
* Tamper suite on `globkat8`: 52/52 rejected (`logs/tamper-globkat8.log`). The global cases are:
  * LOCAL global.get row: `L0`, `idx`, `inv_sp`, `tL`, and the row relabelled as `local.get`;
  * LOCAL global.set row: `V0`, and the row relabelled as `local.set`;
  * the public initial global's limb and tag;
  * a DRAIN global row's value and its `act`.

  The first run "accepted" `STACK.V1_0+1` on `globkat8`, where STACK row 0 is a `drop`. `V1` (the
  select's first operand) is read only by `select` rows, so on a `drop` row it is a free witness that
  does not change the statement, and this is not a soundness issue. The harness now targets a
  `select` row for this case (in `hashloop8` and `memkat`, row 0 was already a `select`).
* Tool: `prep` prints `ngl` and `globals`; `air <nloc> <ngl>`.

## 13. Family 4: calls — design (written before the implementation; see §13.1 for what was built)

Written before the implementation, as §10 was, so another agent can continue it.

**Spec facts used** (`NearSpecV3.Wasm.Exec`):
* `call fi` is `callFunc (advance s) fi`: the caller's pc is advanced first. Then `enter`:
  * if `stackRem < stackCharge`, it aborts (MAV);
  * it charges `prologueGas = k · regular_op_cost`;
  * the new frame gets `locals = args ++ zeros` and `base = size − np`, with the root label at
    height `base`.
* Return (`end` of the body, `return`, `br` to the function label) is `doReturn`:
  * `stack := stack[0, base) ++ results`;
  * the frame is popped and `stackRem` is restored;
  * the result is `.fin` only when no frame is left.
* Under D3 the callee's height at every exit equals its arity, so `doReturn` leaves the operand stack
  unchanged: the results already sit at slots `base ..`. A return therefore moves no stack values.

**Domain** (explicit, decidable):
* module-level `check`: the entry function and every function reachable by `call` pass the
  per-function check;
* `call` targets are defined functions (no host calls, no `call_indirect`);
* each function has `np ≤ 8` params and `nl ≤ 64` locals (params included);
* a call that would hit MAV (stack budget exhausted) cannot be proved, like an out-of-bounds access
  (the trace generator refuses it).

**Design.**
* **Global pc.** The checked functions' code is concatenated (offset `off_F`). Records are keyed by
  global pc, and branch and call targets in records are global. The checker's labels stay local, as
  the spec's are.
* **`call` is straight-line for the static analysis** (pops `np`, pushes the arity), so the caller's
  height after the return is checked by the existing `verifyAt`.
* **CALL chip** (one row per call). It consumes the STATE `(pc, ts, S, 0, sb, cid)` and produces
  `(entry_F, ts+1, S + fee, 0, sb + h − np, ts)`, where `fee` = the call's fee units + the callee's
  prologue units. The records give the callee's data:
  * the call record: `[pc, OP_CALL, h, fee, entry_F, hdr_F, charge_F, 0]`;
  * the function header record at `hdr_F` (a pseudo-record outside executable code; no instruction
    chip fetches its op): `np`, `nl`, the declared locals' type mask (64 bits in 4 limbs), the arity.

  It produces:
  * a call record `[4, ts, 0, pc+1, sb, cid, charge_F, ts]`;
  * the callee's locals in space `16 + ts`:
    * slot `j < np`: the value consumed from stack slot `sb + h − np + j`;
    * slot `np ≤ j < nl`: zero, with the declared type.

  It consumes the stack-budget register (space 5, slot 0), checks that it is `≥ charge_F` by range
  checks, and produces it with `charge_F` subtracted.
* **RET chip.** It handles `opHalt`/`opHif` records at `cid ≠ 0` (`cid · inv = 1`); CTRL keeps
  `cid = 0`. It consumes the call record `[4, cid, 0, retpc, sb_c, cid_c, charge, tp]` and the budget
  register, and produces `(retpc, ts+1, S + fee, 0, sb_c, cid_c)` and the register plus `charge`.
* **Dead activations.** The callee's locals stay live after its return and are drained at the end
  (space `16 + c`, `c ≠ 0`, is allowed in DRAIN).
* **BOUNDARY** sends the initial budget register from a public value. DRAIN consumes the final one.

**Relation** (`Event`):
* `E.rest` (the caller frames) gets a saved-context chain `CallerOK`. For each caller frame:
  * its function is checked;
  * its pc is the return pc;
  * its labels are `shiftLabels sb_k (labels[retpc])`;
  * `heights[retpc] = sb_{k+1} − sb_k + arity_{k+1}`;
  * its locals view is in space `16 + cid_k`, with producer times `< t`;
  * the matching call record is in space 4.
* Of `E.live`, spaces 4 and `16 + c` (`c ≠ cid`) are exactly:
  * the call records;
  * the callers' local views;
  * dead activations' messages (`c < t`, not an active activation).
* All activation ids are `< t`, so the space `16 + t` of a new callee is empty.
* The budget register is a `HeapOK`-style field: exactly one message `[5, 0, 0, s.stackRem, …]`.

**Order.**
1. Module-level `Ctx` / `check` with global pcs. Re-prove everything (the entry function only).
2. The relation's caller chain, and `step_call` / `step_return`.
3. CALL / RET chips and their row lemmas; `Exec`/`Final`.
4. Rust, KAT (calls, recursion, params, locals, dead-activation drain), difftest, tamper.

### 13.1 As implemented (2026-10-19)

**Differences from the design above.**
* **No header pseudo-record.** The callee's static data comes from a second cached table, FUNC
  (table 21, bus 6). It holds one row per checked function:
  `[entry, np + 128·nl, charge, prologue, m0, m1, m2, m3]`, where `nl` counts the params too and
  `m_q` are the 16-bit limbs of the 64-bit local type mask. FUNC is bound through the statement
  like CODE (`func_root`, a deterministic function of the code; padded by repeating the last row).
  The call record is `[pc, 0x10, h, fee, entry, 0, 0, 0]`.
* **CALL state out** is `(entry, ts+1, S + fee + prologue, 0, sb + h − np, ts)`. The call record in
  channel space 4 is `[4, ts, 0, pc+1, sb, cid, charge, ts]`.
* **Range checks.** The new budget `n = r − charge` is checked as canonical limbs: `r16(n0)`, `r16(n1)`
  and `r16(4·n1)`, so `n < 2^30`. `r16(4·n1)` alone leaves `n1` free modulo p; the Lean proof caught
  this. `sb + h − np` and `ts` each get `r16(lo)`, `r16(hi)` and `r16(16·hi)`, so each is `< 2^28`.
* **RET** handles every HALT/HALTIF record at `cid ≠ 0` (`act·(cid·invc − 1)`), including an untaken
  `br_if`. CTRL still forbids halts at `cid ≠ 0`.
* **Extra explicit domain conditions in `wasm_base_sound`:**
  * `FuncOK`: the FUNC table is the checker's function table;
  * `BudOK`: `stackRem < 2^30`, and its limbs are the last two public values
    (`numPub = pubLoc + nloc + 5·ngl + 2`).

**Lean.** Everything below has no `sorry`, and the axioms are unchanged.
* The checker is module-level (`checkModule`, `ModFacts`, `Ctx`).
* Relation:
  * `RelW.calls : CallsOK`, the caller chain `Chain`, with its call records and saved local views;
  * `chainMsgs`, holding spaces 4 and `≥ 16` besides the current frame's locals; everything else is
    dead activations;
  * the budget register `budMsg`.
* Steps (`StepCall`): `step_call`, `step_return` and `step_returnIf`.
* Rows:
  * `Local/Call.call_sound` (the mask and count decoding);
  * `Main/RowCall.call_rowfacts` and `Main/RowRet.ret_rowfacts`;
  * `Lookups.FuncOK` with `instr_func`.

**Rust / Python.**
* `tracegen.rs` keeps a frame stack (`sb`, `cid`, return pc, charge, locals) and sets `fr_sb`/`fr_cid`
  on every row. LOCAL uses `inv_sp = (16 + cid)⁻¹`. The static height check is `h = len − sb`.
* CALL rows move params and zero the declared locals by mask type, emit the call record, and handle
  the budget, range and time checks and the FUNC multiplicities. RET rows cover taken and untaken
  returns.
* DRAIN takes:
  * the dead callee locals (at the end);
  * the final budget register;
  * after a trap: the operand stack, plus every live callee frame's call record and locals. The
    entry frame's locals still go to BOUNDARY, whose `sbf`/`cidf` are the trapping frame's.
* `wasmasm.py`: type, function and code sections for several functions, `('call', i)`, params.
  `refinterp.py`: recursive per-function execution with a shared step counter.

**Evidence.**
* KAT 73/73 (python reference = Lean spec run = Rust trace + full constraint/bus pre-check) (`logs/kat.log`). The new
  programs are:
  * `callkat8` and `callkat64`: i32 and i64 params, declared locals of both types read before being
    written, nested calls, a void callee writing a global, `return` from inside a block, a callee
    `br_if` to the function label (taken and not taken), and calls in a loop;
  * `fib1` and `fib10`: recursion, 177 calls;
  * `calltrap`: a division by zero two frames deep, after a successful call.
* difftest `wasmBaseAir 2 1`, `0 0` and `4 2`: 176 points each. Constraint values and interactions all
  agree (`logs/difftest-calls.log`).
* Tamper suites on `callkat8`, `calltrap` and `fib10` (`logs/tamper-<prog>.log`; running at this commit, results in the next commit). The
  call cases are:
  * CALL: forged `entry`, `shape`, `charge`, `pro`, mask limb, budget limbs and producer time, the
    `sb + h − np` and `ts` limbs, frame columns, `S` and `fee`, param value, time and tag, a dropped
    or extra param, a flipped declared-local type, an extra local, and `act = 0`;
  * FUNC: `charge` (caught by `func_root`) and the multiplicity;
  * RET: `retpc`, `sbc`, `cidc`, `charge`, `tpr`, budget limbs and time, `invc`, frame columns, a
    deleted row, and the condition of an untaken `br_if`;
  * DRAIN: the budget, the call record after a trap, and a callee-local row's `act` and `tp`.

