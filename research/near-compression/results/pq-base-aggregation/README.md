# PQ base layer and n-to-1 aggregation: results (phase 1)

Lane `lane/pq-base-aggregation`. The architecture is in `DESIGN-BASE.md`.

**Revision (2026-10-18, after lane/pq-prover-latency d1a208ef7).**

The design is **G**: one shared-transcript base proof → L1 → T1 → T2 → FINAL.
* **G has no aggregation layer over segments.** Continuity between segments is global-bus terms inside the
  one proof.
* **L1 is k-to-1 only for independent side proofs** (P-PERF-8 PREP / code-hash). The prototype covers it:
  `build_l1_linked`, test `agg_g_l1_linked`.
  * An honest main + sub-proof pass the full debug check (19,028 program rows, 2 transcript chains).
  * A main proof whose code commitment differs from the sub-proof's is rejected, by the program and by the
    circuit.
  * A tampered statement limb is rejected.
* **Bound with z = 24 on base and inner layers, z = 32 on the final layer: PASS, 2^−134.88**
  (`bound-base.out`; uniform z = 32: 2^−134.68 in `bound-base-z32.out`).
* The range-statement tree (N1/N2) below is the fallback for multi-cluster setups.

## What is here

| file | what |
|---|---|
| `DESIGN-BASE.md` | the end-to-end architecture: base AIR set, segments, statement, aggregation, V_d digest, cost per level, assumptions, tree soundness, Base-faithful (S-22), risks |
| `base_bound.py` → `bound-base.out` (z split), `bound-base-z32.out` | S-24: final-soundness `calc/bound.py` (read with `git show` at f8c168f98, not copied) re-run with the pinned base shapes. **PASS, 2^−134.88 (z = 24 base and inner, 32 final); 2^−134.68 (uniform z = 32)** |
| `base_agg_model.py` → `model.out` | cost model for designs G / T2 / T8 / H at adversarial 1 Pgas on 32 H200 |
| `../../native/recursion/patches/openvm-recursion-agg.patch` | the prototype: an overlay on `openvm-recursion-sha384.patch` |
| `../../native/recursion/setup_agg_deps.sh` | builds the overlaid tree under `NEARPROOF_PQ_DEPS` (default `/data/illia/nearproof-deps/pq-base-agg`) and verifies it |
| `logs/` | test and run logs |

Reproduce:

```sh
native/recursion/setup_agg_deps.sh
cd $NEARPROOF_PQ_DEPS/openvm-sha384/crates/recursion
cargo test --release -p openvm-recursion-circuit --lib -- agg_
PARENT_BITS=10 PARENT2_BITS=10 AGG_LOG_ROWS1=17 AGG_LOG_ROWS2=19 \
  cargo test --release -p openvm-recursion-circuit --lib -- agg_chain --ignored --nocapture
```

## The prototype: a k-to-1 NV node (`nv/agg.rs`)

### Code changes (overlay patch, 12 files, +919 / −31)

* **Multi-chain transcript.** Each child's verifier runs on its own Fiat–Shamir transcript.
  * `Builder::restart_transcript`.
  * `replay2_multi(log, starts)`.
  * In the hash-chain role, `is_first` may appear on any row. Its input state is the initial-state
    constant, its t_start comes from the anchor, and `hn = nkh·(1 − next.is_first)`.
  * The ALU declares each chain start: the first job's anchor carries P3 = 1, and the hash row receives
    `is_first` in the anchor message. Chain starts are therefore program constants.
  * Cost: **0 columns**, 0 interactions.
* **Statement.**
  * `PvD` (op 31): NvAir public values are `[level, 18 digest limbs]`. This is the same layout and
    semantics as the recursion lane's G1 passthrough, which is uncommitted there; the merge is
    mechanical.
  * `TAG_RANGE = 9`: D = SHA-384(prefix, 9, [n_ctx, n_state, ctx, a, e, S_a, S_e]), truncated like Merkle
    digests (GLUE `merkle` class).
* **`build_agg(children, kind, preimages)`.** It runs k child verifiers and reads each child's public
  values from its transcript.
  * `App` children: (ctx, j, pre, post).
  * `Node` children: [level, D]. The preimage is witnessed, hashed in-circuit and compared with D.
  * It then checks ctx equality, index adjacency and boundary-state continuity, and exposes level and D.
* **`build_verifier`** returns the child's public-value cells and has an `agg` mode.
* **`NvCircuit::generate_with`** runs any program. `prove_mats` takes public values from the builder.
* **Test fixture `SegAir`.** A Fibonacci machine split into segments. Public values are
  [ctx, j, pre (l, r), post = step(last row)].

### Measurements

**Circuit shape** (`agg_shape`, keygen) [M]. The AIRs are the same as NV's:

| AIR | width | interactions/row | degree | public values |
|---|---:|---:|---:|---:|
| NvAir | 73 | 55 | 8 | 19 |
| Sha512Air | 171 | 14 | 21 | 0 |
| TableAir | 13 | 2 | 4 | 0 |
| ByteAir | 5 | 1 | 3 | 0 |

The k-child node changes no column, degree or interaction count.

**Program size per child** [M] (child = `SegAir` proof at `child_params_small`). The per-child cost equals
the 1-ary verifier: `nv_program_fib` is 9,227 rows for a Fib child. Statement work adds ≈ 0.6k rows per node.

| setting | k = 2 | k = 3 | per child |
|---|---|---|---:|
| 48 B digests, default levers | 18,451 rows, 721 jobs, 464 Merkle nodes | 27,649 rows, 1,081 jobs, 696 Merkle nodes | 9.2k |
| 42 B + coset leaves + all child levers (k1, ×15, keep, multiproof, Gruen, derive, next-mask, WHIR-Y, tight, wide PoW) | 12,688 rows, 229 jobs, 212 Merkle nodes | 19,000 rows | 6.3k |

Debug-size circuit (log_rows 17) [M]: NvAir 2¹⁷ × 73, Sha512Air 2¹⁶ × 171, total 21.1M cells for k = 2 and
k = 3. Under the levers, k = 2 fits in 15.5M cells.

**Real proofs** (`agg_chain`, CPU, 32 threads, test targets): see the "agg_chain" section below.

### Tests (all pass; logs in `logs/`)

**Program level** (`agg_program_honest`, `agg_program_tamper`):
* Honest k = 2 and k = 3: no failures, k − 1 transcript restarts, and the exposed statement equals the
  native `RangeStmt::compose`.
* Each tamper is detected:
  * swapped children: index and state continuity;
  * broken continuity (a valid proof of a segment starting elsewhere): state continuity;
  * dropped child (segments 0, 2): index and state continuity;
  * other chunk: ctx.

**Circuit level** (`agg_circuit_debug`: full constraint and bus debug check). Honest k = 2 and k = 3 pass.
Each tamper below is rejected:

| tamper | rejected by |
|---|---|
| statement digest limb (PV 5) | PvD constraint |
| level PV | Pv constraint |
| chain start removed (`is_first` cleared, previous row's `hn` set) | anchor bus (P3 mismatch) + chain bus |
| chain start forged (`is_first` set mid-chain, previous `hn` cleared) | initial-state constraint / anchor bus |
| swapped children | ALU Zero rows |
| broken continuity | ALU Zero rows |
| dropped child | ALU Zero rows |

**Configurations.** Both pass, at 48 B defaults (`logs/agg_circuit_debug.log`) and at 42 B with every child
lever (`logs/agg-42-levers.log`).

**Native** (`agg_segment_chain_native`): the segments chain, and composition rejects swapped or skipped
segments.

**NV regression with the overlay.** All 17 non-ignored `nv::` tests pass (`logs/nv-suite-48*.log`), except
`nv_app_binding`. That test needs 17.2 GB, above this lane's 16 GB cap; its public-value vector was updated
but it was not re-run here.

### Limits of the prototype (stated in `agg.rs`)

* **`Node` children are not program-bound.** A real N2 needs one BIND region per child (DESIGN §5.1), or
  the preprocessed program commitment (§5.3).
  * The 2-region BIND design reuses the existing BIND/app-binding roles: the ALU sends (y, P) with count 2;
    there are per-child E tables and per-child ACC rows; it adds one role flag column.
  * It is specified but not built.
* `Node` children must be at the same level (a balanced tree).
* N1 requires k ≥ 2 here. DESIGN §4 uses k = 1 for one-segment chunks.

## S-24: pinned base parameters and `bound.py`

`base_bound.py` patches `bound.py` in memory so that each shape may set its own c and m. `whir_schedule` and
`log_mca` already take them; `layer_moves` did not pass them.

Pinned shape seg-v1:
* c = 1, b = 1, m = 16, k₁ = 1, k = 4, lf = 7, log_h = 24, W ≤ 24;
* 32 AIRs, degree 8, 2¹⁴ constraints, 1024 opened columns, 2²⁸ interactions;
* 42 B, z = 32, target 268.

Results:
* queries [518, 247, 80, 48, 34];
* worst move: round-0 query, 2^−268.00;
* **total 2^−134.68, PASS**; the 7-layer union is 2^−131.87;
* the final and inner NV schedules still equal the backend's.

The alternatives and node shapes also pass (`bound-base.out`).

**Tree caveat.** A per-proof union over a 295-proof tree gives 2^−126.48, which **fails** as a union. The
claim needs Theorem 7.4's single database (DESIGN §9.1).

## agg_chain (real proofs, CPU, 32 threads; `logs/agg-chain-T10*.log`)

Two N1 nodes, each 2-to-1 over two Fib-machine segment proofs. Parameters: PARENT n_stack 16, b 3,
10 query bits, queries [8, 5, 4, 3, 2, 2].

| node | cells | program rows | Merkle nodes | chain starts | proof | prove | peak RSS |
|---|---:|---:|---:|---:|---|---:|---:|
| N1a (segments 0-1) | 21.1M | 19,030 | 464 | 2 | 139,609 B (GKR 40,904 / relations 44,640 / stacking 5,776 / WHIR 48,104) | 845–932 s | 4.8 GB |
| N1b (segments 2-3) | 21.1M | 19,030 | 464 | 2 | 139,609 B | 384–922 s | 5.5 GB |

* Both proofs verify natively.
* Their exposed public values equal `check_range_statement` of the composed range statements.
* **N2** (2-to-1 over the two N1 proofs) has a program of 118,916 rows (59.5k per NV child). Its trace
  (NvAir 2¹⁹) did not prove within the lane's 16 GB cap:
  * first attempt: stacked-height error at n_stack 16;
  * second attempt: OOM-killed at n_stack 17.
* The level-2 node logic is instead checked in the debug checker by `agg_node_debug`
  (`logs/agg-node-debug.log`; PARENT n_stack 15, b 2, 8 bits; AGG_LOG_ROWS2 20).
  * Two real N1 proofs feed one N2 trace: 136,988 program rows, 1,048 Merkle nodes, 166.5M cells
    (NvAir 2²⁰ × 73, SHA 2¹⁹ × 171).
  * The trace passes all constraints and buses, and exposes the composed statement of segments [0, 4).
  * Rejected: a wrong preimage (claims another boundary state), swapped children, a duplicated child.
  * Peak 5.2 GB; the run took 34 min.
* Since G needs no N2, this is not pursued further.
