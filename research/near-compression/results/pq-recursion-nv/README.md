# NV: narrow fixed-point verifier circuit (results)

Design: `DESIGN.md`. Code: `crates/recursion/src/nv/` in the `openvm-sha384` tree (patch
`native/recursion/patches/openvm-recursion-sha384.patch`). Tests: `cargo test --release -p
openvm-recursion-circuit --lib nv_`.

## Milestone b: NV v0 verifies a real child (measured)

NV v0 has 10 AIRs:
* ALU (104 columns);
* transcript hash/observe/sample (95 / 8 / 20);
* MerkleNv (100);
* SHA-512 compression (442);
* SHA table (18), block chaining (134), packer (45), byte table (2).

That is **968 columns** in total. The 37 verifier-logic AIRs of the port are replaced by
the one ALU.

* **Program.** `nv/verifier.rs` is the stark-backend SWIRL verifier written against a
  program builder (`nv/builder.rs`). The builder emits one ALU instruction per call and
  executes it at the same time.
  * The program's transcript ends in the same state as the native verifier's
    (`nv_program_fib`, `nv_program_interactions`).
  * A second proof of the same shape yields the identical instruction stream, so the
    program depends only on the vk, the params and the trace heights.
  * Tampering with any of 6 proof fields makes an in-program assertion fail.
* **Circuit.** The child is Fib 2⁵ (test params: l_skip 2, n_stack 8, k 3, queries
  [13, 7, 6], PoW 1–3 bits, checked in-circuit). The debug checker passes on all
  constraints and buses. An interactions child also passes. Size: ALU 2¹⁴ rows (7,405
  used, program incl. 544 reserved binding rows), 16.7M cells.
* **Tamper classes, all rejected by the circuit:**
  * Merkle sibling digest: Merkle root key lookup.
  * Opened value: ALU `ZERO` (WHIR final check). The Merkle root would also fail.
  * Transcript sample, row-consistent: slot bus against the ALU, state-word bus.
  * Commit limb: slot bus, unit bus.
  * An ALU result: ALU constraint.
* **Not yet active:** program-word tampering at one level is caught only by the next
  level's binding check (milestone c) or by the native final check. This is by design;
  see DESIGN §2.1.

## Milestone c: NV verifies NV (v0, measured at a 20-bit query target)

**Parameters.** Every level is proven with l_skip 2, n_stack 19 (stacked height 2²¹),
k 3, log_blowup 3, ListDecoding m = 3, 20 query bits, queries [16, 9, 7, 5, 4, 4], no
PoW. Level 0 is Fib 2⁵ under test params.

**Phase A, natural heights** (`logs/nv-chain-T20-phaseA.log`). The shape repeats from
level 2 onward:
* A2 = A3 = A4: 147.7M cells, 247,834 B.
* Only the transcript-hash AIR moves, from 1,024 to 2,048 rows.

**Phase B, fixed heights** (`logs/nv-chain-T20-fixed.log`):
* Every level uses the same trace heights, so every NV proof has one shape. The
  verifier program from level 2 on is therefore identical.
* Each NV exposes its level as a public value of the ALU AIR, and its program asserts
  level = child level + 1.
* The binding check (child program = own program, through the in-circuit MLE) is
  emitted at every level ≥ 2. It is enforced when the child's level ≠ 1, using a flag
  that the level forces.
* So levels 3 and 4 check, in-circuit, that their child ran the same program. The flag
  is 0 only when the child is level 1, which verified the app with a different program.

| level | verifies | opened cols | interactions (L) | cells (SHA / other) | ALU rows used | Merkle nodes | leaf blocks | proof B (gkr / relations / stacking / whir) | prove s |
|---:|---|---:|---:|---:|---:|---:|---:|---|---:|
| 1 | Fib | 1,938 | 17.86M (25) | 147.98M (115.87M / 32.11M) | 7,294 | 232 | 128 | 247,934 (48,056 / 98,688 / 5,584 / 95,420) | 178 |
| 2 | L1 (NV) | 1,938 | 17.86M (25) | 147.98M | 91,996 | 1,252 | 640 | 247,934 | 187 |
| 3 | L2 (NV), binding on | 1,938 | 17.86M (25) | 147.98M | 91,996 | 1,252 | 640 | 247,934 | 195 |
| 4 | L3 (NV), binding on | 1,938 | 17.86M (25) | 147.98M | 91,996 | 1,252 | 640 | 247,934 | 194 |

* Level 1 is padded to the fixed heights, which is why it is as large as level 2.
* Peak RSS is 23.0 GB, at the cap. Every proof verifies natively.

**Scaling laws checked:**
* relations = 2·48·cols + 5,784 + …: 98,688 B at 969 columns, matching the ext2 law.
* GKR: 72L² + 264L + 248 = 51,848 at L = 25, against 48,056 measured (−7 %).
* Merkle nodes = Σ_r q_r·(2^k − 1 + depth_r): 1,252.
* Leaf blocks = q₀·2^k·⌈(4W + 58)/128⌉ + Σ_{r≥1} q_r·2^k, with W = child stacked width
  ≈ 71: 640.
* The column-opening absorption is the largest transcript term. NV opens 1,938 Ext12
  values, about 23k felts, or about 730 compressions per level.

**Known gaps:**
* **Base case:** level 2 does not check level 1's program, the app-verifier program.
  This is the T_app table check: an MLE of a constant table of about 8k rows, about 24k
  ALU rows. It is designed, not built.
* **Coverage:** levers are not implemented in v0.
* **Columns:** at 969 (1,938 opened), v0 is far over the 100 non-SHA-column budget.
  That is the next step: the air2 SHA AIR plus one shared non-SHA AIR.
