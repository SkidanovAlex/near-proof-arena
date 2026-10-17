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

## NV v1: air2 SHA AIR plus narrowing the non-SHA AIRs

### Step 1: air2 SHA AIR (k = 3), measured

This step uses the S lane's air2 compression AIR (171 + 13 columns, degree 21) and new
word-format glue AIRs: packer, block, transcript hash, sample and Merkle.
* The debug checker passes.
* Five tamper classes are rejected.
* The debug-size circuit is 7.8M cells (v0: 16.7M).

The chain ran at T = 20 with n_stack = 19. Heights are natural here (no NV_FIXED), and
the ALU is 2^18 rows. Log: `logs/nv2-chain-T20-k3.log`.

| level | verifies | cols (opened) | interactions (L) | cells (SHA / other) | ALU rows used | Merkle nodes | leaf blocks | proof B (gkr / relations / stacking / whir) | prove s |
|---:|---|---:|---:|---:|---:|---:|---:|---|---:|
| A1 | Fib | 634 (1,268) | 5.64M (23) | 33.63M (5.60M / 28.03M) | 7,288 | 232 | 128 | 193,886 (40,904 / 82,032 / 2,992 / 67,772) | 313 |
| A2 | A1 (NV) | 634 (1,268) | 10.29M (24) | 76.52M (44.83M / 31.70M) | 75,387 | 1,252 | 384 | 208,590 (44,408 / 82,032 / 3,952 / 78,012) | 2,196 |

* **Proof size:** A2 is 208.6 KB at the T = 20 test target. The column term (relations)
  is the largest, at 82 KB for 634 columns.
* **Prove time:** A2 took 7× longer than A1 for 2.3× the cells. In A2 the degree-21
  SHA AIR has 2^18 rows. Part of A2 also overlapped other test jobs on the same 8
  cores, so this is not a clean timing.
* **Other cells:** 28M of the "other" cells are the 105-column ALU at 2^18 rows. Step U1
  below removes about 45 % of that.
* A3 then ran on the same shape: 208,590 B, and its Obs AIR doubled in height. The
  chain was stopped there because this layout was superseded by U2 below.
  Log: `logs/nv2-chain-T20-k3.log`.

### Step U1: merged ALU + BIND AIR ("UAIR", 59 columns), debug-checked

`nv/uair.rs` replaces the 105-column ALU. One 59-column AIR has two row roles.

**ALU rows** are the lower half, `[0, 2^(H-1))`, and hold the program:
* An op is `8·hi + lo`, with one-hot halves `h[8]` and `g[3]`. The selector is
  `h[lo]·g[hi]`, degree 2. This replaces 22 one-hot flags.
* Every ALU row sends `(y, P0..P3)` on a bind bus.

**BIND rows** are the upper half, one per ALU row:
* They enumerate `y = ya + 512·yb` in order. A counter enforces `ya < 512`, with a wrap
  flag and an inverse column.
* They read E1[ya] and E2[yb] from the program's reserved rows. These memory lookups
  share interactions with the ALU operand reads.
* They receive `(y, P)` and accumulate `acc += e1·e2·Σ τ^j P_j`.
* The last BIND row sends the total, on an acc bus, to the ALU `Acc` row.

**Why the total is the full multilinear evaluation:**
* The P columns are constrained to zero outside ALU rows.
* The fixed `Acc` row sits at program address 2^(H-1) − 1.
* Together these force the ALU region to be exactly the lower half. So the binding total
  is the multilinear evaluation of P over the whole trace, as the parent's opening check
  needs.

**The BIND role reuses the ALU columns:**
* a, b and c hold e1, e2 and acc.
* h[0..8] holds pc0..3, ya, yb, zw and inv_w.

**Cost:**
* Interactions per row: 19, the same as the old ALU.
* Constraint degree: at most 6. The debug check passes with max degree 9 at k = 2
  (`NEARPROOF_SHA_K=2`), so k = 2 stays usable.
* Tests passing: `nv_program_*`, `nv_circuit_fib_debug`,
  `nv_circuit_interactions_debug`, `nv_opening_formula` (formula = opening for
  P0..P3 at the new offsets) and `nv_circuit_tamper`. The tamper test rejects 7 classes:
  the old 5 plus `bind-acc` and `bind-program-word`.
* Columns: total 634 → 588, non-SHA 450 → 404. At H = 18 the UAIR is 2^18 × 59 =
  15.5M cells, against 27.5M for the old ALU (2^17 program rows; A2 uses 75,387).

**Next (U2):** fold the glue AIRs (Hash2 72, Block 102, Merkle2 80, Pack 48, Samp 34,
Obs 7) into row roles of shared narrow AIRs, to get toward about 100 non-SHA columns.

### Step U2: one non-SHA AIR (NvAir), measured

U2 replaces every non-SHA AIR with one AIR, **NvAir**: 69 columns, degree 8,
60 interactions per row. The rows are split into five role regions.

| region | rows | what it does | replaces |
|---|---|---|---|
| ALU | `[0, 2^prog_log)` | the verifier program (U1 ISA), plus new ops `UnitW`, `Dig`, `NodeJob`, `Anchor` | ALU |
| BIND | half of the program length | each row covers 2 ALU rows: E1[ya], E1[ya+1], E2[yb] and the accumulator; `ya/2` is range-checked on the byte table | BIND |
| GLUE | 8 per job compression | one row per pair of message words: bytes, framing, felt/word units, the state pair, 3 SHA interface pairs, digest pairs; a node mode handles Merkle node jobs | packer (48 cols), block chaining (102), the Merkle AIR's interface |
| HASH | one per transcript job | the transcript hash chain | Hash2 (72 cols) |
| SAMP | one per squeezed state word | the sample engine | Samp2 |

Supporting changes:
* **Transcript:** the ALU pushes observed felts and commitment words directly as units of
  statically numbered flush and commit jobs. The ALU also anchors each job with
  `(job, t_start, count)`, which pins its position in the tidx order. The chain row
  forwards its output state as the next job's state units. Squeeze jobs are numbered
  dynamically.
* **Merkle:** paths now run in the ALU program. Child digests come from the digest bus
  (`Dig`). L/R selection is done by Ext12 operations on the bit cells. Node jobs are
  `NodeJob` plus 4 `UnitW`. The root is compared with the commitment cells. Digests are
  held in 4-word + 2-word cells. The Merkle AIR and the key bus are gone.
* **Shared interaction slots:** each role is evaluated against a collecting builder.
  Interactions on the same bus share slots, with message = Σ flag·message and
  count = Σ of the role-gated counts. This takes 59–60 slots instead of about 120.
* **Role order:** a stage value is enforced to be monotone, so each role occupies one
  contiguous region. P0..P3 are common columns that are zero off ALU rows. So the
  program-binding argument is unchanged: the opening formula test still passes.

Tests passing:
* `nv_circuit_fib_debug`, `nv_circuit_interactions_debug`, `nv_opening_formula`,
  `nv_program_*`;
* `nv_hash2_*`: GLUE, including node jobs and 78 mutation cases;
* `nv_circuit_tamper`: Merkle sibling, opened value, transcript sample, transcript state
  limb, ALU result, BIND accumulator, BIND program word;
* `nv_degrees`: NvAir has degree 8. With k = 2 the SHA AIR has degree 9, so k = 2 stays
  usable.

**Columns (measured), non-SHA AIRs:**

| | v1 step 1 | U1 | U2 step 1 (GLUE) | step 2 (transcript) | step 3 (Merkle→ALU) | step 4 (one AIR) | step 5 (BIND ×2) |
|---|---:|---:|---:|---:|---:|---:|---:|
| non-SHA columns | 450 | 404 | 308 | 267 | 187 | 66 | 71 |
| total columns (opened = 2×) | 634 | 588 | 492 | 451 | 371 | 250 | 255 |

Step 5 adds 5 columns. In exchange it halves the BIND rows, which lets NvAir fit 2^18
rows instead of 2^19.

**Chain at T = 20, n_stack = 19 (measured):** NV_LOG_ROWS = 18, NV_PROG_LOG = 17.
Log: `logs/nvu2b-chain-T20.log`.

| level | verifies | cols (opened) | interactions (L) | cells (SHA / NvAir) | program rows | Merkle nodes | proof B (gkr / relations / stacking / whir) | prove s |
|---:|---|---:|---:|---:|---:|---:|---|---:|
| A1 | Fib | 255 (510) | 16.19M (24) | 23.69M (5.60M / 18.09M) | 10,509 | 232 | 157,509 (44,408 / 45,024 / 2,752 / 65,212) | 494 |
| A2 | A1 (NV) | 255 (510) | 19.40M (25) | 62.92M (44.83M / 18.09M) | 79,104 | 1,252 | 171,797 (48,056 / 45,024 / 3,664 / 74,940) | 2,154 |

**Against v1 step 1 at the same level (A2):**
* relations 82,032 → 45,024 B;
* total 208,590 → 171,797 B;
* cells 76.5M → 62.9M.

For reference, the first U2 build before BIND packing was A1 = 165,653 B, with NvAir at
2^19 × 64. Log: `logs/nvu2-chain-T20-A1.log`.

**Program cost per query (measured, `NV_QCOST`, A2):**
* round 0: 762 rows, at depth 21;
* rounds ≥ 1: 566 + 19 rows per extra path level.
* The breakdown is about 230 rows for index bits, recomposition and fold, plus leaves,
  plus Merkle. Merkle costs 2·2^k leaf digests + 7·(2^k − 1) coset nodes + 17 rows per
  path level + 4.
* The fixed part before the queries (preamble, GKR, DAG, stacking) is 42,040 rows.

## Milestone (d): final-layer extrapolation [MODEL]

`extrapolate_nv.py` uses the NV U2 structure measured above:
* columns, interactions per row and degrees;
* rows = 1.5 × program + 8 × compressions + transcript;
* program = 40k + Σ queries × measured per-query cost.

It combines that structure with the corrected final-layer model the S lane uses
(`../pq384-sha-air2/score_designs.py` / `ext.py`), with the same levers: ×15 domains,
coset leaves, multiproof, packing. It then iterates to the NV fixed point.

What is measured and what is not:
* None of the levers is implemented in-circuit yet. Their in-circuit cost is modelled
  with the measured per-node and per-row costs.
* GKR uses the levers-lane law, 48L² + 192L + 152. Today's backend measures
  48,056 B at L = 25.
* "pad" means power-of-two trace heights, as the backend has today. "none" is the split
  or padding-free heights lever.

| setting | heights | final bytes | whir | gkr (L) | relations | penultimate compressions | queries | program → padded | cells | interactions |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| L (z = 32, 42 B, 236 / 226 bits) | pow2 | **310,803** | 222,982 | 34,952 (25) | 45,004 | 4,843 | 102 | 124,414 → 2^17 | 2^25.91 | 2^24.21 |
| L | none | **299,667** | 215,542 | 32,408 (24) | 45,004 | 4,729 | 102 | 120,842 | 2^25.60 | 2^23.95 |
| L + byte-pair lookups (48 int/row) | pow2 | 308,259 | 222,982 | 32,408 (24) | 45,004 | 4,843 | 102 | 124,414 → 2^17 | 2^25.91 | 2^23.95 |
| T (268 bits, 48 B) | pow2 | 378,827 | 289,374 | 37,592 (26) | 46,060 | 5,446 | 115 | 141,476 → 2^18 | 2^26.27 | 2^25.07 |
| T | none | 364,514 | 272,277 | 34,952 (25) | 45,004 | 5,182 | 115 | 132,940 | 2^25.73 | 2^24.08 |

**Reading:**
* With NV U2 the final layer is WHIR-dominated, at about 215–223 KB of the
  300–311 KB. Relations are about 45 KB. Of that, about 24.5 KB is the 255 columns
  opened at two points. About 17 KB is the degree-21 SHA AIR's (d + 1)·n sumcheck term.
* Under 300 KB at the L settings needs all of:
  * the in-circuit levers (×15, coset leaves, 42 B digests, z = 32 grinding, multiproof);
  * NV U2 as built;
  * either padding-free trace heights, or about 9 KB of other savings. The candidates
    are byte-pair lookups (−2.5 KB), a 43-row SHA layout and a cheaper Merkle select.
* At power-of-two heights the model gives about 308–311 KB.
* At the T settings nothing gets below about 360 KB.
* **The program sits at 124k rows, close to 2^17.** The fixed point holds only while
  the program stays under 2^17 rows. At the T settings it crosses into 2^18, and the
  NvAir height doubles.

**Hardware for the real final-layer run [estimate]:**
* The fixed point is about 2^25.9 cells, at L = 24–25, with a ×15 domain at rate 2^-9
  (pen shape b = 9). The low-degree extension is about 2^25.9 × 2^9 × 15 ≈ 2^38.8 field
  elements. That has to be streamed or sharded; the CPU backend here cannot hold it.
* That points to the multi-GPU (H200-class) prover in the chunk-proof target, with
  about 100+ GB of host RAM.
* At T = 20 the measured CPU prover takes about 36 min per level on 8 threads at
  23 GB. The degree-21 SHA AIR dominates that.
