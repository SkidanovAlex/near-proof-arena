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

**Step 6** makes three changes:
* the byte table becomes a byte-pair table (65,536 × 5; single bytes are looked up as
  (v, 0));
* NvAir drops to 48 interactions per row (from 60);
* Merkle path nodes use new select-push ops `UnitWS4` / `UnitWS2`. The unit index is
  offset by 12 × bit, so a path level costs 10 ALU rows instead of 17.

This brings the non-SHA columns to 74 (NvAir 69 + byte table 5), and 258 in total.

**Chain at T = 20, n_stack = 19 (measured):** NV_LOG_ROWS = 18, NV_PROG_LOG = 17.
Log: `logs/nvu2b-chain-T20.log`.

| level | verifies | cols (opened) | interactions (L) | cells (SHA / NvAir) | program rows | Merkle nodes | proof B (gkr / relations / stacking / whir) | prove s |
|---:|---|---:|---:|---:|---:|---:|---|---:|
| A1 | Fib | 255 (510) | 16.19M (24) | 23.69M (5.60M / 18.09M) | 10,509 | 232 | 157,509 (44,408 / 45,024 / 2,752 / 65,212) | 494 |
| A2 | A1 (NV) | 255 (510) | 19.40M (25) | 62.92M (44.83M / 18.09M) | 79,104 | 1,252 | 171,797 (48,056 / 45,024 / 3,664 / 74,940) | 2,154 |
| A3 | A2 (NV) | 255 (510) | 19.40M (25) | 62.92M | 81,818 | 1,252 | 171,797 (same) | 2,161 |
| L1 | Fib, fixed heights | 255 (510) | 19.40M (25) | 62.92M | 10,509 | 232 | 171,797 | 2,141 |
| L2 | L1 (NV) | 255 (510) | 19.40M (25) | 62.92M | 84,025 | 1,252 | 171,797 | 2,146 |
| L3 | L2 (NV), **binding on** | 255 (510) | 19.40M (25) | 62.92M | 84,025 | 1,252 | 171,797 | 2,149 |
| step 6 A1 | Fib | 258 (516) | 13.11M (24) | 24.02M | 9,669 | 232 | 157,797 (44,408 / 45,312 / 2,752 / 65,212) | 505 |
| step 6 A2 | A1 (NV) | 258 (516) | 16.32M (**24**) | 63.24M | 72,843 | 1,252 | **168,437** (44,408 / 45,312 / 3,664 / 74,940) | 2,130 |

What the chain shows:
* **Fixed point:** A3 has the same heights as A2, so the fixed point is reached:
  heights [2^18, 2^18, 64, 256].
* **Binding:** phase B ran L1 to L3. L3 verifies L2 with in-circuit program binding
  enforced. Every proof verifies natively.
* **Resources:** peak RSS 19.3 GB, 3 h 07 min for 6 levels. Log:
  `logs/nvu2b-chain-T20.log`.
* **Step 6:** two levels, peak 11.2 GB. Log: `logs/nvu2c-chain-T20.log`. Interactions
  fall under 2^24, so L drops to 24 and saves 3.6 KB of GKR.

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
| L (z = 32, 42 B, 236 / 226 bits) | pow2 | **308,547** | 222,982 | 32,408 (24) | 45,292 | 4,843 | 102 | 107,952 → 2^17 | 2^25.91 | 2^23.95 |
| L | none | **298,881** | 214,612 | 32,408 (24) | 45,292 | 4,729 | 102 | 103,924 | 2^25.55 | 2^23.55 |
| T (268 bits, 48 B) | pow2 | 363,519 | 277,954 | 32,408 (24) | 45,292 | 5,270 | 115 | 116,963 → 2^17 | 2^25.91 | 2^23.95 |
| T | none | 359,535 | 269,890 | 32,408 (24) | 45,292 | 5,182 | 115 | 113,883 | 2^25.68 | 2^23.68 |

These are the step 6 numbers. Before step 6 the model gave L = 310,803 (pow2) /
299,667 (none), and T = 378,827, because the T program crossed 2^17.

**Reading:**
* With NV U2 the final layer is WHIR-dominated, at about 215–223 KB of the
  299–309 KB. Relations are about 45 KB. Of that, about 24.8 KB is the 258 columns
  opened at two points. About 17 KB is the degree-21 SHA AIR's (d + 1)·n sumcheck term.
* Under 300 KB at the L settings needs all of:
  * the in-circuit levers (×15, coset leaves, 42 B digests, z = 32 grinding, multiproof);
  * NV U2 as built;
  * either padding-free trace heights, or about 9 KB of other savings. The candidates
    are per-column next-row openings (about 3 KB) and a 43-row SHA layout.
* At power-of-two heights the model gives about 308.5 KB.
* At the T settings nothing gets below about 360 KB.
* **Program margin:** after step 6 the program is about 108k rows (117k at T), so both
  settings fit under 2^17. If it crossed 2^17, the NvAir height would double.

**Hardware for the real final-layer run [estimate]:**
* The fixed point is about 2^25.9 cells, at L = 24–25, with a ×15 domain at rate 2^-9
  (pen shape b = 9). The low-degree extension is about 2^25.9 × 2^9 × 15 ≈ 2^38.8 field
  elements. That has to be streamed or sharded; the CPU backend here cannot hold it.
* That points to the multi-GPU (H200-class) prover in the chunk-proof target, with
  about 100+ GB of host RAM.
* At T = 20 the measured CPU prover takes about 36 min per level on 8 threads, with a
  peak of 11–19 GB. The degree-21 SHA AIR dominates that.

## Phase 2, step 1: one unified backend patch stack [measured]

`native/recursion/patches/stark-backend-unified.patch`, built by
`native/recursion/setup_unified_deps.sh` on top of the pinned d667af5 + native base tree. It
contains:

* **Levers:** the levers patch from lane/pq-whir-levers, round 3 at 85be07ae2: k1, multiproof,
  keep-domain, coset-leaf hook, next-row mask, Gruen GKR and Gruen batch, derived GKR claims,
  2-element PoW, and `tight_heights`.
* **×15 domains:** the ×15 patch from lane/pq-x15-domains at 2cf46f1a4.
* **Merge fixes:** conflicts resolved, plus three interplay fixes I found by bisection:
  * `MerkleTree::new_with_cosets` now hashes each fold coset with `MerkleHasher::hash_coset`.
    Before the fix, ×15 with coset leaves failed with `MerkleVerify`.
  * the multiproof depth now adds `ceil_log2(c)`. Before the fix, ×15 with multiproof failed.
  * `stacked_commit_odd` takes the tight flag.
* **CPU backend port** (`crates/cpu-backend`):
  * commit and WHIR opening go through the reference PCS (`stacked_commit_odd`,
    `prover::whir::prove_whir_opening`), and the PCS data is the reference `StackedPcsData`;
  * the stacking reduction is the reference `StackedReductionCpu`, which carries the rotation
    masks and tight chunks;
  * the row-major zerocheck/GKR prover gets the four lever edits: per-column rotation masks,
    Gruen GKR, Gruen zerocheck, derived claims;
  * `committed_heights` is implemented.

Every lever is off by default.

* **Defaults reproduce existing proofs:**
  * gas-failure5 re-proved on the unified backend is byte-identical (`ba042e71…`), with both
    the native driver and the levers driver at defaults (`logs/unified/unified-default.log`).
  * The x15 lane's `ident` hashes equal its recorded base hashes.
* **Upstream tests:** 142 backend tests plus the CPU-backend tests pass.
* **Levers alone, on gas-failure5:** coset + 42 B + multiproof + m = 8 + z = 16 + Gruen +
  derive + next mask gives 241,027 B, with 21 negative cases rejected.
* **×15 alone:** the x15 lane's self-test rejects 55/55 cases, and its adversarial words are
  rejected.
* **Every lever plus ×15 plus tight heights,** on a 17-column dummy with 700 of 1,024 rows
  real: 176,587 B, with 26 negative cases rejected (`logs/unified/unified-all-tight-x15-dummy.log`).
* **CPU backend equals the reference** (`nv::tests::unified_cpu_matches_reference`): the
  row-major CPU backend produces byte-identical proofs to the reference backend for Fib and
  interactions fixtures. The cases are: default, k1 = 1, keep-domain, multiproof,
  Gruen + derive, next mask, ×15, tight, and all of them together. They hold both with the
  SHA levers at default and with `NEARPROOF_COSET_LEAF=1 NEARPROOF_DIGEST_BYTES=42`.

**Recursion SHA config** (`sha384/config.rs`):
* It ports the hash levers of `native_sha384_levers_config.rs`: v5 framing prefix,
  42-byte truncation, tag-6 coset leaves, and tag-7 PoW with one or two witness elements. They
  are process-global (env), because the codec is static.
* The native transcript vectors and the native differential test still pass.

**First in-circuit lever, the PoW check:**
* NV's `pow_check` now follows the tag-7 scheme:
  * a static transcript job `H(7, [state, witness])` hashed by GLUE and chained by the hash
    role;
  * the hash role sends the output word 0 (limbs) to a new ALU op `PowChk`;
  * the ALU proves that the top `bits` bits are zero, by recomposing only the allowed low bits
    of limbs 1 and 2 from BIT rows.
* The NV debug, tamper and opening tests pass with the child's PoW bits active.

## Phase 2, step 2: levers inside NV's verifier program [measured: debug checks and tamper tests]

Each lever below is consumed in-circuit. Each is tested with a child proof that uses it:
* the program run is cross-checked against the native verifier's transcript
  (`nv_program_*`);
* the circuit passes the debug constraint and bus check;
* the tamper cases listed are rejected.

| lever | in NV | tamper tests |
|---|---|---|
| tag-7 PoW (one or two elements) | static transcript job `H(7,[state,w])`; the hash role sends word 0 to the ALU `PowChk` op; the top z bits are proved zero from BIT rows | PoW witness, wide element 1 |
| coset leaf | one tag-6 leaf job per query (2^k rows); no coset tree | opened value, codeword value |
| WHIR-Y (new backend lever, default off, native prover and verifier) | `obs12(y_i)` before γ in every round | (transcript cross-check), codeword value |
| Gruen GKR + derived claims | s(3) and the derived fields are zero in the proof; t(0..2) and p_xi_1 / q0 are recomputed with checked inverses | s(3) ≠ 0, s(1), p_xi_1 ≠ 0, q0 ≠ 0, layer q_xi_1 |
| Gruen zerocheck | last eval recomputed: Lagrange at s_deg of s(k)/eq1(k) | last eval ≠ 0, eval |
| next-row mask | rotated claims only for masked columns; per-column stacking kernels | column opening |
| k1, keep-domain | per-round k and domain sizes | k1 leaf row |
| ×15 | rejects x = p−1; index = (x mod 15·2^m) with witnessed q, a; point ζ^a·ω^u0; depth +4 | final poly, codeword |
| multiproof | the witness generator decompresses the stream into per-query paths, and every path is hashed to the root in-circuit (no dedup savings) | initial / codeword digest |
| 42-B digests | GLUE node42 mode (L aligned, R at byte shift 2, 2-byte tails); Merkle jobs truncate word 5 (flag declared by the job's producer on the job bus); commit payload gets a 2-byte tail + pad slot with a bit-length correction | (hash mutations at 42 B), Merkle digests |
| tight heights | the committed height is observed; chunk factors c and δ in the stacking kernel; claim index by column | stacking opening, opened row (zero-tail fixture with 700 of 1,024 rows) |

* **Zero padding:** NvAir padding rows are now all zero, including `y` and the pool. A
  non-zero value in a padding row is rejected (`nvair padding row y/pool`). The S lane's
  SHA AIR v2.1 is merged and ported: 43 rows, zero-valid padding, `cid = 43 × index`.
* **Degrees:** NvAir stays at degree 8 with 42-B digests. With k = 2 the SHA AIR is
  degree 9, so k = 2 is still selectable.
* **Next-row mask on NV's own AIRs:** NvAir 36/70 columns rotated, SHA 144/171, table 11/13,
  byte table 2/5.

## Phase 2, step 3: app-verifier binding, and a soundness fix [measured]

**App binding.** The NV program (levels ≥ 2) now carries the level-1 program as a data
region: `Data` rows directly after the reserved rows, holding its words verbatim.
* A new row role (app-binding rows, flag `kc`) accumulates the multilinear evaluation of
  that table at the child's point, using the same E1/E2 tables.
* Its length is pinned by `Acc2`'s P0.
* The binding check is flag·own + (1 − flag)·(ACC2 + the fixed last-row term) = p̂. The
  flag is 0 exactly when the child is level 1.
* `nv_app_binding`: level 2 over a real level-1 NV proof accepts the honest table. A
  one-bit change in the table is rejected: the program binding fails and the circuit's Zero
  constraint fails. Log: `logs/nv-app-binding.log`, 17.2 GB peak.

**Soundness fix: the op was not bound to P1.** An ALU row's op is selected by witness
one-hot columns. P1 = B + op·2^20 was only decomposed, never range-checked. So a prover could
relabel a row to an op that does not use B and keep the same program words. For example, a
`Const` row relabeled as `Load` gets a free result. This was present since v0.
* **Fix:** B ∈ [0, 2^20) on every non-data ALU row, checked by byte-pair lookups (3 pool
  columns; the lookups share existing byte slots).
* `Acc` additionally pins the BIND region length.
* Test `op relabel const->load` is now rejected.

## Soundness fix T* (final-soundness G-1, G-2, G-9, G-10, G-11) [measured: tests]

Source: lane/pq-final-soundness @ ae0ae8a7b, `final-soundness/{PROOF.md, GAPS.md}`. These
changes are in the backend tree, in the native SHA config, in the recursion SHA config, and in
the NV circuit.

**The transcript (T\*).** The flag is `tstar` in `ShaLevers`; its framing prefix is v6.
* **T\*-1, counter-mode squeeze.** Challenge blocks are B_j = H(5, κ‖le32(j)), j = 1, 2, …, where
  κ is the key after the absorb. Once a squeeze run ends, the transcript state is the last
  block consumed. A squeeze message is 101 bytes, so each block is still one compression.
* **T\*-2, PoW blocks.** B_j = H(7, σ‖w‖le32(j)).
  * The PoW is the first z bits of B_1.
  * Challenges begin at B_1's next 64-bit word, then continue with B_2, …
  * The honest grind costs one compression per attempt: 105 bytes for a narrow witness, 109
    bytes for a wide one.
* **G-11.** When z = 0, the witness must be zero. This holds in the backend default
  `check_witness` / `check_witness_wide`, the SHA transcripts, and NV (`Builder::pow`).

**Backend fixes** (`stark-backend-unified.patch`):
* **G-9:** the verifier rejects `tight_height = Some(_)` when common_main = 0, and the prover
  never emits one.
* **G-10:** when c ≠ 1, the odd domain factor c is bound into the vk pre-hash (`x15c‖c`).
  c = 1 keeps the upstream bytes.
* NV takes the child's pre-hash and parameters as program constants, and the program is bound,
  so this also holds for recursion.

**Where it is turned on:**
* **Recursion crate** (`sha384/config.rs`): on by default. `NEARPROOF_TSTAR=0` gives the legacy
  chained squeeze, which the native vector and differential tests need. With T\* on, those
  two tests skip.
* **Native levers driver** (`native/recursion/levers-check/`): set by env `NEARPROOF_TSTAR=1`.
  The default is off, so gas-failure5 stays byte-identical at defaults.

**NV circuit** (`nv/transcript2.rs`, `nv/builder.rs`):
* **New hash-chain row kinds and columns:**
  * `op_q` is a PoW-run block B_j with j ≥ 2.
  * new columns: `ctr`, `nwit`, `scnt` (samples read from B_1), `rd`, `nsq`, and
    `state_in[18]`.
* **State units.** Each row sends its own input-state units. Rows are linked by a
  `chain` bus, not by next-row reads, so no column is rotated: the previous row sends
  (next job, its key if the next row is squeeze or PoW-run, otherwise its output).
* **First row.** Its input state is the initial-state constant.
* **Counters:**
  * a squeeze block takes j = 1 after an absorb, otherwise j + 1;
  * a PoW-run block takes j + 1;
  * B_1 is j = 1;
  * the counter is unit 16, or 16 + nwit after the witness units.
* **Reads.** The sample role starts a B_1 run at word 1. The ALU pushes the PoW witness units
  into every block of the PoW run.
* **Cost.** NvAir grows from 70 to 73 columns and from 52 to 55 interactions per row. The
  rotated columns stay at 36. The proof grows only by the 3 extra column openings
  (≈ 144 B) plus the extra cells. The SHA count does not change, because every block is still
  one compression.

**Tests (all pass):**
* **Backend:** 142 backend tests, plus the CPU-backend tests, plus new tests for G-11 (zero
  witness) and G-10 (the pre-hash changes with c). Log: `logs/tstar/unified-tstar-tests.summary.log`.
* **Recursion SHA config:** `tstar_counter_mode` and `tstar_pow`. They check B_j against the
  spec formula, that the state is the last block consumed, wrong counters, the old chain, a
  witness ground on the old chain being rejected, challenges starting after the PoW word, and
  G-11.
* **NV suite:** 20 tests, with the SHA levers both at default and at all child levers (42 B,
  coset, x15, k1, keep, multiproof, Gruen, derive, next mask, WHIR-Y, tight, wide PoW). This
  includes `unified_cpu_matches_reference`.
* **NV `nv_tstar_tamper`.** The fixture has 30 squeeze, 12 PoW and 16 PoW-run blocks. Each of
  these is rejected:
  * a wrong counter on a squeeze block;
  * a wrong counter on a PoW-run block;
  * a squeeze-key limb;
  * challenges read from B_1's PoW word;
  * a logup PoW witness ground on the old chain.
* **Native levers driver.** The default profile still gives gas-failure5 byte-identical
  (`ba042e71…`). With T\* plus every lever plus ×15 plus tight heights on the dummy:
  177,007 B, 26 lever negatives rejected, and 3 T\* negatives rejected. The T\* negatives are a
  prover that deviates and an honest verifier that rejects it:
  * counter j + 1;
  * a PoW ground on the old chain;
  * challenges taken from the PoW word.
* **Native levers driver on gas-failure5,** with T\*, 42 B, coset, multiproof, m = 8, z = 16,
  Gruen, derive, next mask and WHIR-Y: 242,329 B, 21 plus 3 negatives rejected.
* The proof size moves by a few hundred bytes against the pre-T\* runs, because the query
  positions change and so does multiproof dedup.

## Audit fixes B1–B6, statement passthrough (G1), final-layer domain (U-12) [measured: tests]

**Audit fixes B1–B6 merged.** Source: lane/pq-nv-circuit-soundness 2e36b0228, 09fead0bc,
274fe5ccf; see `FAITHFUL.md`. I re-applied them on top of the unpadded program and T\*, and
kept their tests (`faithful_tests`, `faithful_tr_tests`, `faithful_sha_tests`, DOF harness).
* **B1:** the B-field range is integral.
* **B2:** the child's trace-height limit is checked.
* **B3:** base-field loads use `LoadF`.
* **B4:** the 42-B commitment tail is written by `UnitWT`.
* **B5:** squeeze job ids are pinned. Under T\* I extended this: squeeze blocks and PoW-run
  blocks share the pinned numbering `TJOB_SQUEEZE_BASE + ns`, with
  `ns' = ns + op_s + op_q`. New tamper: `tstar PoW-run job id`.
* **B6:** anchors carry the job tag.

**Statement passthrough (G1).**
* **Level 1:** NV hashes the app proof's public values. The message is
  `[num_airs, len_0.., pv_0.., pv_1..]`, hashed with SHA-384 under a new tag 8
  (`TAG_STATEMENT`). It runs as a leaf job in the circuit and is truncated like Merkle
  digests at 42 B.
* **Exposure:** a new ALU op `PvD` (op 31; there are now 32 ops) exposes the digest as NvAir
  public values 1..19, from the lo and hi cells. NvAir public values are now
  `[level, 18 digest limbs]`.
* **Level ≥ 2, or any NV child** (`bind` or `child_nv`): the child's public values 1..19 are
  packed into cells and re-exposed unchanged.
* **Native V_d:** `circuit::check_statement(final_pvs, app_public_values)`. `nv_chain` asserts
  it for every level and for the final proof.
* **Tests:**
  * `nv_statement_digest`: the digest binds the app public values. Changed exposed limbs 1,
    12, 13 and 18 are rejected, and an app proof with a changed public value is rejected.
  * `nv_app_binding`: L1 = L2 = the statement digest, and a level-2 trace that re-exposes a
    different digest is rejected.

**Final-layer hash domain (U-12).**
* `Sha384CpuEngine::new_final` and `Sha384Config::new_final` give a transcript init of
  `H(2, ['F'])`, where inner layers use `H(2, [])`. Merkle nodes use node prefix byte 7 = `'F'`.
* Leaves are unchanged.
* It costs 0 bytes.
* The NV circuit only ever verifies inner children, so its constants stay inner. `nv_chain`
  proves the FINAL layer with `new_final`.
* **Test `final_layer_domain`:** a final proof is rejected under the inner domain, and an inner
  proof is rejected under the final domain. Each verifies in its own domain.

**SHA-384 is never inside a GKR layer.** Every in-circuit SHA-384 evaluation in NV is a
compression in committed `Sha512Air` rows of the common-main trace: leaf, coset leaf, node,
transcript flush/commit/squeeze, PoW, PoW-run, and statement jobs alike. Each compression takes
43 rows, and the GLUE, hash-chain and ALU roles reach it only through the job, iface and digest
buses. The GKR layers are only LogUp's fractional-sum tree over interaction fractions. This is
the mitigation for Khovratovich–Rothblum–Soukhanov-style attacks. Evidence:
* the `A*_AIR Sha512Air h=…` lines of every chain level;
* `hash_tests::nv_hash2_rejects_mutations`.

## Size analysis: where the 324 KB goes and what moves it [MODEL from measured laws]

These figures come from `extrapolate_nv2.py` (268 bits, z = 32, 42 B) and
`size_sensitivity.py`. The baseline final layer is **323,955 B**:

| part | bytes |
|---|---|
| WHIR | 242,562 |
| GKR (L = 24) | 32,408 |
| relations | 43,232 |
| stacking | 5,680 |

The penultimate layer uses b = 5, n_stack = 17. The program is 181,754 rows, NvAir has 341,773
rows and SHA has 309,858 rows.

* **Padding: already gone.** The program is not padded to 2^18. The unpadded layout (ACC2/ACC
  at fixed early rows) puts it at its real even length, and tight heights commit only the used
  NvAir/SHA rows. The model counts NvAir rows as prog + prog/2 + app/2 + glue + transcript, with
  no power of two, so 2^17 is not a threshold any more. Program cuts move bytes only linearly
  through the cells:

  | cut | final | change |
  |---|---|---|
  | app table moved out of the program (−11k rows) | 323,637 B | −0.3 KB |
  | program −28 %, every cost scaled | 320,565 B | −3.4 KB |
  | NvAir removed entirely (lower bound: SHA rows only) | 305,397 B | −18.6 KB |

  LoadBit query bits are about 22 rows per query, roughly 3 % of the program. T\* PoW-run blocks
  add 1–2 ALU rows per block.
* **Opened columns.** The relations term implies **455** opened values, not 258. The AIRs give
  cols + rot: NvAir 73 + 36, Sha512Air 171 + 144, Table 13 + 11, Byte 5 + 2. Next-row openings
  are already per column (the next-row mask: only columns read at the next row are rotated). The
  excess is Sha512Air's 144 rotated columns.
* **Relations is dominated by the SHA AIR's degree 21.** The parts are:

  | part | bytes |
  |---|---|
  | 48(cols + rot) | 21,840 |
  | 48((d+1)(2^l−1)+1) | 3,216 |
  | 48((d+1)n − g) | 17,760 |
  | 96·airs + 32 | 416 |

  Lowering the degree and the rotations:

  | SHA AIR change | final | change |
  |---|---|---|
  | degree 12 | 315,315 B | −8.6 KB |
  | degree 8 | 311,475 B | −12.5 KB |
  | 40 rotated columns instead of 144 | 318,963 B | −5.0 KB |

  These belong to the SHA AIR, owned by the S lane, not to NV.
* **GKR.** There are 2^24.85 interactions: 55 per NvAir row and 14 per SHA row. Cutting NvAir
  to 30 interactions per row would give L = 23, worth −2.4 KB (321,507 B).
* **In-circuit multiproof dedup is not possible with a bound program.** Which Merkle nodes
  coincide depends on the sampled indices, so the program would change from proof to proof. As
  a what-if it would be −3.4 KB, with 15 % fewer compressions (`DEDUP` flag, off).
* **Combined:**

  | levers | final |
  |---|---|
  | NV side: program −28 %, 30 interactions per row (dedup also on, though it is not possible) | 314,277 B |
  | plus SHA AIR degree 8 with 40 rotated columns | **296,805 B** |

  Getting under 300 KB needs the SHA AIR shape (S lane) or the MCA upgrade (lane/pq-mca-upgrade,
  −15 to −45 KB on WHIR, not counted here). NV-side program cuts alone cannot do it.

### MCA regimes (lane/pq-mca-upgrade @ 6841b5f56) and the program cut [MODEL]

`extrapolate_nv2.py` now takes the env `NV_MCA` to pick how many bits each WHIR query buys:
* `m3`: today's default, BCGM with `ListDecoding{m: 3}`.
* `m64`: O-1, DKT26 Thm 5.12 with `ListDecoding{m: 64}`.
* `O2`: O-1 plus O-2. Each round uses a first-order agreement
  a_i = (a1(ρ_i)/√ρ_i + 0.05)√ρ_i, which is `agreement_table()`, the rule in that lane's
  `dkt_certs.json` / `bound_mca.py`. The table is bound into the vk, and 48 B per later round
  are reserved for a second OOD answer.

Both upgrades are still pending verification. In the chain config, m is chosen with
`PARENT_LIST_M` / `FINAL_LIST_M`, and the default stays m = 3. The hook reproduces the lane's
numbers exactly: 323,955 / 313,759 / 300,733 B.

`size_cut_mca.py` gives each regime with the program cut (best penultimate b and n_stack):

| regime | baseline | program −28 % (< 2^17 rows) | plus 30 interactions per NvAir row |
|---|---|---|---|
| m = 3 | 323,955 (program 181,754) | 320,565 (126,690) | 318,117 |
| m = 64 | 313,759 (177,222) | 311,745 (123,804) | 309,297 |
| O-2 | 300,733 (165,884) | **299,229** (120,918) | **296,781** |

The program has no power-of-two padding, so the cut pays linearly: 1.5–3.4 KB for 28 %. 2^17
is no longer a threshold. Under O-2 the cut is what crosses 300,000 B.

Where the rows go, from the measured A2 at 268 bits with b = 2 (234,533 rows):
* preamble, including the app table: 38.4k;
* DAG: 22.1k;
* stacking: 12.5k;
* queries plus the final check: 161.6k.

Each Merkle level costs 10 rows: 2 sibling loads, 1 `one_minus`, `NodeJob`, 4 `UnitWS`, and 2
`Dig`. That is about 58k rows over all paths. A "load-and-push" UnitWS op that takes the sibling
as a free witness would remove the 2 load rows per level, about −12k rows (−0.8 KB). It needs a
33rd op, which means a fifth op-selector half and one more NvAir column.

**What a realistic program cut buys.** Take a sibling op that loads and pushes with the negated
bit (saving 3 rows per Merkle level), plus a cheaper fold butterfly (5 rows instead of 7). Then
the per-query cost drops from 451 to 379 rows in round 0 and from 530 to 437 in later rounds,
and the program goes from 181,754 to 160,364 rows (−12 %). The final layer moves only
**−0.3 KB** under m = 3 (323,637 B) and **−0.4 KB** under O-2 (300,357 B). The earlier
"−28 % = −3.4 KB" is mostly a step: crossing a stacking and penultimate-shape boundary.

NvAir cells are about 30 % of the total, WHIR bytes grow with the log of the cells, and the
query counts do not depend on them. So program rows are a weak lever. The strong levers are:
* the SHA AIR's degree and rotated columns;
* the MCA regime;
* WHIR queries.

### Correction: GKR runs over power-of-two heights; the 2^18 NvAir threshold [measured + model]

A2 at 268 bits measured GKR = 34,952 B, which is L = 25. GKR uses the full trace heights: tight
heights shrink only the commitment, not the LogUp tree. The interaction count is
2^19 × 55 (NvAir) + 2^19 × 14 (SHA) + tables = 2^25.1. `extrapolate_nv2.py` now counts
interactions on power-of-two heights, and NvAir is 74 columns as measured.

The corrected finals:

| regime | baseline | program −28 % | plus 30 interactions per row |
|---|---|---|---|
| m = 3 | 326,547 | 320,997 | 318,549 |
| m = 64 | 316,351 | 311,793 | 309,345 |
| O-2 | 303,701 | **299,277** | **296,829** |

So there is a real step after all. The interaction count drops below 2^25, giving L = 24 and
−2.5 KB of GKR, in either of two ways:
* NvAir gets under 2^18 used rows, so its height becomes 2^18;
* NvAir drops to at most 49 interactions per row, from 55.

That is why the program cut matters: 2^17 program rows is roughly 2^18 NvAir rows.

Interactions per bus, as the maximum over roles (`NV_INT_DUMP=1`, total 55):
* slot bus: 13 (hash role 13, ALU 12);
* byte-pair bus: 17 (GLUE 17);
* word bus: 6 (hash);
* ctl: 3 (GLUE);
* digest: 3;
* memory: 3;
* chain: 2;
* the rest: 1–2 each.

Cutting 6 means slimming GLUE's byte-pair lookups and the hash role's unit sends together.

The NvAir row budget (O-2 baseline) is about 315k rows:
* program 166k;
* BIND 83k, at prog/2;
* app 5.5k;
* GLUE 55k, at 8 rows per compression;
* transcript 6k.

Getting under 262k needs −53k rows. For example, BIND rows that each cover 4 program rows
would save 41k, and a further −8 % program would cover the rest. Either change touches the
audited program-binding argument.

## Phase 2, step 5: the real-settings chain at 268 bits [measured]

Logs: `logs/r268/`. Binary: nv-g2, which is lane head 95c08894c plus the chain driver. It
includes T\*, B1–B6, the statement passthrough and the final-layer domain.

Settings:
* 268 bits = 236 query bits + z = 32 wide PoW, 42-B digests, coset leaves, ×15 domains;
* k1 = 1, k = 4, keep-domain, multiproof, Gruen GKR and zerocheck, derived claims, next-row
  mask, WHIR-Y, tight heights, m = 3;
* penultimate (inner) layers: b = 2, n_stack = 18, log_final = 3;
* NvAir 2^19 rows, program limit 2^18.

All runs used 32 threads on a shared machine; other lanes' VMs held about 25 GB.

| level | what it verifies | wall | peak RSS | program rows | proof bytes | gkr | relations | stacking | whir |
|---|---|---|---|---|---|---|---|---|---|
| A1 | the Fib app proof | 48.1 min | 19.5 GB | 9,142 | 401,337 | 32,408 | 43,348 | 2,272 | 323,110 |
| A2 | A1 | 58.1 min | 58.3 GB | 234,534 | 473,565 | 34,952 | 43,348 | 6,784 | 388,282 |
| A3 (fixed point) | A2 | 48.8 min | 60.6 GB | 259,430 | 481,125 | 34,952 | 43,348 | 7,120 | 395,506 |
| **FINAL** | A3 | 45.3 min | 64.9 GB (68.0 by `time`) | 261,688 | **416,171** | 34,952 | 43,348 | 4,720 | 332,952 |

Notes on the run:
* **Fixed point.** Heights repeat from A2 to A3: NvAir 2^19, SHA 2^19, Table 64, Byte 2^16.
* **Statement.** `check_statement` passes for every level and for the final proof. The final
  binds the Fib app's public values.
* **Final layer** (`new_final` domain): b = 2, n_stack = 19, k1 = 1, k = 3, log_final = 8,
  queries [87, 74, 50, 38, 31], soundness 268.6 bits.
* **Larger final shapes OOM on this machine.** The model-preferred b = 3 shape (log_h 24)
  reached 82 GB, and b = 2 at log_h 25 reached 90 GB. The machine's watchdog killed both at
  MemAvailable < 10 GB, while other lanes' VMs were holding 25 GB. The A3 checkpoint
  (`NV_RESUME_PROOF`) made it possible to re-run only the final layer.

**Measured against the model, per component.** The model is `extrapolate_nv2.py`: laws plus
ext.layer, fed each run's own shape and stacked width W.

| level | WHIR model / measured | GKR (law L = 25) | relations law / measured | stacking law | total model / measured |
|---|---|---|---|---|---|
| A2 (W = 98) | 388,638 / 388,282 (−0.1 %) | 34,952 = 34,952 | 43,280 / 43,348 | 6,784 = 6,784 | — |
| A3 (W = 105) | 393,510 / 395,506 (+0.5 %) | 34,952 = 34,952 | 43,280 / 43,348 | 7,120 = 7,120 | — |
| FINAL (W = 53) | 333,828 / 332,952 (−0.3 %) | 34,952 = 34,952 | 43,280 / 43,348 | 4,720 = 4,720 | 416,853 / **416,171** (−0.2 %) |

**Conclusion.**
* **The measured final is 416,171 B,** at the largest final shape that fits this machine
  (b = 2, about 65 GB).
* **The size model is confirmed to within 0.5 %** on every component. GKR and stacking match
  exactly, and relations is off by 68 B, one column.
* **The model's optimum is not under 300 KB.** It needs b = 7–8, which means an x15 codeword
  of about 1 TB, so several H200-class nodes. There it gives 326,547 B (m = 3), 316,351 B
  (m = 64) and 303,701 B (O-2), with GKR corrected to power-of-two heights. With O-2 plus the
  program cut (NvAir under 2^18 rows, so L = 24), it gives 299,277 B.

**The final's WHIR bytes, broken down** [model for the measured shape; its WHIR total is
within 0.3 % of the measured 332,952]:

| part | bytes |
|---|---|
| Merkle authentication (42-B multiproof) | 208,824 |
| initial-round opened rows (k1 = 1, W = 53) | 36,888 |
| codeword values | 74,112 |
| final polynomial (2^8 Ext12) | 12,288 |
| small items | ~1.8 KB |

The rest of the measured final is GKR 34,952, relations 43,348 and stacking 4,720.

## O-2 implemented (U-13) and NvAir down to 49 interactions per row (L = 24) [measured: tests; model]

**O-2: the per-round first-order agreement table** (`stark-backend-unified.patch`).
* **Config.** `WhirConfig.agreement: Option<AgreementTable>` holds `target_bits`,
  `margin_milli` (50), `m` (64), and per round `(n_i, k_i, A_i, q_i)`.
  * `with_first_order(..)` builds the canonical table: `A_i = ceil(min(a1(ρ_i)/√ρ_i + 0.05,
    1 + 1/(2m)) · √((k_i−1)/n_i) · n_i)` and `q_i = ceil(target / −log2(A_i/n_i))`. This is
    lane/pq-mca-upgrade `bound_mca.py` regime 'F'.
  * It sets each round's query count from the table.
  * The table is serialized into the vk (skipped when absent), so it is bound into the vk
    pre-hash. Default parameters are unchanged: gas-failure5 is still byte-identical,
    `ba042e71…`.
* **Native verifier.** `verify` first runs `check_agreement`: the table must be canonical for
  the schedule, and the round query counts must equal the table's. Otherwise it returns
  `VerifierError::AgreementTableMismatch`.
* **NV circuit.** The program takes the child's query counts from the child vk, whose table
  is a program constant via the pre-hash. The builder also re-checks the table and records a
  failure if it is not canonical.
* **The PQ default is now m = 64 + O-2.** `params_from_env` applies `{prefix}_O2` (default 1),
  and the chain's default `LIST_M` is 64.
* **Test `o2_agreement_table`:**
  * query counts equal the table's, the proof verifies, and NV verifies the O-2 child;
  * an altered A_0 is rejected, both by an engine holding the altered parameters and by the
    honest engine;
  * a weaker but self-consistent table is rejected by the honest verifier, and its vk
    pre-hash differs.
* **To check against the certificates:** the A_i for the real shapes should be checked against
  the DKT certificate grid (lane/pq-dkt-verify).

**NvAir: 55 → 49 interactions per row.** Before this change, 6 of the 55 were the hash role's
word sends on a separate word bus.
* **New source for sampled words.** The sample role now receives its 64-bit word directly from
  GLUE's digest rows. The bus is the digest bus, the key is `8 + word`, and the message is
  `(job, 8+w, 3 limbs, 0, 0, 0)`.
* **GLUE side.** GLUE has new columns `dx[2]`: on the digest rows of untruncated (transcript)
  jobs, each read word is sent once more.
  * Constraints: `dx` is boolean, nonzero only on digest rows (`last·q2·(1−q0q1)`), and zero
    on truncated jobs.
  * The multiplicity is pinned by the bus balance.
  * GLUE's interactions on the digest bus go from 1 to 3, which equals the hash role's 3, so
    the bus maximum does not change.
* **Sample role.** It has a new column `w0`, the run's first word (0 for squeeze or PoW-run
  blocks, 1 for B_1).
  * `is_first·(wi − w0) = 0`, and w0 stays constant within a run.
  * w0 is carried in the t.sample message, and the hash row requires it to equal `op_p`.
    Before, the start word was pinned by the multiset of the hash role's word sends.
* **Hash role.** It no longer sends words. `rdw` stays, only for the last-word / full / count
  constraints.
* **Size.** The bus census is now 49, and NvAir stays at 74 columns. Interactions are
  2^19·49 + 2^19·14 + tables = 2^24.98 < 2^25, so L = 24 (−2.5 KB GKR). The margin is thin:
  NvAir must stay at 49 or below.
* **Test `nv_sample_word_source_tamper`:** a squeeze run starting at word 1 is rejected, and so
  are a dropped word send and an extra word send.
* **Suites:** the NV suite passes in 48-B, 42-B + coset and all-child-levers modes (50 tests
  each), and the backend has 230 tests passing.

**For the re-audit:**
1. GLUE `dx` word sends, which replace the hash role's `rdw`-weighted word bus.
2. The sample run's start pinned by `w0` in the t.sample message, not by the word multiset.
3. The O-2 table check, which is native and Rust-side in the NV builder. The table is a vk
   constant.

The program-binding argument is unchanged.

**New extrapolation** (`extrapolate_nv2.py`: 49 interactions per row, GKR on power-of-two
heights, default regime O-2):

| regime | final |
|---|---|
| m = 3 | 324,003 B |
| m = 64 | 313,807 B |
| **O-2 (U-13)** | **301,157 B** |

The O-2 breakdown is WHIR 219,908, GKR 32,408 (L = 24), relations 43,280 and stacking 5,344.
The final shape is b = 7, k1 = 1, k = 4, log_h 20, log_final 7. The penultimate is b = 6,
n_stack = 17. The remaining 1.2 KB, and more, is expected from SHA AIR v4
(lane/pq-sha384-air3, about −17.5 KB).
