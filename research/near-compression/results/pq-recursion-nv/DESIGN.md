# NV: narrow, fixed-point verifier circuit for SHA-384/Ext12 SWIRL proofs (design, milestone a)

Lane R, 2026-10-17. Inputs:
* measured: the ported OpenVM verifier (`results/pq-recursion-sha384/`);
* corrected size laws: `lane/pq-native-hermetic` `l4-study/models-C/ext2.py`;
* lever spec: `lane/pq-whir-levers` README;
* ×15 domains: `lane/pq-x15-domains` README.

Labels: **[measured]** = run here; **[model]** = ext2/ext laws; **[estimate]** = counted
from the design, not yet built.

## 1. Why the stock layout cannot work [measured]

The ported OpenVM verifier has 46 AIRs and 3,481–3,923 columns, of which 6,714–7,598
are opened values (322–365 KB):
* verifier logic: 37 AIRs, 2,622 columns;
* hash glue: 399 columns;
* SHA: 442 × instances.

Interactions are 18.2M at L = 25.

The columns also cost SHA work in the next level. 7.6k Ext12 openings are absorbed
into the child's transcript, about 3–4k compressions.

## 2. Architecture

| AIR | role | columns (v1 target) | next-row cols | rows | interactions/row |
|---|---|---:|---:|---|---:|
| SHA compression (L3 AIR, swappable; air2 lane) | 2 rounds/row, 44 rows/compression | 442 (air2: ≈250?) | most | 44·N_c | 43 |
| SHA control+range table | 64 rows | 18 | 16 | 64 | 2 |
| byte table | 256 rows | 2 | 1 | 256 | 1 |
| **GLUE** (one AIR) | one row per SHA message word: packer + block chaining + transcript events + leaf/node framing | ≈ 70 | ≈ 30 | 16·N_c | ≈ 16 |
| **ALU** (one AIR) | one Ext12 op per row; operands via memory lookups; program words bound in-circuit | ≈ 88 | 12 (acc) | ≈ 2^16–2^17 | ≈ 16 |
| **total v1** | | **≈ 620 (air2: ≈ 430)** | | | |

**v0, the first working version, reuses the tested hash AIRs as they are**, about 934
columns:
* message packer 45 and block chaining 134;
* transcript hash/observe/sample 123;
* a new Merkle-node AIR, about 85;
* plus SHA, the tables and the ALU.

v1 then merges the glue into one AIR. Correctness, scaling laws and the fixed point
(milestones b and c) are measured on v0. Column-driven bytes are reported for both.

### 2.1 ALU (replaces the 37 verifier-logic AIRs)

Row = one instruction. Columns:
* `a[12]`, `b[12]` (operands), `c[12]` (result);
* program words `P0..P3`;
* about 10 one-hot op flags;
* `mult`, the read count of c;
* `x`, the row index.

Memory is read-only:
* row x writes c at address x, with key (x, c) and multiplicity `mult`;
* operand reads are lookups (A, a) and (B, b). A and B are program words.

There are no other memory columns: no timestamps or write-twice cells.

Ops:
* `MUL`: c = a·b in F[X]/(X^12 − 31).
* `ADD`, `SUB`.
* `CONST`: c = A, as a base-field immediate.
* `LOAD`: c is a free witness. It must be bound by one of the next three ops.
* `OBS1` / `OBS12`: observe c₀ or all 12 coefficients at tidx = P2.
* `SMP1` / `SMP12`: c is the sampled value(s) at tidx = P2.
* `UNIT1` / `UNIT12`: push c₀ or c₀..c₁₁ as framing units of SHA job P2 at unit index P3.
  These are leaf message payloads and digests.
* `JOB`: start SHA job P2 with tag A and push its length-prefix units.
* `BIT`: c₀ ∈ {0, 1}. A chain of BIT rows recomposes an index, which is sampled and then
  range-split. The bit keys (path, level, bit) are offered to the Merkle AIR.
* `ZERO`: assert c = 0. This covers every verifier equality check.

The 12 value-slot messages carry (channel, P2, P3 + k, c_k) on one bus. The transcript
engine and the packer each receive their own channel. So observe, sample and unit share
12 interactions per row.

Constraints:
* MUL: degree 2 per coefficient; flags × (c − f(a, b)), at most degree 3.
* SMP12: binds 12 sampled felts, as in `sample_ext`.

**Program binding (one round-0 commitment, no preprocessed trace).** The program words
are ordinary main columns. NV verifying NV checks that the child's program equals its
own (the fixed point):
1. The child's openings of P0..P3 at the child's batch point r are combined as
   p̂ = Σ_j τ^j·open(P_j). τ ∈ Ext12 \ F is a fixed constant. {1, τ, τ², τ³} is
   linearly independent over F, so the per-row combination is injective on base-field
   words.
2. The parent accumulates acc = Σ_x w_r(x)·(Σ_j τ^j P_j[x]) over its own rows, with
   w_r(x) = L_{x mod 2^l_skip}(r₀)·eq(r_high, x ≫ l_skip). L and E are looked up from
   memory tables that the program computes once r is sampled. The update is degree 3:
   acc' = acc + (L·E)·(Σ τ^j P_j).
3. One `ZERO` row checks acc_final − p̂ = 0.

Cost:
* 36 columns (L, E, acc);
* 2 lookups per row;
* about 2^(h − l_skip) ALU rows for the E table.

The native final verifier checks the final proof's program openings against the fixed
program natively, which is O(|program|) and cheap off-circuit. Induction gives every
level the same program.

The alternatives are worse:
* hashing the program with SHA costs about 1 MB, or about 8k compressions;
* a preprocessed commitment adds one round-0 tree, about 25–45 KB in the final proof
  and about 1.3k in-circuit compressions.

*Base case.* Level 1 verifies an app proof with a different program, so level 2 must
check its child against that program instead. The steady state (level ≥ 3) has
identical programs. The level-2 exception is a mode bit exposed as a public value and
checked natively at the end. This is labelled as a gap until it is implemented.

**Data-dependent control flow is fixed by the program:**
* Query index: SMP1, then BIT rows. The recomposition is a range proof, giving bits
  below log_dom. The points are ω^idx by a fixed square-and-select chain.
* Merkle directions: bit keys into the Merkle AIR.
* Per-round shapes and child trace heights: constants of the program. The program
  asserts the child's observed log_heights, and every NV trace is padded to fixed
  heights so the child shape is constant at the fixed point.

### 2.2 Glue and Merkle (v0: existing AIRs; v1: one AIR)

v0 keeps the tested pieces:
* packer and block chaining;
* the transcript hash-chain, observe and sample engine. The observe/sample AIRs receive
  ALU value-slot messages by (tidx, value, kind) exactly as the verifier AIRs did.

A new **MerkleAir** has one row per node, as a direct compression:
* cur(24), sib(24), out(24), out67(8), bit, cid, path/level;
* L/R selection is inline (degree 2 in the interface message);
* next.cur = out within a path, as a transition with no bus;
* path start receives the leaf digest from the digest bus;
* path end looks up the commitment, which the ALU offers with multiplicity = #paths.

v1 GLUE: one row per message word.
* Columns: 8 bytes, carry, slot flags and kinds, felt-canonical gadget (4), phase,
  uidx, 4-bit position plus 3 derived flags, job, block-chaining state limbs (4), cid,
  and transcript/merkle/role flags.
* Block chaining moves into the word rows: row pos < 8 receives output word pos of its
  compression and forwards it as input word pos of the next block or as the digest.
* Merkle nodes become 16-word jobs.
* About 70 columns at 16 rows per compression, about 1,120 cells per compression
  (+6 % over SHA).

## 3. Budgets per AIR [estimate], for NV verifying NV at the final-layer shape

The shape is the L4-C fixed point: about 5.1–5.7k penultimate compressions, k1 = 1,
k = 4, W ≈ 100.

| item | v0 | v1 | air2 SHA + v1 |
|---|---:|---:|---:|
| opened columns (local) | ≈ 934 | ≈ 620 | ≈ 430 |
| next-row columns | ≈ 700 | ≈ 470 | ≈ 260 (≈ 0.6) |
| SHA compressions | ≈ 5.5k (2^18 rows) | same | same |
| SHA cells | 116M | 116M | (air2 TBD) |
| glue cells | ≈ 20M | ≈ 9M | ≈ 9M |
| ALU rows / cells | ≈ 2^17 / 11.5M | 2^17 / 11.5M | same |
| total cells | ≈ 2^27.1 | ≈ 2^27.0 | ≈ 2^26.6 |
| interactions | SHA 2^23.4 + glue 2^21.5 + ALU 2^21 → L = 24 | L = 24 | L = 24 |

ALU instruction count [estimate]:
* constraint DAG evaluation: about 20k. The measured DAG of the SHA AIR alone is 13,163
  nodes; glue and ALU add about 2–4k.
* WHIR round 0: q0·2^k1·W ≈ 8.8k (Horner, plus units).
* folding: about 10k.
* query points: about 7k.
* final polynomial: about 3k.
* later-round leaf values with units: about 2k.
* transcript observes of column openings and sumcheck polynomials: about 2k Ext12 rows.
* binding tables: about 2^15.
* Total: about 60–90k, so 2^16.5–2^17 rows.

## 4. Modelled final bytes (ext2.final_bytes, gruen on)

Settings: ×15 domain (extra = log2 15), pack 31/32. "L" = z = 32 grinding / 42 B / m = 8
/ target 226. "T" = 268 / 48 B / m = 3.

| circuit | cells | opened cols | next frac | ipc | final L | final T |
|---|---:|---:|---:|---:|---:|---:|
| ported stock (measured cols) | 2^27.9 | 3,481 | 0.93 | 0.10 | 639,645 | 713,697 |
| NV v1, today's SHA | 2^27.0 | 612 | 0.75 | 0.117 | 343,638 | 411,630 |
| NV v1, today's SHA, padding-free cells | 2^26.6 | 612 | 0.75 | 0.117 | 332,028 | 397,927 |
| NV v1 + air2 SHA (≈ 250 cols) | 2^26.6 | 420 | 0.6 | 0.117 | 313,111 | 379,010 |
| NV v1 + air2, 2^26.3 cells | 2^26.3 | 420 | 0.6 | 0.117 | 305,737 | 370,311 |
| NV v1 + air2, next 0.3 | 2^26.6 | 420 | 0.3 | 0.117 | 307,063 | 372,962 |

**Reading:**
* NV removes about 300 KB of column openings compared with the port.
* With NV the final layer is WHIR-dominated: about 225–240 KB at the L settings. The
  rest is GKR 34 KB at L = 24, relations 35–60 KB, and stacking about 6–8 KB.
* Under 300 KB needs all of:
  * air2 SHA, at ≲ 250 columns and fewer cells per compression;
  * total cells ≲ 2^26.3, which means about 5k compressions without power-of-two padding
    (split SHA trace heights are a lever);
  * the L settings;
  * the next-row lever.
* At the T settings no NV variant gets below about 370 KB.

## 5. Plan

* (b) v0 NV verifies a small real child. Debug checker passes, and the 4 tamper classes
  are rejected.
* (c) NV-verifies-NV for 2–3 levels at a low query target. Measure per level.
* v1 glue merge.
* Levers one at a time:
  1. coset leaf;
  2. 42 B digests;
  3. PoW;
  4. k1;
  5. multiproof;
  6. ×15 (exact sampler, a 15-entry point table, +4 depth).
* (d) Extrapolate.
