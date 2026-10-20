# DESIGN-BASE: from a NEAR chunk to one PQ proof (base layer, aggregation, statement)

Lane `lane/pq-base-aggregation`, 2026-10-18. Branched from `lane/pq-recursion-sha384` @ 46b7e62e2.

This document covers what sits under the recursive final layer (NV, `results/pq-recursion-nv/`):
* the base ("app") proofs of chunk validation;
* how 1 Pgas is split into segments;
* the segment statement;
* the aggregation layer;
* the statement digest that the native final verifier V_d checks;
* per-level cost and memory;
* Base-faithful (final-soundness S-22).

Labels:
* **[M]** measured here or in a cited log;
* **[L]** a law fitted to NV measurements (`extrapolate_nv2.py`);
* **[B]** exact: the backend's WHIR schedule as re-derived by `bound.py`;
* **[A]** assumption, listed in §8;
* **[P]** proposal (needs a decision).

Companion files in this directory:
* `README.md`: prototype results and tests;
* `base_bound.py` → `bound-base.out`: S-24;
* `base_agg_model.py` → `model.out`: the cost model.

The code is `native/recursion/patches/openvm-recursion-agg.patch`, an overlay on the recursion lane's
patch, set up with `native/recursion/setup_agg_deps.sh`.

---

## 0. Summary (revised 2026-10-18 after lane/pq-prover-latency d1a208ef7)

**The design is G.** Measured NV recursion costs **≈ 400–1,250 work cell-eq per NV cell** in the mid case
(136–658 optimistic). Zerocheck + GKR of the degree-21 SHA AIR in Ext12 is 94–97 % of a layer
(LATENCY.md §4.3).

My first version assumed 4–30. At the measured cost, every design with recursion levels per segment group
is out of real time: T8 ≈ 87 s (LATENCY.md), and T2 / H are worse. The pipeline is therefore:

> one shared-transcript base proof over all GPUs (PERF P-PERF-4) → L1 → T1 → T2 → FINAL

LATENCY.md puts it at 5.7 s mid / 1.6 s optimistic after execution, at adversarial 1 Pgas on 32 H200, with
a 2.6 s mid tail.

**Does G need an n-to-1 NV layer? Only at L1, and only for side proofs.**
* **No layer per segment.** In G the segments are GPU slices of one proof with one transcript. Continuity
  between segments (state, memory, timestamps) is a set of ordinary global-bus terms of that single proof,
  as in PERF §5.2.
  * There are no per-segment statements, no boundary digests and no continuity checks in a verifier
    circuit.
  * The base proof's public values are the chunk statement itself: ctx, enc S_0, enc S_S. L1 hashes them
    under tag 8, exactly as in the recursion lane's G1 passthrough. Intermediate boundaries never leave
    the proof.
  * A digest over segments inside the base proof would add in-AIR SHA work and buy nothing.
* **L1 is k-to-1 only if independent side proofs exist.** The candidates are P-PERF-8's early PREP and
  code-hash sub-proofs, which start at t = 0 because contract code is known at chunk start.
  * L1 then verifies the main base proof plus those sub-proofs, each on its own transcript, and checks
    cross-proof links. Example: the PREP proof's code-table commitment equals the one the main proof's
    FETCH table uses.
  * This is exactly the level-1 capability the prototype provides: no program binding (children are
    base-layer proofs), linear cost, heterogeneous vks.
  * **Built and tested: `build_l1_linked`** (`agg_g_l1_linked`). An honest main + sub-proof pass the
    debug check. A main proof using a different commitment than the sub-proof proves is rejected, and so
    is a tampered statement limb.
* **The range-statement tree** (segment statements, N1/N2, tag 9) **stays as the fallback.** It is for
  configurations a single transcript cannot span, such as several clusters or failure isolation. It is
  not on the real-time path.

**Grinding: z = 24 on base and inner layers, z = 32 on the final layer** (LATENCY.md §5.3: a per-segment
z = 32 would cost 697 GPU-s). `bound.py` re-run with that split
(`base_bound.py`, `bound-base.out`; uniform z = 32 kept in `bound-base-z32.out`):
* base seg-v1 queries become [536, 256, 83, 50, 36];
* inner NV becomes [52, 47, 34, 27];
* worst move: base round-0 query, 2^−268.20;
* **total 2^−134.88: PASS**. The 7-layer union is 2^−132.08.

The query move is target-calibrated (q·log α − z ≈ −268), so lowering z raises q, not the error.

In design G the chain has ≤ 5 + (number of side proofs) proofs. Even the conservative per-proof union then
passes (2^−132), so the tree caveat of §9.1 does not arise.

**Pinned base parameters** (§3):
* c = 1, b = 1, m = 16, k₁ = 1, k = 4;
* stacked height 2²⁴ per GPU slice, W ≤ 24;
* ≤ 32 AIRs, degree ≤ 8, interactions ≤ 2²⁸;
* 42-B digests, z = 24, target 268, T\*.

In G the global proof has W ≈ 690 at 2²⁶ (or slices stacked per GPU, PERF §5.2). The bound terms do not
depend on W at this size.

**Unchanged findings:**
* k-to-1 is cheap at level 1: 0 extra columns, per-child rows equal to the 1-ary verifier.
* It is quadratic at levels ≥ 2 because of in-circuit program binding.
* The final proof size is independent of aggregation.
* Base-faithful (§10) is open for any real segment AIR set.
* Independent proofs must cut at receipt boundaries (§2.3).

The sections below keep the original analysis. Where a figure was superseded, it is marked
**(superseded)**.

---

## 0a. Original summary (superseded where marked)

* **Statement chain.**
  * A chunk claim fixes an initial boundary state S_0 (from the pre-state root and the chunk inputs) and a
    final one S_S (post-state root, outcome and receipt roots, gas, balance burnt).
  * Segments j = 0..S−1 each prove "S_j → S_{j+1} by the NEAR chunk-validation transition, restricted to
    segment j". Their public values are (ctx, j, enc S_j, enc S_{j+1}).
  * Aggregation nodes check continuity and hash the range statement
    D = SHA-384₄₂(tag 9, [ctx, a, e, S_a, S_e]).
  * Above the root, NV passes D through unchanged.
  * V_d checks D = D(ctx(claim), 0, S, enc S_0(claim), enc S_S(claim)) (§6).
* **Base AIR set.** On SWIRL/Ext12/SHA-384 (§2), one segment AIR set holds:
  * the WASM machine chips of V3-PERF-DESIGN §2.3;
  * the NEAR host/trie tables of `nearAirV3`/`nearAirV3D1`, ported from the classical stack;
  * a SHA-384 table for boundary digests.

  Only the 3-table direct-Wasm slice (gas-failure5) exists on the PQ stack today. The rest is a port.
* **Segment size.** 2²³ WASM ops (≤ 2^28.25 main cells). At adversarial 1 Pgas that is **S = 146**
  segments. A typical-mix chunk needs about 4× fewer [A].
* **Pinned base parameters** (§3):
  * c = 1, log_blowup b = 1 (rate 1/2), m = 16, k₁ = 1, k = 4;
  * stacked height 2²⁴, W ≤ 24, ≤ 32 AIRs, degree ≤ 8, interactions ≤ 2²⁸;
  * 42-B digests, z = 32, target 268, T\*.

  Queries [518, 247, 80, 48, 34].

  **`bound.py` PASSES: 2^−134.68** with these parameters (worst move: the base WHIR round-0 query, at
  2^−268.00). The conservative 7-layer union is 2^−131.87. A per-proof union over a whole 295-proof tree
  would give 2^−126.5, which fails. So the tree claim relies on the single-database theorem (§9.1).
* **Aggregation.** k-to-1 inside NV is practical at **level 1** (children = base proofs, no program
  binding). Measured on the prototype:
  * per-child program rows equal the 1-ary verifier's (9.2k per child at test parameters);
  * the circuit is unchanged at 73 / 171 / 13 / 5 columns, degrees 8 / 21 / 4 / 3;
  * the multi-transcript change adds no column.

  At **levels ≥ 2** the in-circuit program binding needs one BIND pass over the parent's program per
  child, which is quadratic in k. So the minimal tree is **2-to-1 with two BIND regions**. A k-ary node at
  levels ≥ 2 needs a preprocessed program commitment (linear in k), §5.3.
* **(superseded: A-4 was 1–2 orders of magnitude too low; see §0 and §7)** Latency at adversarial 1 Pgas on 32 H200, after execution (`model.py`, §7):

  | design | latency (s) |
  |---|---:|
  | G: one shared-transcript base proof (PERF P-PERF-4) → NV chain | 1.97 / 2.20 / 2.98 |
  | T8: wide tree (8-to-1, then 4-to-1 preprocessed) | 2.27 / 2.86 / 4.84 |
  | H: 4 machine ranges | 2.52 / 2.84 / 3.91 |
  | T2: binary tree | 3.65 / 6.21 / 14.72 |

  The three figures are for 4 / 10 / 30 work cell-eq per NV cell; that number is unmeasured.

  **The base proof alone is 1.73 s after execution.** SWIRL at Ext12 costs ≈ 546 cell-eq per adversarial
  op, against 281 in PERF's univariate design. So ≤ 2 s holds only for design G, and only if NV cells are
  cheap. That is the largest risk (§11).
* **Final proof size is unchanged by aggregation.** The tree feeds the same NV fixed point that the final
  layer verifies. The final layer always verifies an inner NV proof of the fixed-point shape (§5.4).
* **Base-faithful** (§10): lemma stated.
  * Existing pieces: the D0a AIR→relation extraction on the classical stack (`ExtractV3Stmt`), the
    4-opcode Wasm-slice theorem on the PQ stack, the segment-fold lemma `run_foldSegments`, and the
    three-way difftests.
  * Missing: everything that ties the SWIRL segment AIR set to the segment relation, plus the
    receipt-level fold.

---

## 1. What is proven, end to end

```
claim C = (chunk header ctx, pre-state root, receipts in, ..., post-state root, outcomes, gas, burnt)
          │ native V_d computes   ctx(C), enc S_0(C), enc S_S(C)
          ▼
final proof π_d ──NV chain (passthrough)── root of aggregation ──...── node: D(ctx, a, e, S_a, S_e)
                                                                           │ checks ctx_i = ctx, a_{i+1} = e_i,
                                                                           │ S_a(i+1) = S_e(i); hashes (tag 9)
                                                         segment proofs j: public values (ctx, j, S_j, S_{j+1})
                                                                           │ Base-faithful (§10)
                                                         T_j ∈ R_seg  ⇒  S_j →_{segment j} S_{j+1}
```

Soundness composes as in final-soundness Theorem 7.4, extended to trees (§9.1):
1. one QROM database;
2. straight-line extraction node by node, down to the leaves;
3. A-IC(τ) at every NV node;
4. Base-faithful at every leaf;
5. continuity plus range digests give the folded transition S_0 → S_S, and `run_foldSegments` turns that
   into the chunk relation.

---

## 2. Base layer: the AIR set that proves a segment

### 2.1 Proof system

The base proof is a SWIRL proof on the unified backend: BabyBear, Ext12, SHA-384 with T\*, GKR LogUp,
univariate-skip zerocheck, stacked WHIR. It is the same stack NV verifies.

NV can only verify proofs of this backend. A univariate/FRI base, which is PERF-DESIGN's choice, would need
a second verifier circuit. §11 R1 discusses why that might still be worth it.

### 2.2 AIR families of segment AIR set "seg-v1" [P]

| family | tables | source (definition) | on the PQ stack today |
|---|---|---|---|
| WASM machine | STATE, FETCH (code table), ALU32/64, MUL (byte limbs), DIV, SHIFT/ROT, CMP, MEM (offline memory checking, timestamps), CALL/RET frames, BULK (copy/fill), stack-temporary channels | V3-PERF-DESIGN §2.3 (spike-4 layouts, measured on the classical prover) | only i32.const/add/drop/end: direct-Wasm EXEC 157 / CODE 114 / RANGE 24 columns, 3 AIRs (gas-failure5) **[M]** |
| ranges | RANGE16, RANGE-T (2²⁴), PAIR8, BYTEOP | PERF §2.3 | RANGE (direct-Wasm) |
| NEAR host + runtime | registers, storage read/write (trie walk: `walkV3`/`walkU`, `nodeD1`, `valA7`/`uvalV3`, `nmemV3`, `uniqD1`), receipts and promises (`rcptV3D1`), accounts and balances (`acctTableV3`), access keys (`akmV3`), tx (`txV3`), Ed25519 (D1a native), sort, Merkle-empty | `nearAirV3` (25 tables, `NearAirDefs.lean:91`), `nearAirV3D1` (33 tables, `NearAirD1Defs.lean:60`) | **no**: classical `np-udr-stark-v2` only |
| NEAR's own hashes | SHA-256 (trie node hashes, code hash, `sha256` host function) | `shaTable` (D0a) | no (the PQ stack has SHA-384 only) |
| boundary digests | SHA-384/512 family table (U-7: D1's SHA-512 table generalised) hashing enc S_j and enc S_{j+1}, plus ctx | new | the NV SHA AIR v2.1 (171 columns, degree 21) is reusable |
| contract preparation | PREP code-table proof per contract version (P-PERF-8) | PERF §3.4 | no |

**NEAR's data hashes stay SHA-256.** Trie node hashes are part of NEAR's state format. U-7 (SHA-384) applies
to the *proof system's* hashing: commitments, Fiat–Shamir, recursion, and the boundary digests introduced
here.

**FETCH needs a per-contract code table.** PERF makes it a preprocessed commitment. NV supports neither
preprocessed nor cached children today (`build_verifier` asserts it). So either:
* NV learns preprocessed children (also needed for §5.3); or
* the code table becomes a main-trace table bound to the code hash by the PREP sub-proof.

This is a hard dependency (§11 R4).

### 2.3 Segment boundaries: two kinds [P]

1. **Receipt (function-call) boundaries.** NEAR instantiates fresh Wasm memory per function call. At a
   receipt boundary the machine state is empty and the boundary state is small:
   * trie root;
   * receipt cursor;
   * outcome, outgoing-receipt and log accumulators;
   * gas and balance counters.

   Placing segment boundaries here costs only the digest of a few hundred bytes (§4).
2. **Intra-call boundaries.** These are needed because one call can be ≤ 300 Tgas [A], about
   3.6·10⁸ adversarial ops, which is far more than one segment. The boundary state then includes the
   Wasm machine:
   * pc, frames, operand stack (≤ 256 KiB), globals;
   * linear memory (≤ 64 MiB initial, lazily zero).

   There are two ways to carry it:
   * **inside one shared-transcript proof** (designs G/H): memory continuity is ordinary global-bus terms
     (PERF §5.2), and nothing is hashed;
   * **across independent proofs** (designs T): the memory must be committed. A page-Merkle root costs
     touched pages × page bytes of in-AIR SHA-384 per boundary. At PERF's bound of ≤ 512 dirty 64-KiB pages
     per segment, that is up to 32 MiB ≈ 262k compressions ≈ 10¹⁰ cell-eq per boundary. This is ≫ the
     segment itself (≈ 4.6·10⁹).

   **Independent proofs should therefore cut only at receipt boundaries, or at intra-call points with
   small dirty sets.** Only designs G and H handle arbitrary intra-call splits cheaply.

### 2.4 Segment size and count at 1 Pgas

| quantity | value | label |
|---|---|---|
| adversarial pure-Wasm 1 Pgas | 1.22·10⁹ ops | study §10.1 [A] |
| main cells per op (SWIRL: no aux, no quotient) | 10 / 21 / 38 (typical / mainnet-like / adversarial) | PERF §4.6 [A] |
| work per op, SWIRL at E = 12 | 98 / 207 / 455 × 1.2 = 118 / 248 / 546 cell-eq | PERF §4.6 × 12/10 [A] |
| segment | 2²³ ops, ≤ 2^28.25 main cells; stacked at 2²⁴ rows ⇒ W ≈ 19 (pinned ≤ 24) | [P] |
| segments at adversarial 1 Pgas | S = 146 | — |
| base work | 94 GPU-s ⇒ 2.93 s on 32 H200, 1.73 s after the 1.2 s execution (GPU-bound, streaming) | [A] rate 7.1 G cell-eq/s/GPU |
| memory per segment proof | main 1.2 GiB; LDE (2×) 2.4 GiB; GKR buffers ≈ 2^27.3 fractions × 48 B × 2 ≈ 15 GiB | [A] |

In design G, "segment" means a GPU slice of one shared-transcript proof (≤ 2²⁴ rows per table per GPU, as in
PERF §5.2). The same size works there.

---

## 3. Pinned base-layer parameters (S-24) [P, checked by `base_bound.py`]

| parameter | value | why |
|---|---|---|
| field / extension | BabyBear, Ext12 (X¹² − 31) | U-7/U-10 stack; NV arithmetic |
| hash, digests | SHA-384, T\* transcript, 42-B Merkle digests, 48-B FS state | U-7, U-10, G-1/G-2 |
| l_skip, n_stack | 2, 22 (stacked height 2²⁴) | W small ⇒ cheap round-0 leaves in the verifier |
| stacked width W | ≤ 24 | adversarial segment 19.0 |
| AIRs / degree / constraints / opened columns | ≤ 32 / ≤ 8 / ≤ 2¹⁴ / ≤ 1024 (incl. rotations) | PERF degree ≤ 3; 8 covers direct-Wasm EXEC (5) |
| interactions, message length | ≤ 2²⁸, ≤ 16 | 19 fractions/op adversarial ⇒ 2^27.25 |
| commitments | 1 (common main; no preprocessed) | current NV restriction |
| WHIR | c = 1, b = 1 (rate 1/2), m = 16, k₁ = 1, k = 4, final length 2⁷, keep-domain, WHIR-Y, multiproof, coset leaves, z = 32, target 268 (236 query bits) | base LDE 2× (PERF: base rate 1/2); m = 16 recovers query bits at rate 1/2 |
| queries per round | **[536, 256, 83, 50, 36] at z = 24** (current); [518, 247, 80, 48, 34] at z = 32 [B] | — |
| grinding | **z = 24** on base, node and inner layers; z = 32 only on the final layer | LATENCY.md §5.3 |

**`bound.py` result, z split (current)** (`bound-base.out`): ε_rbr = 2^−268.20 (base round-0 query), total ≤ **2^−134.88, PASS** (7-layer union 2^−132.08); inner NV at z = 24 has queries [52, 47, 34, 27]; L1 of design G (NV AIRs, c = 1, b = 3, m = 8) [173, 128, 63, 42, 31].

**`bound.py` result, uniform z = 32** (`bound-base-z32.out`, `bound.py` @ f8c168f98, run via `base_bound.py`):
* worst move: base round-0 WHIR query, 2^−268.00;
* ε_rbr = 2^−268.00;
* total ≤ **2^−134.68**, **PASS**; the conservative 7-layer union is 2^−131.87.

The final and inner NV shapes still reproduce the backend schedules ([42, 38, 31, 26] and [50, 46, 33, 26]).

Alternatives checked (all PASS; `bound-base.out`):

| shape | queries | worst move | base LDE vs pinned |
|---|---|---:|---:|
| c = 1, b = 2, m = 8 | [259, 168, 70, 44, 32] | 2^−268.35 | 2× |
| c = 15, b = 0, m = 8 | [127, 100, 55, 38, 29] | 2^−268.60 | 7.5× |
| gas-failure5 vk at U-10 (c = 1, b = 7, m = 3) | [73, 63, 45, 35] | 2^−269.22 | — |
| N1 node (NV AIRs, b = 3, c = 15) | [74, 64, 42, 31] | 2^−270.79 | — |
| N2 node (NV AIRs, inner settings) | [50, 46, 33, 26] | 2^−268.55 | — |

* Every PIOP and field term of the base shape is ≤ 2^−359. Ext12 makes them irrelevant. Only the
  target-calibrated WHIR query moves matter.
* The trade is base LDE cost (×2 per blowup bit) against verifier queries (N1 cost ∝ Σq). At rate 1/2 the
  pinned shape spends 927 queries. That makes one segment cost 2^28.0 NV cells to verify [L], against
  2^26.1 for an inner NV child.
* b = 2 halves the queries for 2× base LDE. Pick it if node levels end up on the critical path more than
  base LDE (design T).

---

## 4. Segment statement

Public values of segment j (AIR 0), as base-field felts:

| field | encoding | felts |
|---|---|---|
| ctx | chunk context digest: SHA-384₄₂ (tag 9 domain) of the chunk header fields the transition reads (chunk hash / tx root, prev state root, block height/timestamp/gas price, epoch, protocol version, receipts-in root); 18 limbs (NV digest format) | 18 |
| j | segment index | 1 |
| enc S_j, enc S_{j+1} | boundary state, below | 2 × n_state |

**Boundary state S, receipt boundary [P].** Each field is in limbs:
* trie root (SHA-256, 16 × 16-bit);
* receipt cursor;
* outcome accumulator, outgoing-receipt accumulator and log accumulator (SHA-384₄₂, 18 each);
* gas used and balance burnt (u64/u128 limbs);
* flags (halted).

That is n_state ≈ 90 felts.

**Intra-call boundary.** Add a machine-state digest (pc, frames, stack, globals, memory root) when the cut
is between independent proofs (§2.3).

**Node statement.** D(ctx, a, e, S_a, S_e) = SHA-384(prefix, tag 9, [n_ctx, n_state, ctx, a, e, S_a, S_e]),
truncated like Merkle digests (42 B under the lever).
* It sits in the narrow-leaf oracle class of Lemma 1.1, together with tags 0 and 6.
* The lengths make the encoding injective.
* At n_state = 90 the message is ≈ 800 B, 7 compressions.

Relation to the recursion lane's passthrough: its level 1 hashes an app proof's public values under tag 8.
In this design, level 1 (N1) computes tag-9 range digests instead. Above the root the digest is passed
through exactly as in G1. For a one-segment chunk, N1 runs with k = 1.

---

## 5. Aggregation layer

### 5.1 Node kinds

| node | children | binding of the children's program | statement work | cost |
|---|---|---|---|---|
| **N1** (level 1) | k₁ ≥ 1 segment proofs | none needed: children are base proofs, whose vk pre-hash and params are program constants (F2) | reads the children's public values from their transcripts; checks continuity; hashes the range digest | k₁ × (1-ary verifier) [M: linear] |
| **N2** (2-to-1) | 2 NV proofs (N1 or N2) | one BIND pass per child over the parent's program (E1/E2 tables at each child's point r_j) | witnesses the children's preimages, hashes them in-circuit and compares with the children's D; continuity; output D | ≈ 2 × (1-ary) + one extra BIND region (prog/2 rows) |
| **N2×k** (k-ary, levels ≥ 2) | k NV proofs | **preprocessed program commitment** (vk constant) instead of BIND: + ≈ 1.3k compressions per child (Merkle paths of the extra tree) | same | linear in k |
| **T1** (top) | 1 node proof | app-table binding (the existing ACC2 mechanism, against the node program) | passthrough | as NV |

**Why k-ary is quadratic with BIND.**
* BIND evaluates the parent's own program multilinear at the child's random point r_j. Each child brings
  its own r_j, so each needs a full pass of prog/2 rows.
* The parent's program itself grows ∝ k. So BIND rows ∝ k²/2 × (1-ary program).
* At k = 2: BIND = program, and the node is ≈ 2× the 1-ary node. At k = 4: BIND = 2 × program.

**Multi-point batching** (Σ_j ρ^j P(r_j) in one pass) would need k E-table pairs per BIND row, i.e. ≥ 24k
pool columns. The preprocessed commitment is cheaper.

### 5.2 Transcripts and chain starts (prototype, measured)

Each child's verifier runs on its own Fiat–Shamir transcript.
* **Builder.** `restart_transcript()` closes the open flush job, resets the sponge to the initial state, and
  records the start tidx. tidx and job ids stay global and unique.
* **Hash-chain role.** A row may start a chain anywhere (`is_first`). Its input state is the initial-state
  constant, and its t_start is no longer forced to 0. The previous row has no successor (`hn = 0`), so the
  chain bus is balanced.
* **Binding.** The ALU declares chain starts: the anchor of a chain's first job carries P3 = 1, and the hash
  row receives `(…, t_start, cnt, is_first)`. The number and position of chain starts are therefore program
  constants, and they are bound like every other program word.
* **Cost.** 0 columns. The tamper tests show that both removing a start and forging one are rejected.

### 5.3 Tree shapes and how they feed the NV chain

* **T2 (binary).** N1(k₁ = 2) → ⌈log₂(S/2)⌉ = 7 levels of N2 → T1 → T2 (inner NV fixed point) → FINAL. That is
  11 levels on the critical path.
* **T8 (wide).** N1(k₁ = 8, linear) → 3 levels of N2×4 (preprocessed program) → T1 → T2 → FINAL. That is
  7 levels.
* **H (machine ranges).** Each 8-GPU machine proves one contiguous range as a shared-transcript proof
  (P-PERF-4 inside the machine). Then H1 = N1(k = 4, linear) → T1 → T2 → FINAL.
* **G (no aggregation).** One shared-transcript base proof over all 32 GPUs (PERF P-PERF-4). L1 = NV over one
  child → T2 → FINAL. The statement is then the chunk statement itself: public values hashed under tag 8,
  as in G1.

### 5.4 Effect on the final proof

* The final layer verifies an NV proof of the inner fixed-point shape (T2), and T2 verifies T1 by
  app-table binding.
* None of T1's or T2's shapes depends on S or on the tree. So the final proof size is the NV lane's figure
  (299–324 KB by its current model), unchanged.
* What aggregation adds is levels before the fixed point, and their latency.

---

## 6. Final statement digest checked by V_d

V_d (native) receives the claim C and π_d. It checks:
1. π_d verifies under vk_d (final domain, U-12);
2. level and program as in final-soundness §7.1;
3. NvAir public values 1..19 = **D(ctx(C), 0, S, enc S_0(C), enc S_S(C))**, where:
   * S_0(C) is the receipt-boundary state "before the first receipt of the chunk": trie root = prev state
     root, empty accumulators, zero gas;
   * S_S(C) is "after the last": post-state root, the outcome / outgoing-receipt roots derived from the
     accumulators, gas used, balance burnt, halted.

S, the segment count, is part of the digest preimage and supplied by the prover. A short tree (a dropped
last segment) names a different S_e and fails (tested: `agg_chain`).

The prototype's native check is `agg::check_range_statement(pvs, &RangeStmt)`.

---

## 7. Prover time and memory per level

**Current (design G).** Use LATENCY.md (lane/pq-prover-latency, d1a208ef7). It measures NV layer cost
(zerocheck + GKR dominate) and distributes each tail layer over the GPUs. At adversarial 1 Pgas, after
execution:

| | 8 H200 | 16 H200 | 32 H200 |
|---|---:|---:|---:|
| optimistic / mid / pessimistic (s) | 8.9 / 20.9 / 68 | 4.3 / 12.3 / 46 | 1.6 / 5.7 / 23 |

* The tail is 2.6 s mid (0.8 s optimistic) at 32 H200.
* The largest remaining lever is the SHA AIR's zerocheck: degree 9 gives a 1.84 s mid tail.
* `model.out` was re-run with the measured 140 / 400 / 1,250 cell-eq per NV cell. It puts every node on
  one GPU, so its absolute numbers overstate G: 7.3 / 17 / 50 s.
* It is kept for the **ratios** between designs at equal node placement, at 400 cell-eq per NV cell:

  | design | after execution (s) |
  |---|---:|
  | G | 17 |
  | H | 24 |
  | T8 | 41 |
  | T2 | 109–172 |

  Trees stay 2.4–10× worse than G.

### 7.0 Original table (superseded: A-4 = 4–30 cell-eq per NV cell)

All figures are [A] model outputs at adversarial 1 Pgas on 4 × 8 H200 at 7.1 G cell-eq/s per GPU (PERF,
35 % of peak). Each latency cell is the 4 / 10 / 30 cell-eq per NV cell triple.

Tree nodes prove at c = 1, b = 3, m = 8 (LDE 8×). The inner-NV settings (c = 15, b = 6, LDE 960×) need
0.6–7 TiB of LDE per node, which is infeasible on one GPU without streaming.

| level | NV cells [L] | GPUs | memory (trace / LDE) | time (s) |
|---|---:|---:|---|---|
| segment proof (base) | 2^28.25 main | 1 per segment, 146 total | 1.2 / 2.4 GiB + GKR ≈ 15 GiB | 0.64 each; 1.73 after execution in aggregate |
| N1, 2 segments | 2^28.94 | 1 | 1.9 / 15 GiB | 0.31 / 0.74 / 2.19 |
| N1, 8 segments | 2^30.93 | 8 | 7.6 / 61 GiB | 0.27 / 0.63 / 1.85 |
| N2 (2-to-1, BIND ×2) | 2^28.28 | 1 | 1.2 / 10 GiB | 0.20 / 0.48 / 1.40 |
| N2×4 (preprocessed) | 2^29.16 | 8 | — | 0.06 / 0.13 / 0.37 |
| L1 (G: one global child, W = 690) | 2^28.73 | 8 | — | 0.07 / 0.15 / 0.42 |
| H1 (4 machine ranges) | 2^30.26 | 8 | 4.8 / 38 GiB | 0.11 / 0.24 / 0.68 |
| T1 / T2 / FINAL (NV fixed point) | 2^26.13 | 1 | (recursion lane) | 0.06 / 0.12 / 0.33 each |

| design | critical path after execution (s) |
|---|---|
| G | 1.73 + L1 + 3 tail = **1.97 / 2.20 / 2.98** |
| T8 | 1.73 + 4 node levels + 3 tail = 2.27 / 2.86 / 4.84 |
| H | 2.22 (ranges sized 0.29 / 0.26 / 0.24 / 0.21 to finish together; contiguous ranges execute in order) + H1 + 3 tail = 2.52 / 2.84 / 3.91 |
| T2 | 1.73 + 8 node levels + 3 tail = 3.65 / 6.21 / 14.72 |

Reading:
* The base dominates.
* Design G has the shortest tail, but needs a cluster-wide SWIRL prover: global sumcheck rounds as
  all-reduces over InfiniBand, and one WHIR commitment over all GPUs.
* T8 is the best design that uses independent proofs. Its N2×4 needs preprocessed children in NV.
* T2 (the minimal NV change) is too slow on the critical path.
* H loses ≈ 0.5 s to the sequential order of contiguous ranges.

Measured prototype numbers (CPU, test parameters) are in `README.md`.

---

## 8. Assumptions

* **A-1** 1 Pgas adversarial = 1.22·10⁹ Wasm ops (study §10.1), with execution 1.2 s including
  checkpointing (PERF §1).
* **A-2** SWIRL main cells and work per op are PERF §4.6's ML figures (98 / 207 / 455 cell-eq at E = 10),
  scaled ×1.2 for Ext12. Unmeasured on SWIRL.
* **A-3** GPU rate 7.1 G cell-eq/s per H200 (35 % of peak INT32; PERF §0). There is no H200 measurement.
* **A-4 (superseded)** NV prover work per NV cell was assumed to be 4–30 cell-eq.
  * **Measured/modelled by lane/pq-prover-latency: 400–1,250 (mid), 136–658 (optimistic).**
  * The degree-21 SHA AIR's zerocheck dominates, as stated below.
  * Measured on CPU, the NV prover runs at ≈ 3.7 k cells/s per thread, against 16 M for PERF's calibrated
    LDE.
  * **No GPU NV prover exists.**
* **A-5** Per-level overhead 20 ms.
* **A-6** Segment AIR set seg-v1 fits the pinned bounds (§3). Its constraint DAG evaluation in NV is within
  the measured fixed part (≈ 72k rows incl. NV's own DAG).
* **A-7** One NEAR function call is ≤ 300 Tgas (prepaid-gas limit). To be checked against the pinned nearcore
  config.
* **A-8** The boundary-state encoding is either injective felts or SHA-384 digests computed in the segment
  AIR (§10, BF3).
* **A-9** The tree composition theorem (§9.1) holds as sketched. The conservative per-proof union fails at
  295 proofs.

---

## 9. Soundness of the tree

### 9.1 Theorem 7.4 for trees (sketch; to be written in final-soundness)

Generalise `dec_i` to `dec_v(T) = (π_{c_1}, …, π_{c_k})` for node v with children c_1..c_k, and replace (F3)
with:

> **(F3-tree)** x_v's digest = D(ctx, a_{c_1}, e_{c_k}, S_a(c_1), S_e(c_k)), and for each child
> x_{c_i}'s digest = D(preimage_i), with ctx and adjacency equal as checked.

The induction of Theorem 7.4 step 2 runs over the tree in any top-down order. Its ingredients are:
* one database;
* every accepting transcript in D extractable;
* A-IC at every node.

The error stays (t′G + √(ℓ_V/2³³⁶))². It depends on the family maximum ε, not on the number of nodes.

Two caveats:
1. t, the total query budget, includes the honest-size work of every node. 2⁶⁴ is far above it.
2. **The conservative per-proof union bound, which the current text uses as a cross-check, fails for
   trees.** A 295-proof tree gives 2^−126.5 > 2^−128. So the tree claim needs Theorem 6.4's
   single-database form. Alternatively, raise every layer's target by ≈ 8 bits.

### 9.2 Statement binding

* Continuity is exact equality of felts in-circuit.
* The digest step needs collision resistance of the in-circuit SHA-384 (tag 9, 336 bits). Under A-IC these
  evaluations are oracle evaluations, and the CMS19-style bound t³/2³³⁶ applies (U-10).
* Swapped, dropped, duplicated and foreign children fail adjacency or ctx.

---

## 10. Base-faithful (S-22)

### 10.1 Lemma (required form)

Let vk_seg be the pinned segment vk (AIR set seg-v1, §3), with public values
x = (ctx, j, h, h′) ∈ F^{18+1+2·n_state}.

**Lemma 7.2-seg (Base-faithful).** For every x and every trace T ∈ R_{vk_seg}(x), the relation of
final-soundness §1.2:
* constraints vanish on every row, including the zero rows beyond tight heights;
* every bus balances mod p;
* no program columns.

there exist a prepared chunk context p and boundary states s, s′ such that:
1. `prepChunk ctx = .ok p`, where ctx is the preimage of the ctx digest;
2. `enc s = h` and `enc s′ = h′`;
3. `segRel p j s s′`: s′ is reached from s by the NEAR chunk-validation transition restricted to segment j.
   * Within a function call: `seg cfg p k s = .cont s′` (or `.fin s′` at the call's end), with
     k ≤ K_seg = 2²³ (`Wasm/Segment.lean`).
   * Across receipts: the receipt-application step of the spec, applied to the receipts of segment j.

**Lemma 7.2-chain (composition, no AIRs).** Suppose:
* `segRel p j s_j s_{j+1}` for j < S;
* `s_0 = init C`;
* `s_S = final C`.

Then the chunk relation holds for C:
* the D0a/D1/D3α relations, by `run_foldSegments` within calls;
* a receipt-level fold lemma across calls.

Together with §9 this yields final-soundness Lemma 7.2.

### 10.2 Obligations and what exists

| # | obligation | exists | missing |
|---|---|---|---|
| BF1 | **AIR ⇒ segment relation.** `HoldsP seg-v1 pub T → segRel …` | D0a analogue on the classical stack: `ExtractV3Stmt` (`NearAdmission.lean:98-110`), composed into `nearV3_admission_final` (`AdmissionV3.lean:48`); no sorry or extra axioms (audited). PQ stack: `packed_literal_family_public_run_call` (`PackedLiteralFamily.lean:43`), direct-Wasm 3 tables ⇒ `runCall … = .done` for i32.const/add/drop/end, one function, ≤ 8 stack slots | everything for the WASM machine chips; D1a's `nearV3D1_admission_final` (planned, `V3-D1-PHASE2.md` §1: A7D1Step, LinkD1CoreStmt, F1, R1/R2, A1 open); host-function chips; memory channels (P-PERF-5 soundness sketch only) |
| BF2 | **SWIRL relation ⇒ Lean AIR semantics.** R_{vk} (symbolic constraints/interactions in the vk; mod-p bus balance; zero rows) ⇒ `HoldsP` (`ZkFormal/Air/Basic.lean:86`) | classical: the deployed verifier `npVerifierP challengeSpecD0a nearAirV3` is Lean-checked against the Lean AIR; mod-p ⇒ multiset needs multiplicity bounds: `nearAirV3D1_sizeMaxAligned`, `multBound` 896,319,520 < p (`NearAirD1Check.lean`); `nearAirV3D1_wf` (degree ≤ 16) | (a) an equality check between the Rust SWIRL vk (symbolic DAG, interactions, widths) and the Lean `Air`, by codegen or a certificate (cf. `air-program-certificates`); (b) zero-row inertness under tight heights (F5 analogue); (c) the public-value layout = x; (d) multiplicity bound < p for seg-v1 |
| BF3 | **Boundary encoding.** enc injective, or digests binding | — | choice of enc; if SHA-384 in the AIR, collision resistance of concrete SHA-384 (standard assumption), or treat it under A-IC |
| BF4 | **Spec link and folds.** segRel = `NearSpecV3` step semantics; fold across receipts | `seg`, `foldSegments`, `seg_add`, `run_seg`, `run_foldSegments`, `foldSegments_stop` (`spec/lean/v3/NearSpecV3/Wasm/Segment.lean:43-108`); `runCall` (`Wasm/Exec.lean:447`) | receipt-level fold lemma; `prepChunk` / ctx digest definition; init C / final C as functions of `ClaimV3` (`ClaimV3.lean:67`) |
| BF5 | **Conformance.** The spec is the reference behaviour | three-way difftests (nearcore / Lean / Python): D0a 421 cases, 0 disagreements; D1 257 fixtures (1,053 checks); D1, D2, D3α spec ladder, 0 disagreements (HANDOVER) | difftest of segRel at segment granularity (split points, boundary encodings) on D3 fixtures; a fixture exercising a stub / `nmemV3` query (HANDOVER: none yet) |
| BF6 | **Prover completeness** (not soundness) | D0a prover; live run: CONFORMANCE rejection on `applied_receipts_hash` validation (HANDOVER §0a) | the same full-witness validation for the segment prover |

**Status.** BF1–BF4 are open for seg-v1. The classical D0a pipeline shows the shape of each obligation and
proves them for a smaller AIR (no contract code). The only PQ-stack theorem covers a 4-opcode slice. S-22
stays **relies-on-unreviewed / open**.

---

## 11. Risks (ranked; revised)

* **R0 (new, decisive)** Recursion layers cost ≈ 400–1,250 cell-eq per NV cell (LATENCY.md).
  * Only design G can be real time, and it needs a cluster-wide shared-transcript SWIRL prover:
    sumcheck all-reduces, one WHIR over all GPUs, WHIR round codewords by all-gather.
  * Nothing of that prover exists yet.
  * The tail (2.6 s mid) is on the critical path and set by the SHA AIR's zerocheck.
* **R1–R8 below**:
  * R2 is now measured (see R0).
  * R3, R5 and R7 apply only to the tree fallback.
  * R1, R4 and R6 still apply to G.



* **R1 Base cost on SWIRL at Ext12.** ≈ 546 cell-eq per adversarial op, against PERF's univariate 281.
  That alone is 1.73 s after execution on 32 H200.
  * The ≤ 2 s worst case then needs design G plus cheap NV cells, or > 35 % GPU efficiency, or a smaller
    extension for the base layer. A smaller extension would need NV to verify an Ext10 child.
  * Alternatively, a univariate base layer with a dedicated level-1 verifier circuit.
* **R2 NV prover speed is unmeasured on GPU.**
  * On CPU the NV prover is ≈ 4,000× slower per cell than PERF's calibrated LDE path.
  * The tree designs' 4–11 node levels make the critical path sensitive to it: 4 → 30 cell-eq per NV cell
    moves T8 from 2.27 to 4.84 s.
* **R3 Program binding is quadratic in arity at levels ≥ 2.** The scalable fix (preprocessed program
  commitments) needs NV to verify preprocessed children. That is also needed for FETCH code tables (R4).
* **R4 No preprocessed or cached children in NV.** This blocks the per-contract code table as PERF
  designs it.
* **R5 Memory continuity across independent proofs** is expensive (§2.3). Cuts must follow receipt
  boundaries, or the machine-internal shared transcript (G/H).
* **R6 Base-faithful is almost entirely open** for a real segment AIR set (§10).
* **R7 The tree soundness claim needs the single-database theorem.** A per-proof union fails at ≥ ~60
  proofs (§9.1).
* **R8 Inner-NV LDE at c = 15, b = 6 is 960×.** Tree nodes must use low blowup. Their verification then
  costs more queries in the parent: [168, 124, 61, 40, 30] instead of [50, 46, 33, 26].

## 12. Next steps (phase 2, revised for G)

1. **G's L1.** Productise `build_l1_linked`:
   * fixed side-proof slots, so the program shape is fixed;
   * vk pre-hash constants per side-proof kind;
   * link layout.

   Merge with the recursion lane's G1 passthrough: tag 8 and `PvD` are already identical.
2. Chunk-statement public values of the global base proof: ctx, enc S_0, enc S_S, and the layout V_d
   recomputes.
3. Shared-transcript SWIRL prover across GPUs (with lane/pq-prover-latency).
4. Base-faithful BF1/BF2 for the first real seg-v1 tables.
5. Tree fallback items (below) only if a multi-cluster configuration is wanted.

Original list:

1. Generalise the prototype's N2 to two BIND regions: per-child E-table reserved rows, a region index in
   BIND rows, and two ACC rows. Then prove a real 2-to-1 N2 with binding.
2. Add preprocessed children to NV (one extra commitment in stacking/WHIR). This unblocks N2×k and FETCH.
3. Port a first real segment AIR (direct-Wasm EXEC/CODE/RANGE + MEM + STATE with boundary public values)
   to the pinned shape, and measure N1 per child against [L].
4. GPU spike: NV cell cost (A-4) and SWIRL base cost per op (A-2). Together they decide G vs T8.
5. final-soundness: write Theorem 7.4-tree (F3-tree) and drop the union cross-check for trees.
