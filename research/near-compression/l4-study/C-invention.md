# L4-C: inventing hash-only levers for a < 300 KB PQ final proof

Date 2026-10-17. Design model only. No repo modified. Scripts are in `scratchpad/l4/m/`:
- `ext.py` generalises `levers_model.py`. It handles a domain with an odd blowup factor, cell and element byte sizes, a domain shrink factor, bytes per column, element bit-packing, the penultimate's leaf-hash format and in-circuit multiproof dedup.
- `run.py`, `run2.py` and `run3.py` run the experiments. Outputs: `run.txt` plus the stdout tables below.

`ext.py` reproduces the log's numbers exactly: the child's query schedule [82,63,51,43,37], its initial and codeword bytes, and the corrected fixed point (c_sha 12k: penultimate 9,146 SHA, cells 2^26.78, final **444,481 B**; all-levers row **355,883 B**).

**Baselines.** "T" is the log's *today* row: 268-bit target, 48-B digests, m = 8, per-round k1. It is the levers `fixed_point_table` setting. "L" is the log's *all-levers* row: penultimate target 236, final target 226 (z = 32 grinding), 42-B digests. I also give m = 3 numbers where they matter. The parent-circuit guesses (2,000 cells per query, 2^20 fixed cells, 300 columns, 40 cells per Ext12 multiply-add) are unchanged, so every number inherits them.

## Key finding

Two structural levers that do not touch the contract stand out:
1. A **mixed-radix ×15 blowup**. BabyBear's p−1 = 2^27·3·5, so the evaluation domain can be 15·2^27 points instead of 2^27.
2. A **coset-as-one-message leaf hash** in the penultimate layer, which cuts the in-circuit SHA count by 25–32 %.

Combined with three small encoding and protocol tweaks, the model reaches **≈ 298–311 KB at today's security settings** (268 bits, 48-B digests, no grinding) at c_sha = 12k. It reaches **≈ 241–247 KB with grinding and 42-B digests**. At c_sha = 24k the figures are ≈ 330–351 KB and ≈ 264–277 KB. Neither of the two main levers changes the hash, the field size or the security assumptions. Both still need a theorem check and engineering.

## Results table (final proof bytes, fixed point)

| lever | T, 12k | L, 12k | T, 24k | L, 24k |
|---|---:|---:|---:|---:|
| baseline (log) | 444,481 | 355,883 | 527,161 | 416,893 |
| E1 penultimate leaf = one SHA message per coset | 412,465 | 332,219 | 494,689 | 393,537 |
| E2 in-circuit multiproof dedup | 429,025 | 345,211 | 513,025 | 406,285 |
| E1+E2 | 398,113 | 321,547 | 475,097 | 380,137 |
| E3 blowup ×3 | 389,641 | 317,415 | 450,345 | 361,019 |
| E3 blowup ×5 | 375,233 | 301,987 | 425,041 | 343,339 |
| **E3 blowup ×15** | **345,409** | **278,725** | 386,625 | 310,959 |
| E3 ×15 final layer only | 356,625 | 290,085 | – | – |
| E3 ×15 + E1 | 330,321 | 268,117 | – | – |
| E5 non-shrinking domains | 419,873 | 334,553 | 486,937 | 386,365 |
| E6 one opening per column (48 B) | 430,081 | 341,483 | 512,761 | 402,493 |
| E7 bit-packed elements (31/32) | 438,646 | 351,342 | 520,913 | 411,967 |
| **COMBO neutral (E1,E2,E3×15,E6,E7)** | **306,914** | **247,142** | 342,936 | 277,145 |
| **COMBO + E5** | **298,400** | **240,674** | 329,728 | 263,536 |
| COMBO, 150 columns instead of 300 | 299,714 | – | 335,736 | – |
| m = 3: baseline / COMBO | 458,369 / 310,858 | – | 547,873 / 351,379 | – |
| Goldilocks final layer (best variant) | 349,265 | 282,487 | 381,185 | 307,021 |
| beacon queries (final target 140), alone / with COMBO | 267,553 / 184,555 | – | 312,201 / 203,843 | – |

Breakdown of COMBO+E5 at T/12k: auth 164 KB, initial leaves 40 KB, codeword 40 KB, final polynomial 25 KB, relations 18 KB, GKR and other 11 KB. Shape: b = 8 (×15), log h = 19, W = 111, q = [46,43,35,29]. Penultimate: 4,678 SHA compressions (from 9,146), 2^25.8 cells. **Merkle authentication is again the dominant term (55 %).** That is agent B's territory.

## Ideas

### 1. Mixed-radix (×3, ×5, ×15) blowup domains. PROMISING (rank 1)

**Mechanism.** The binding constraint at every fixed point is log h + b ≤ 27, from BabyBear's two-adicity. p−1 = 2^27·15, so a multiplicative subgroup of order 15·2^N exists. It is the union of 15 cosets ζ^j·H_{2^N}, so the prover runs 15 ordinary radix-2 coset LDEs and needs no new NTT code. WHIR folding only uses the 2^k-to-1 maps x→x^{2^k} and x→x^2, which act coset by coset, so the odd factor just carries through the rounds. The rate becomes 2^-b/15, which gives about +1.95 bits per query (≈ b/2 → (b+3.9)/2). This helps the final layer (fewer queries) and also the penultimate (fewer in-circuit SHA, so a smaller final circuit and narrower leaves).

**Security.**
- BCIKS20-type proximity gaps and the CCC 2026 MCA hold for RS over any evaluation set.
- Explicit MCA (ePrint 2025/2051, Thm 9.2) at n = 15·2^27 = 2^30.9 and ρ = 2^-11.9:
  - m = 8: ε = 8.5^7/3 · ρ^-1.5 · 3 · n²/|F| = 2^(20.0+17.9+1.6+61.8−372.1) = **2^-270.9**. That is under the 2^-268 per-round need, but with only 2.9 bits of margin.
  - m = 3: **2^-279.8**.
- Prefer m = 3 here. It costs only +4 KB (310,858 vs 306,914).
- To check: WHIR (ePrint 2024/1586) states its theorems for "smooth" (2-power order) cosets. The proof needs re-reading to confirm that only the 2^k-to-1 structure is used. Shift-query sampling over a non-2-power index set needs unbiased sampling (rejection sampling, negligible cost).

**Bytes.**
- −99 KB (T/12k, 444→345 KB) and −77 KB (L/12k).
- ×5 alone gives −69 KB; ×3 gives −55 KB.
- ×15 in the final layer only gives −88 KB.
- "Hypothetical two-adicity 30" gives 360 KB, the same as ×15's 345, so this lever is "+3.9 bits of two-adicity for free".

**Cost.**
- Final-layer LDE: 2^25.8 × 2^8 × 15 ≈ 2^37.7 base elements ≈ 0.9 TB. That does not fit in HBM, so it must be streamed coset by coset, keeping only the row digests (2^29.9 leaves × 48 B ≈ 46 GB). The q0 ≈ 46 opened cosets are recomputed at query time.
- Rough throughput: about 2^37.7 NTT-elements plus about 0.9 TB of SHA-512 hashing. My guess is a few seconds per 8×H200 machine. Not measured.
- Round-1 Ext12 codeword ≈ 2^29.9 × 48 B ≈ 46 GB.
- Verifier work: unchanged or lower (fewer queries).

### 2. Coset-as-one-message leaf hashing in the penultimate. PROMISING (rank 2)

**Mechanism.** The backend hashes each of the 2^k points of a fold coset separately and then builds a 2^k mini-tree. That costs 2^k + 2^k − 1 compressions per query, which is 15 for k = 3 and 31 for k = 4. The verifier always opens the whole coset, so the leaf can be a single SHA-384 message over the concatenated coset: ⌈(2^k·48+58)/128⌉ = 4 (k = 3) or 7 (k = 4) compressions. The final proof's bytes are unchanged (same values, and depth already excludes the intra-coset levels). The gain comes entirely from a smaller final circuit (2^26.8 → 2^26.3 cells), which cuts W and the initial-leaf bytes.

**Security.** Neutral. Collision resistance of SHA-384 over a fixed-length message.

**Bytes.**
- Predicted gas-failure5 verifier count: **10,229 → 6,947 compressions** (−32 %). This is directly checkable.
- Fixed point: penultimate SHA 9,146 → 6,849; final −32 KB (T/12k), −24 KB (L/12k), −33 KB (T/24k).
- It also applies to the final layer's own tree (no byte change, faster native verify).

**Cost.** Lower prover and verifier hashing. It changes the leaf format of every layer.

### 3. In-circuit multiproof dedup (or static Merkle caps) for the penultimate's paths. PROMISING-small

**Mechanism.** The model counts q·depth node compressions in-circuit. Only the distinct nodes need hashing. In the AIR, each node row provides (level, index, digest) on a LogUp bus and consumes its two children. Siblings not on any path enter as advice rows. The row count is data-dependent, so it is padded to the expectation plus a tail bound (a completeness-only failure). A static Merkle cap of height c (sent in the penultimate proof, absorbed into the transcript) captures most of the gain with a fixed layout.

**Security.** Neutral (collision resistance; the root binds).

**Bytes.** Child 10,229 → 8,645 (−15 %). Final −15 KB (T/12k); with E1, −46 KB in total.

**Cost.** AIR complexity (memory-style bus).

### 4. Goldilocks (two-adicity 32, very smooth p−1) final layer over the BabyBear penultimate. PROMISING-fallback, dominated by #1

**Mechanism.** The final circuit is SHA-dominated, so a 64-bit field changes little in SHA cost. Ext6 = 384 bits = 48 B satisfies MCA. The two-adicity limit moves to 32 (plus odd factors 3·5·17·257·65537).

**Cost model.** Cells are 8 B. BabyBear Ext12 arithmetic becomes non-native (×4 assumed). c_sha is ×0.7 or ×1.0 of BabyBear's.

**Bytes.** 349–375 KB (T/12k) against 345 KB for ×15 in BabyBear.

**Cost.** A second field in the backend and non-native arithmetic, for no gain over #1. Keep it only as a fallback if a mixed-radix WHIR proof turns out to need a 2-power order.

### 5. Non-shrinking domains (rate decays by k per round instead of k−1). PROMISING-small

**Mechanism.** Keep each round's domain at the previous size instead of halving it. The rate improves by 2^k per round, so later rounds need fewer queries. The cost is +1 depth per round and a larger prover domain in Ext12.

**Security.** Same WHIR theorem; the domain choice is free.

**Bytes.** −25 KB alone (T/12k), −8 to −13 KB on top of COMBO.

**Cost.** Round i commits a domain 2^i× larger than standard WHIR. That is a bounded prover cost (rounds 1–3 in Ext12), but Ext12 hashing and NTT grow by roughly 2–4×.

### 6. One opening per column (shift via sumcheck). PROMISING-small

**Mechanism.** Each column currently costs 2 Ext12 openings (r and r·ω). Reduce the "next-row" claims with a shift sumcheck (HyperPlonk/Jolt style) onto the batch point, so each column costs 48 B.

**Security.** Sumcheck error is about deg·log n/|F|, negligible.

**Bytes.** −14 KB. Halving the columns to 150 adds −7 KB.

**Cost.** One more small sumcheck.

### 7. Bit-packed proof encoding (31-bit cells, 372-bit Ext12). PROMISING-trivial

**Mechanism.** Serialise opened values at their real bit width.

**Bytes.** −4 to −6 KB.

**Cost.** Encoder only.

### 8. Beacon-derived queries (commit, then queries from a later block's randomness). KILL under the contract

**Mechanism.** If the query positions come from public randomness revealed after the commitments, the prover cannot grind them, so the per-round target falls from 268 to about 128 plus a bias margin (modelled as 140). WHIR's queries interleave with later commitments, so this needs one beacon per round or a FRI-style "all commits, then queries" layout.

**Bytes.** 267 KB alone and 185 KB with COMBO (T/12k), which is the largest lever found.

**Why killed.**
- Soundness would rest on NEAR consensus randomness. The VRF is Ed25519, which is not post-quantum.
- Colluding consecutive block producers can predict the next random value before the commitment is fixed.
- The proof stops being standalone and adds 1–5 blocks of latency.

It is a user-level contract change, not a technical win. Listed for completeness.

### 9. Amortising one final proof over all shards or blocks. KILL as a size lever

Per-proof bytes are unchanged. Per-chunk bytes fall by 1/S only if the arena metric counts per chunk; a verifier of one chunk still downloads the whole proof. Aggregating over blocks breaks real-time verification. It is a metric decision, not a compression.

### 10. Verifier-held preprocessed oracles (the fixed final circuit's tree). KILL (micro)

The verifier would have to store about 2^35+ codeword cells (> 100 GB) or recompute evaluations in O(N). The saving is limited to the preprocessed share of W, which is small for a SHA verifier. The better version is to design the final AIR with no preprocessed columns: use structured lookup tables whose MLE the verifier evaluates in O(log). Worth ≤ a few KB.

### 11. GKR-proven SHA-384 with only I/O committed. KILL

The aim would be c_sha → about 50 committed cells. But SHA-512 as a layered circuit has about 10^3+ layers (80 rounds, carry chains). The GKR transcript is about layers × log(width) × 4 × 48 B ≈ 4 MB. That is either final-proof bytes or about 3×10^4 in-circuit transcript compressions. Both are worse than a 12k-cell committed AIR.

### 12. Higher-arity or compression-function Merkle nodes in the penultimate. KILL (contract)

Binary with 48-B digests is already optimal (96 B + padding is one block; arity 4 is 2 blocks per 2 levels; arity 8 is 4 per 3). Arity 3 in one raw 128-B block needs 42-B digests (a U-7 decision) and drops MD padding. Using the chaining value as data assumes an ideal compression function, which is a new assumption beyond SHA-384-as-RO. Revisit only if U-7 adopts 42 B: it would cut penultimate node hashing by about 37 %.

### 13. Extension-field or ECFFT domains for more two-adicity. KILL

- Ext12: v2(p^12−1) = 29, only +2 bits, and every initial-leaf cell becomes 48 B (12×).
- Ext2 multiplicative: 2^28.
- ECFFT over F_p: the Hasse interval p+1 ± 2^16.5 contains no multiple of 2^28 (p ≈ 7.5·2^28), so no curve beats 2^27·odd.
- ECFFT over F_{p^2}: values in Ext2 (2× leaf bytes), and there is no WHIR-over-isogeny soundness theorem.

#1 gets +3.9 bits for free instead.

### 14. Splitting the final into two half-size proofs, or a DA "proof plus data" split. KILL

Fixed costs double, and the model gives 2 × (proof at 2^25.8) > 1 × (proof at 2^26.8). Only verifier-known statement data (roots, VK) can legitimately be excluded, and that is already excluded.

### 15. Batch-opening all rounds against one tree, or linked (FRI-style) query positions. KILL

The round-(i+1) oracle depends on round-i challenges, so it cannot share a tree. Linked queries lose WHIR's rate decay (FRI needs q0 queries in every layer).

### 16. Smaller extension (Ext10 or Ext11) for codeword values. KILL

The MCA error ≈ 2^86.4/|F| (m = 3, n = 2^27, ρ = 2^-8) must be ≤ 2^-268, which needs |F| ≥ 2^354. Ext11 is 341 bits.

### 17. Validators each checking a random subset of queries. KILL

It gives network-level soundness with an honest minority, not per-verifier ≤ 2^-128.

### 18. Packing limbs to cut committed cells or opened bytes. KILL

Openings are at LDE points, which are full field elements, so a limb range-check saves nothing on the wire. Lookups need the limbs as separate cells.

### 19. Per-round variable fold k_i (beyond k1). Untested, expected ≤ a few KB

The search already shows k ∈ {3, 4, 5} is near-flat.

## Top 3 PROMISING and their next experiments

1. **Mixed-radix ×15 blowup (−77 to −99 KB alone; the core of the sub-300 combo).**
   - (a) Theorem check: re-read the WHIR soundness proof (ePrint 2024/1586, plus the Tartu corrections) and confirm that nothing needs |L| to be a power of two. Fix the shift-query sampler.
   - (b) Prototype: a 15-coset LDE plus Merkle commit on the pinned backend for a 2^26-cell, W ≈ 110 trace at blowup 15·2^8, streamed. Measure wall time and peak memory on one 8×H200.
   - (c) Adopt m = 3 for the MCA margin (2^-279.8 vs 2^-270.9).
2. **Single-message coset leaves, plus in-circuit dedup or caps (−46 KB together).**
   - Change the Merkle leaf format and re-run the instrumented verifier on gas-failure5.
   - Prediction: **6,947 compressions** (seq leaves) and 5,363 (with dedup), against the measured 10,227. One run validates the model.
3. **Micro-lever bundle: non-shrinking domains, one opening per column, bit-packed encoding, ≤ 150 columns (≈ −25 to −35 KB on top of the top two).**
   - Build the encoder change first (free).
   - Then estimate the prover cost of E5 (Ext12 domain growth) on the same final shape.
   - Then design the narrow (≤ 150-column) SHA-384 AIR whose c_sha the whole result depends on. **c_sha remains the gate:** COMBO+E5 is under 300 KB at today's settings only for c_sha ≲ 12k; with grinding and 42-B digests it holds up to about 24k.

## Honesty notes

- Every number inherits the unmeasured parent guesses (c_sha, cells per query, fixed cells, 300 columns).
- The multiproof count for non-power-of-two leaf sets is approximated level by level.
- ×15 with m = 8 has only 2.9 bits of MCA margin.
- The WHIR theorem for non-2-power cosets is not yet verified.
- No prover-time numbers are measured. Real-time feasibility of the 0.9-TB streamed LDE is a guess.
