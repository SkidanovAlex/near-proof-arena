# PQ final-layer size model and the WHIR list-decoding question — 2026-10-17

Lane `lane/pq-native-hermetic`. Design model only; no new proof, no security
certificate. Contract unchanged (V3-D3A-STUDY §D: SHA-384, ≤ 2⁻¹²⁸ at 2⁶⁴
quantum queries, proven bounds; 0.5–1 MB target, 300 KB stretch).

## Measured child, decomposed (gas-failure5, 378,849 B)

WHIR is 336,260 B. Of that, Merkle auth paths are 256,992 B (76 %): 5,354
digests = Σ queries × depth with queries [82,63,51,43,37] and depths
[21,20,19,18,17] (log domain 24, leaves group 2^k = 8, domain halves per round).
Codeword values 74,496 B (194 queries × 8 Ext12); initial leaves 2,624 B
(stacked width 1). Verifier: 10,227 SHA-384 compressions = 2,208 leaf
(276 queries × 8) + 7,286 node (5,354 path + 276 × 7 intra-leaf) + 733 transcript.

## Model

`research/near-compression/native/final_layer_model.py` mirrors
`WhirConfig::new` (268 query bits, no grinding, ListDecoding m = 3 or
UniqueDecoding) and asserts that it reproduces all of the numbers above exactly
(queries, digests, values, WHIR bytes ±16, verifier compressions). Parent-circuit
costs are explicit inputs: cells per in-circuit SHA-384 compression `c_sha`,
20,000 cells per child query, 2²² fixed cells, column count. It iterates
"each layer verifies the previous one" to a fixed point, choosing the
penultimate shape to minimise the final layer's SHA work and the final shape
(b, k, stacking height ≤ 2^(27−b), final-poly length) to minimise bytes;
optimal-multiproof digests by exact expectation (3,499 for the child, below the
measured 4,017-digest dictionary). Output: `results/pq384-final-layer-model.{txt,json}`.

| regime | c_sha | final layer (multiproof, 300 cols) | shape |
|---|---:|---:|---|
| list m=3 | 8k | **521 KB** | b=5, k=3, h=2²², final poly 2¹⁰, W=31 |
| list m=3 | 12k | 589 KB | same, W=49 |
| list m=3 | 20k | 702 KB | b=4, h=2²³ |
| list m=3 | 30k | 817 KB | b=4, k=2 |
| unique | 8k–30k | 2.8–3.6 MB | — |

Columns cost 96 B each (two Ext12 openings): 1,500 columns add ≈ 115 KB, so the
parent AIRs must be narrow. Breakdown of the 521 KB point: auth 235 KB,
initial leaves 117 KB, codeword values 75 KB, final poly 49 KB, relations 32 KB.

**Conclusion.** With SWIRL/WHIR at 268 bits and SHA-384, the final layer is
≈ 0.5–0.8 MB; Merkle authentication alone is ≥ 235 KB at any realistic shape.
Remaining levers, none modelled as adopted: first-round fold k=1 (≈ −90 KB, needs
a per-round-k backend change), larger m (≈ −5–8 % queries; raises the MCA error
term), ≈ 330-bit truncated digests (≈ −40 KB, a U-7 spec question). Together
≈ 370 KB at the optimistic SHA cost. **300 KB is not reached by this family**;
the U-9 0.5–1 MB target is consistent with it.

## Is WHIR's list-decoding regime proven?

Yes, for the radius the backend uses. Bordage–Chiesa–Guan–Manzur, *All
polynomial generators preserve distance with mutual correlated agreement*, CCC
2026 (LIPIcs 383, 24; full version ePrint 2025/2051), Theorem 5: every polynomial
generator has MCA for RS[F, D, k] for γ ≤ 1 − (1 + 1/2m)√ρ, m ≥ 3, with error
O(m⁷ n² / ρ^{3/2} · Σ dᵢ / |F|) (explicit constants in the full version, not yet
read — the ePrint PDF returned 403). The backend's `ListDecoding{m}` agreement is
exactly (1 + 1/2m)√ρ. Order-of-magnitude for n = 2²⁷, m = 3, ρ = 2⁻⁵, Σdᵢ = 3:
≈ 2⁷⁴·C / 2³⁷² = 2⁻²⁹⁸·C per round, inside the ≈ 2⁻²⁶⁸ need unless C > 2³⁰;
Ext8 would give 2⁻¹⁷⁴ (insufficient), confirming Ext12. Capacity-regime
conjectures are false (ePrint 2025/2046) and stay excluded.

Still open before calling a parameter set certified: the explicit constant of
Theorem 5; the WHIR soundness theorem consuming it (incl. the corrections in the
2026 Tartu thesis); rbr knowledge soundness and the QROM BCS transfer (§11.2).

## Implication for the next step

The parent's cell count matters only through first-round leaf width; the
column count and Merkle paths matter more. The SHA-384/Ext12 parent should be
designed narrow (≤ ~500 columns total, SHA-512-family compression as a tall
narrow table), with a measured `c_sha` replacing the model input.

## Reconciliation with the lane's ~357–379 KB figures

The `research/direct-wasm-whir` sub-400 KB numbers are all **non-recursive
child proofs of a ≤ 193-instruction straight-line Wasm slice** at SHA-384/Ext12,
268 query bits: 357,069 B (byte-packed 193-instruction child + dictionary +
request), 375,127 B (framed diagnostic bundle), 379,047 B (gas-failure5). A child's
size is nearly independent of its workload only up to its stacking height;
it says nothing about a proof covering 1 Pgas. The model above reproduces
gas-failure5 exactly.

The only measured **recursive parents** (`results/native-literal-query128*`,
compression log 2026-10-17 "Integrated Wasm recursion at stronger query
targets") use Poseidon2 + Ext4, a 128-bit query target and SplitUniqueList
(first round unique): parent 470,137 / 513,561 / 875,289 B at log-blowup
5 / 3 / 1, WHIR 84 % of the bytes, and the native calculator's proximity term
only 75.7 bits. Under U-7 (48-B digests vs 32 B) and 268 query bits (≈ 2× queries)
the same shape would be well above 1 MB. No recursive layer at the PQ contract
has been measured yet; the model's 0.5–0.8 MB already assumes list decoding in
every round, multiproof dedup and an optimized final-poly cut.

## Iteration 2: levers and the decisive parameter (correction)

`native/levers_model.py` (output `results/pq384-final-layer-levers.txt`)
generalises the calibrated model: per-round query target, list multiplicity m,
digest width, a separate first-round fold k1, grinding (under U-6's bounded
queries the attack succeeds with O(t²·2⁻ᶻ·ε), so z PoW bits lower the target by z;
honest cost 2ᶻ SHA-384 per round), and the final circuit's cell count. It
reproduces the measured child.

**Correction to the earlier conclusion.** The ≥ 521 KB figure assumed 8k–30k
committed cells per in-circuit SHA-384 compression and 20k cells per query.
The final layer's size is driven by its committed cell count (first-round
leaf width), and in SWIRL lookups/interactions are proven by GKR, not committed:

| final circuit | today (268, m=3, 48 B) | all levers (226, m=8, 42 B, k1 free) |
|---|---:|---:|
| 2²² cells | 261,697 | 206,317 |
| 2²⁴ cells | 342,177 | 260,373 |
| 2²⁷ cells | 525,041 | 374,777 |

Fixed point (penultimate shaped for minimal in-circuit SHA work; 2,000 cells per
query, 2²⁰ fixed arithmetic cells — both guesses):

| c_sha (cells/compression) | penultimate SHA | final cells | today | +k1,m=8, 258 | + z=32, 42 B |
|---:|---:|---:|---:|---:|---:|
| 1,000 | 2,343 | 2²¹·⁷ | 237,953 | 228,737 | 197,581 |
| 2,500 | 2,803 | 2²³·⁰ | 272,001 | 259,585 | 224,317 |
| 4,000 | 3,355 | 2²³·⁸ | 301,569 | 287,041 | 248,341 |
| 8,000 | 5,133 | 2²⁵·³ | 362,977 | 344,545 | 295,171 |

**Gate:** < 300 KB at today's protocol settings needs c_sha ≲ 4k committed cells
per SHA-384 compression (plus the arithmetic guesses holding); ≲ 8k with grinding
and 42-B digests (both need user decisions). Next: measure c_sha with a real
SHA-512-family AIR on the pinned backend, then prove a shape-equivalent final
layer (same cells/columns/params) to measure final bytes directly.

## Iteration 3: realistic in-circuit SHA-384 cost closes the hash-only gap only partly

Existing lane SHA-384 AIRs (`results/sha384-batched`, `sha384-shared` on
`research/direct-wasm-whir`): core table 5,234 columns × 80 rows ≈ 419k cells per
compression (bit-decomposed), ~100× over the gate; its width alone would add
≈ 500 KB of column openings to a final layer. A compact one-row-per-round
SHA-512-family AIR on BabyBear needs the 192 new bits per round (a, e, W) plus
split decompositions for the non-byte-aligned Σ/σ rotations and copies of
b, c, f, g: ≈ 120–600 committed cells per row, i.e. **≈ 10–48k per compression**
(published reference: OpenVM SHA-256 ≈ 12k cells per compression; SHA-512 ~2×).
The ≲ 4k gate is not reachable with a committed-trace AIR.

Fixed point at realistic cost (same assumptions as iteration 2):

| c_sha | today | + k1, m=8, 258 | + z=32, 42 B |
|---:|---:|---:|---:|
| 12k | 398,113 | 376,465 | 321,547 |
| 16k | 430,681 | 402,337 | 344,283 |
| 24k | 485,209 | 456,065 | 384,425 |
| 32k | 526,417 | 494,785 | 415,645 |

Binius (lane, binary-field PCS, unique-decoding queries, 32-B digests): the fixed
hash graph alone is 341,716 B at a 128-bit query budget and 643,444 B at 272 —
the same Merkle-query floor.

**Verdict at this iteration:** a hash-only SWIRL/WHIR recursion with a realistic
SHA-384 AIR lands at ≈ 320–530 KB; < 300 KB needs ALL of: c_sha ≲ 8k, grinding
z ≈ 32, 42-B digests, per-round k1 and m = 8. Structural alternatives to
investigate: (1) hash-based accumulation (Arc/WARP-style) so the final circuit
does not re-verify multi-round Merkle openings; (2) a non-hash final wrap
(lattice: LaBRADOR/Greyhound) — a new assumption class, user decision.

## Iteration 4: accumulation does not move the final-layer floor; MCA constant pinned

**WARP** (Bünz–Chiesa–Fenzi–Wang, ePrint 2025/753, §2 and Table 1): the
accumulation verifier makes ℓ·t queries with t > λ / −log(1−δ_PG), one Merkle
opening per query into each accumulated codeword, list-decoding regime.
In-circuit SHA-384 per step ≈ ℓ·t·depth ≈ 2 × 71 × 24 ≈ 3.4k compressions at
rate 2⁻⁸ and 268 bits — the same range as the cheapest WHIR verifier at the fixed
point (2.3–8.6k). The decider still needs a full succinct proof of the
accumulator (a WHIR opening over a codeword the size of the step witness), so the
final layer is the same fixed point. Accumulation buys linear prover time, not a
smaller final proof. Arc (ePrint 2024/1731) is similar with more queries.
WARP's own RS list-decoding row cites only BCIKS20 correlated agreement with MCA
conjectured; CCC 2026 (below) now supplies MCA.

**Explicit MCA constant** (Bordage–Chiesa–Guan–Manzur full version, ePrint
2025/2051, Definition 9.1 / Theorem 9.2): for γ ≤ 1 − (1 + 1/2m)√ρ, m ≥ 3,
ε = Σᵢ (m+½)⁷ / (3ρ^{3/2}) · dᵢ · n² / |F|. With n = 2²⁷, ρ = 2⁻⁵, Σdᵢ = 3,
|F| = 2^372.1 (Ext12): **2⁻²⁹⁸ for m = 3, 2⁻²⁸⁹ for m = 8**, below the ≈ 2⁻²⁶⁸
per-round need. Ext8 (2^248) would give 2⁻¹⁷⁴. Still open: the WHIR theorem
consuming MCA (incl. the 2026 Tartu corrections), rbr knowledge, QROM BCS.

**State after four iterations.** Hash-only, no new user decisions: ≈ 398 KB at
best (c_sha 12k). Under 300 KB needs user decisions (grinding z ≈ 32,
≈ 336-bit truncated digests) plus backend changes (per-round k1, m = 8) and a
SHA-384 AIR at ≲ 8k cells/compression — none demonstrated. Or a non-hash final
wrap (lattice), which adds an assumption class.

## Iteration 5: lattice final wrap — fits easily, but needs decisions

LaBRADOR (Beullens–Seiler, CRYPTO 2023, ePrint 2022/1341): ≈ 58 KB at 128-bit
security for R1CS mod 2⁶⁴+1 with 2²⁰ constraints; size nearly constant in the
practical range (dominated by the last recursion step). Greyhound (CRYPTO 2024)
gives a lattice PCS with ≈ 53 KB proofs at N = 2³⁰ and O(√N) verification.
A final layer "LaBRADOR proof that the penultimate SWIRL proof verifies" is
estimated at **≈ 60–80 KB**: SHA-384 at ~50–100k R1CS constraints per
compression × 2–6k compressions ≈ 2²⁷–2²⁹ constraints, plus non-native BabyBear
Ext12 arithmetic.

What it costs (none resolved here):
1. **New assumption class** (Module-SIS hardness, lattice-estimator based) beside
   SHA-384-as-QRO; amends U-7 "SHA-384 throughout". User decision.
2. **Security proofs:** LaBRADOR's knowledge soundness is classical ROM with
   relaxed (norm-bounded) extraction; QROM/rbr treatment at the U-6 contract and
   "proven bounds only" (U-2) not established.
3. **Verifier:** LaBRADOR verification is linear in the R1CS size (~2²⁸ mults)
   unless the fixed verifier R1CS is preprocessed with a Greyhound-style
   commitment; NEAR validators need cheap verification.
4. **Prover latency:** a 2²⁸-constraint lattice proof per chunk against U-8
   real-time; unmeasured.
5. **Formal correctness:** no Lean model of lattice soundness exists.

## Decision point after five iterations

| route | final size | needs |
|---|---:|---|
| hash-only, current settings, realistic SHA AIR | ≈ 400–530 KB | nothing new |
| hash-only, all levers | ≈ 300–415 KB (< 300 only if c_sha ≲ 8k) | grinding z≈32, ≈336-bit digests (U-7), per-round k1 + m=8 backend changes |
| accumulation (WARP/Arc) | same as hash-only | — (prover speed only) |
| lattice final wrap | ≈ 60–80 KB | MSIS assumption, QROM/proven-bound work, verifier preprocessing, latency |

## Iteration 6: is there new science for hash-only? (user: "otherwise use lattice")

The hash-only floor rests on (1) the ≈ 258–268-bit per-round target (Grover-tight
t² loss on Fiat–Shamir query sampling — no known way around it), (2) 48-B digests
(t³/2ⁿ binding), and (3) **per-query bits ≈ b/2 at the Johnson radius**. Only (3)
has live research: proximity gaps up to list-decoding *capacity* would give
≈ b bits per query.

* Jeronimo–Liu–Rajpal, arXiv 2601.10047 (folded RS, capacity): **withdrawn**,
  "subsumed by the prior work of Goyal and Guruswami".
* Jeronimo, arXiv 2609.05870 (Sept 2026, single author, unreviewed): RS list
  decoding to 1−ρ−γ and MCA for curves with error n^{O_γ(1)}/q, constants
  unstated. Polynomial-in-n factors with exponent ~1/γ force a much larger
  field for small slack; no FRI/STIR/WHIR theorem.
* Capacity is the hard limit: beyond it the conjectures are false (ePrint 2025/2046).

Model (`levers_model.py`, `bits` patched to b − 0.5 or b − 1; Ext24 = 96-B elements to absorb the error):

| assumption | c_sha 12k, today | 12k, z=32 + 42 B | 24k, today | 24k, z=32 + 42 B |
|---|---:|---:|---:|---:|
| Johnson (proven), Ext12 | 398,113 | 321,547 | 485,209 | 384,425 |
| capacity b−0.5, Ext24 | 292,177 | 245,509 | 334,609 | 278,953 |
| capacity b−1, Ext24 | 303,393 | 258,831 | 353,209 | 295,039 |
| capacity b−0.5, Ext12 (optimistic) | 218,129 | 180,751 | 253,585 | 208,521 |

**Verdict:** hash-only < 300 KB is plausible only if capacity-regime MCA for RS
(or folded RS) is proven with explicit, small-enough constants and plugged into a
WHIR-class protocol — open research, not usable under U-2 today.

**User decision (2026-10-17): pursue the lattice final wrap**; keep capacity-regime
proximity gaps as a watch item that could later make a hash-only final layer viable.

## Iteration 7: pushing the capacity-regime science through — it does not shrink proofs here

The optimal-gap folding IOPP now exists: Li–Xing–Yao–Yuan–Zhu, *How to Fold
Linear Error-Correcting Codes with Optimal Proximity Gaps*, ePrint 2026/2133
(FRI-style folding for folded RS and univariate multiplicity codes, CRT
consistency), on Goyal–Guruswami (STOC 2026, ePrint 2025/2054) MCA for
subspace-design codes. Their Theorem 1.1/4.14: MCA at radius 1 − R − ε with
error O((N/ε + 1/ε³)/q), **provided the folding parameter
m ≥ 4R(2−R)/ε² + 4(1−R)/ε**; each query returns 2m field elements. Their own
tables use ε ≈ 0.25–0.35, m = 16–32, and claim a smaller field (128-bit field for
100-bit security vs 192 for FRI), not smaller proofs. Reducing m to O(1/ε) with
a usable error is stated as open; Jeronimo's RS result (arXiv 2609.05870) gets
m = O(1/ε) "at the cost of a prohibitively large soundness error bound".

Bytes per security bit at ρ = 2⁻⁵ (path 23 × 48 B; Johnson m=8 leaf 8 × 48 B):

| ε | proven m | vs Johnson | conjectured m = 1/ε | vs Johnson |
|---:|---:|---:|---:|---:|
| 0.15 | 37 | 3.06× | 7 | 1.17× |
| 0.10 | 64 | 4.01× | 10 | 1.14× |
| 0.05 | 176 | 8.06× | 20 | 1.35× |
| 0.02 | 809 | 29.8× | 50 | 2.23× |

At low rate the Johnson radius already yields ≈ b/2 bits per query; capacity
gains require ε ≪ ρ and hence large symbols, whose bytes exceed the saved queries.
Capacity-regime gaps help at high rate (smaller field, cheaper prover), not for
our proof size. **Correction:** iteration 6's "b − 0.5" rows ignored symbol size
and are withdrawn. Even a full solution of the stated open problem (m = O(1/ε)
with small error) would be worse per byte at our rates.

The shared ChatGPT research ("Designing Succinct STARK Proofs") reaches the same
contract arithmetic (≈ 256-bit rbr + margin, ≈ 384-bit hash) and concludes that a
conservative 128-bit-quantum < 300 KB proof "still needs its own complete
parameter analysis and benchmark"; its cited sub-300 KB systems (OpenVM 2.0,
100-bit; RISC Zero ≈ 200 kB) do not meet U-6.

**Conclusion unchanged: lattice final wrap is the route to < 300 KB.**

## Correction (2026-10-17): final-polynomial cost was missing from the penultimate shape

`levers_model.sha_blocks` counted transcript absorption as a constant 733
blocks, so the optimiser chose penultimate shapes with a 2¹⁴-element final
polynomial for free. It now adds the absorption (2^log_final × 48 B / 128 B
blocks) and the final-polynomial evaluation at every last-round query (40 cells
per Ext12 multiply-add, an estimate). The child check is 10,229 vs the measured
10,227 (the child's 4-element final poly was already inside the 733).
Corrected fixed point (iteration 2/3 tables superseded):

| c_sha | penultimate SHA | final cells | today | all levers |
|---:|---:|---:|---:|---:|
| 1k | 5,998 | 2²²·⁹ | 269,201 | 222,301 |
| 4k | 7,329 | 2²⁴·⁹ | 342,969 | 279,363 |
| 12k | 9,146 | 2²⁶·⁸ | 444,481 | 355,883 |
| 24k | 11,447 | 2²⁸·¹ | 527,161 | 416,893 |
| 32k | 12,363 | 2²⁸·⁶ | 570,313 | 448,717 |

Hash-only at realistic SHA cost: ≈ 444–570 KB (today), ≈ 356–449 KB (all levers).
**Lattice-wrap statement size:** verifying the cheapest penultimate costs
≈ 9–12k SHA-384 compressions + ≈ 6×10⁴ Ext12 multiply-equivalents.

## L4: hash-only research bets (2026-10-17)

Three parallel investigations; reports and scripts in
`research/near-compression/l4-study/` (A-sequential-fs, B-openings, C-invention;
`models-C/` reproduces this log's baselines exactly, `calc-B/` likewise).

**A. Sequential-work Fiat–Shamir — KILL (size).** Quantum results (Blocki–Lee–Zhou
2021; Chung–Fehr–Huang–Liao 2021) bound sequential *depth*, not total-query search;
the hoped (t/T)²·ε bound is unproven and a naive compressed-oracle argument gives
no gain. PoSW/spot checks don't make the output unique (cheap resampling) and add
≈ 200–260 KB; full recomputation saves only ≈ 10–29 KB (356 → 327–346 KB) for
0.4–20 s verify. At best a prover-side substitute for grinding (if lemmas L1–L3 proven).

**B. Beating Merkle openings — count reduction KILL; narrower digests PROMISING [O].**
Only lower bound for ROM SNARGs (Haitner–Nukrai–Yogev 2022, conditional, classical)
is ~100× below our paths; Ω(log N) path length is open. Correlated/reused queries,
shared trees, caps, higher arity, bigger leaves, multiproof grinding: all killed
(unsound or no gain; any query distribution saves ≤ 9–18 % of digests and needs a
new theorem). The real lever is Chiesa–Yogev-style *weak binding* (tolerate few
collisions, position-indexed nodes; ePrint 2021/188, 2021/281): quantum
extrapolation ≈ 36 B (uncapped) or ≈ 26 B (capped) digests vs 48 B. At c_sha 12k:
current settings 444 → 388 (36 B) / 338 KB (26 B); with existing levers 376 → 332
/ 290 KB; + 4-ary penultimate tree 276 KB. Needs new lemmas (quantum collision
counting, multi-round FS with state restoration, robust WHIR query soundness) and
a U-7 amendment (digest width), no new assumption class.

**C. Invention — 19 ideas, 7 promising, 11 killed.** Model-only results:
1. **Blowup ×15 domains** (BabyBear p−1 = 15·2²⁷: evaluation domain 15·2ᴺ; prover
   = 15 radix-2 coset LDEs; x→x² folding works per coset). Lifts the h+b ≤ 27 limit
   by 3.9 bits; 444 → 345 KB alone. MCA (ePrint 2025/2051 Thm 9.2) at n = 2³⁰·⁹,
   ρ = 2⁻¹¹·⁹, m = 3: 2⁻²⁷⁹·⁷ (checked independently here), inside 2⁻²⁶⁸.
   Open: WHIR theorem for non-power-of-two domains; streamed ≈ 0.9 TB LDE cost.
2. **Hash a whole fold coset as one SHA message** (not 2^k leaves + subtree):
   cuts in-circuit SHA; predicts gas-failure5 verify 6,947 compressions (measured
   10,227) — directly testable; −24…−46 KB final.
3. Bundle: non-halving domains, one opening per column (shift sumcheck), tight
   field packing, 150-column final circuit: −25…−35 KB.
Combined (c_sha 12k): **≈ 298–311 KB today, ≈ 241–247 KB with z=32 + 42 B**;
c_sha 24k: 330–351 / 264–277 KB. Killed: later-block randomness (185 KB but relies
on NEAR consensus + non-PQ Ed25519 VRF), GKR-proven SHA, shard amortization,
verifier-held trees, Goldilocks (dominated by ×15), extension/EC domains, one tree
for all rounds, Ext10/11, split proofs, subset checking, limb packing.

**Synthesis.** Under 300 KB hash-only now looks reachable *in the model* without
new assumptions: C's ×15 domain + coset hashing + small levers at c_sha ≲ 12k
reaches ≈ 298–311 KB at today's settings, and B's weak-binding digests would stack
on C's auth term (164 KB of C's best point) — not yet modelled jointly. Gates, in
order: (1) L3's measured c_sha; (2) WHIR soundness on 15·2ᴺ domains (paper
check); (3) coset-hash test on gas-failure5 (predict 6,947); (4) streamed ×15 LDE
timing; (5) optional: weak-binding lemmas (B) for a further 40–80 KB.

## L3 milestone 1 measured + L4 levers → hash-only < 300 KB in the model (2026-10-17)

L3 (`lane/pq-sha384-air` @ `58889824f`, report in that lane's
`research/near-compression/results/pq384-sha-air/`): narrow SHA-512-compression AIR
(SHA-384 = IV + truncation), 2 rounds/row, 44 rows × 442 columns (+18 table) =
**19,448 committed cells per compression dense (28,288 padded to 2ᵏ)**, 1.27× the
15,360-cell floor of a bit-based design. Tests: 10,000 + 1,008 compressions equal
`sha2::compress512` (incl. SHA-384/512 vectors, multi-block); debug checker passes;
7,208/7,208 single-cell mutations and 10/10 constraint-preserving bus forgeries
rejected. SHA-only proofs (not a final layer): N = 1,024 → 874,845 B, 67.7 s;
N = 4,096 → 1,024,317 B, 198.6 s; verify 27 ms; ≤ 15.4 GB. N = 16,384 not run (~45 GB).

Fixed point with the measured cost (`l4-study/models-C/run-measured-csha.txt`, L4-C
model, 460 columns):

| c_sha | settings | baseline | ×15 domain | C combo | C combo + non-halving |
|---:|---|---:|---:|---:|---:|
| 19,448 | today (268, m=8, 48 B) | 517,969 | 388,385 | 340,928 | **327,721** |
| 19,448 | levers (236/226, z=32, 42 B) | 413,533 | 317,829 | 276,827 | **263,884** |
| 28,288 | today | 564,841 | 411,393 | 360,303 | 346,323 |
| 28,288 | levers | 449,101 | 333,839 | 292,156 | **278,548** |

**Hash-only < 300 KB is reachable in the model with the measured SHA AIR** — needs
×15 BabyBear domains, coset-as-one-message hashing, the small C levers, grinding
z = 32 (Grover-tight, proven; 2³² SHA-384 per query phase on the prover), digests
truncated to 42 B (t³/2³³⁶ = 2⁻¹⁴⁴ — within the proven-bound contract but amends U-7's
"SHA-384" to "SHA-384 truncated to 336 bits"), per-round k1 and m = 8 backend
changes. Today's settings alone stop at ≈ 320–346 KB. B's weak-binding digests
would be an alternative/extra lever on the ≈ 120–165 KB auth term.
Gates now: (1) WHIR soundness on 15·2ᴺ domains; (2) coset-hash test on gas-failure5
(predict 6,947 compressions); (3) user decision on 42-B digests + grinding;
(4) streamed ×15 LDE timing; (5) a real shape-equivalent final-layer proof.

## Levers implemented and measured; gate 2 confirmed, gate 5 corrects the model (2026-10-17, lane/pq-whir-levers)

Native prover + verifier levers (`native/patches/stark-backend-levers.patch`,
`airbender/direct-wasm/native_sha384_levers_*.rs`; report and circuit spec in
`research/near-compression/results/pq-whir-levers/README.md`). Defaults re-prove
gas-failure5 byte-identically. Measured on gas-failure5: grinding z=24 −27.8 KB,
42-B digests −32.2 KB, m=8 −8.4 KB, multiproof −90.3 KB, E5 −20.5 KB, k1 hurts at W=1;
all combined 378,849 → **246,016 B**, verify 10,227 → 4,898 compressions. Grinding:
2.9–5.3·10⁷ SHA-384/s on 8 threads ⇒ z=32 ≈ 81–148 s per round (extrapolated).
**Gate 2: 6,956 compressions measured vs 6,947 predicted** (leaf/node exact).
**Gate 5** (460-column dummy at the model's best shape b=8 k1=1 k=3 log_h=19, measured
at W ≤ 15, extrapolated with laws exact at three widths): WHIR terms match the model
(auth −0.5 %, initial/codeword/final poly exact), but GKR (72L²+264L+248 B; 44.4 KB at
L=23 for the L3 SHA AIR at 2^18 rows), stacking openings (48 B per stacked column) and
relations exceed the model's child constants by ≈ 47–49 KB: 2^26.4 cells → **479 KB
(268/48 B) and 409 KB (z=32/42 B)** vs model 432 / 360 KB. E6 (one opening per column)
gives no gain: the next-row values must be sent for the nonlinear constraint check.
Applied to the L4-C COMBO+E5 levers point (263,884 B) this gives ≈ 309 KB with E6 and
≈ 332 KB without: the GKR term is now the largest correctable item.

## Round-2 levers measured (2026-10-17, lane/pq-whir-levers)

Gruen GKR + derived GKR claims: GKR = **48L² + 192L + 152 B** (was 72L² + 264L + 248), exact on
the dummy and on the real L3 SHA AIR at 2^18 rows (L=23: 29,960 vs 44,408 B). Gruen batch-constraint
rounds and `max_constraint_degree` = 4 (our driver used 8) cut relations ≈ 3.5–4.3 KB. Next-row mask
(per column, in the vk): child 116/271 rotated, **SHA AIR 438/442 main columns read at the next
row** — ext2's "next 0.3" is not available for that AIR. Two-element PoW: z=32 proved in a real
proof; z=28 3.8 s, z=32 65.5 s (8 threads). Gate 5 re-measured (W=15): 350,713 B (268/48 B) and
293,903 B (z=32 proved, 42 B); extrapolated to 2^26.4 cells: **459,923 / 389,561 B** (round 1:
479,156 / 408,734). On ext2's `L m=3 combo` point the measured laws give ≈ 325 KB. Laws:
`native/levers_laws.py`; report: `results/pq-whir-levers/README.md`.

## Padding-free trace heights implemented (2026-10-17, lane/pq-whir-levers)

`WhirLevers.tight_heights`: each common-main trace commits only its rows up to the last non-zero row
(rounded to 2^l_skip) as power-of-two chunks. The zerocheck and GKR are unchanged (virtual zero tail
up to 2^k). The stacking reduction scales each chunk by an eq factor and adds one first-row rotation
term per chunk. Sound by construction (the proved statement is the upstream one for a zero-padded
trace); AIRs must accept all-zero rows. Circuit-level splitting was rejected: each extra AIR instance
re-pays its column openings (NvAir +6.6 KB, SHA +16 KB). Measured: committed width drops exactly to the
real rows (gate-5 shape at 78 % fill: W 15 → 12, 353,497 → 350,789 B); saving = ΔW × (q0·2^k1·4 + 48),
the W-proportional law the NV model uses, so its ≈ 9.7 KB (308.5 → 298.9 KB at L) applies, provided the
NV AIRs' padding rows are zero-valid. Report: `results/pq-whir-levers/README.md` (round 3).
||||||| d79998e78

## Push to a measured recursive final layer — lanes started (2026-10-17)

User: "continue until we have recursive last step under 300k". Three lanes off this branch:
`lane/pq-recursion-sha384` (port OpenVM v2.1 `crates/recursion` — same stark-backend
commit d667af5 — to SHA-384/Ext12 using the L3 SHA AIR), `lane/pq-whir-levers`
(grinding, 42-B digests, k1, m, coset-as-one-message leaves; gate 2; gate 5 dummy
final layer), `lane/pq-x15-domains` (gate 1 + prototype).

**Gate 1 — ×15 domains: PASS on paper** (`lane/pq-x15-domains` @ `2cf46f1a4`,
`x15-domains/SOUNDNESS.md`). WHIR's smoothness is used only via −x ∈ L, |L^(2^j)| =
|L|/2^j, disjoint 2^k fibres and power-of-two degree; all hold for 15·2ᴺ. BCGM Thm 9.2
and BCHKS25 Thm 1.5 are stated for arbitrary evaluation sets. One edit needed in
WHIR Thm 5.2 ("smooth" → "coset of order c·2^K"), exact uniform query sampling
(reject p−1, reduce mod 15·2^j). **Caveat: at |Ext12| = 2^370.88 and W ≈ 530–600
stacked columns, m = 8 misses 2⁻²⁶⁸ by 2.4–7.5 bits (passes 2⁻²⁵⁸); m = 3 clears
(≤ 2⁻²⁶⁹·⁴, 1.4-bit margin on the batching term) → use m = 3 (≈ +4 KB in model).**
Prototype: `WhirConfig.domain_odd_factor` (default 1, byte-identical: gas-failure5
re-proof ba042e71…), ×15 in every WHIR round, 55/55 tamper tests rejected; 15 coset
DFTs are faster per point than one radix-2 DFT (2¹⁶×64: 5.6–8.5 s vs 11.3–11.9 s).
Streamed LDE (modelled): 0.77–1.22 TB never materialised; ≤ 10 GiB/worker; 30–73 min
on 8 threads, minutes on 192 cores. Open: recursion circuit needs the sampler, 15-point
table, +4 Merkle depth; cpu/cuda backends not ported.

**Gate 2 confirmed, gate 5 corrects the model** (`lane/pq-whir-levers` @ `f5dc91757`,
report `results/pq-whir-levers/README.md`). All levers implemented natively behind
parameters (defaults byte-identical to gas-failure5, 142 upstream tests pass): grinding
(≤ z = 28; z ≥ 29 needs a 2-element witness), 42-B digests, k1, m, coset-as-one-message
leaves, Merkle multiproof, non-halving domains. Gas-failure5 with grinding + 42 B + m=8 +
coset + multiproof: 378,849 → 246,016 B, 10,227 → 4,898 verify compressions. **Gate 2:
coset leaves 6,956 measured vs 6,947 predicted.** Grinding 3–5·10⁷ SHA-384/s on 8
threads → z = 32 ≈ 1.5–2.5 min/round on this CPU. **Gate 5** (460-col dummy at the
model's best shape, measured W ≤ 15, extrapolated with laws exact at 3 widths): WHIR
matches the model (auth −0.5 %, initial/codeword/final exact) but three child-calibrated
constants were low: **GKR = 72L² + 264L + 248 B** (L = log2 interactions; 44 KB at
L = 23, model had 8.5 KB), stacking 1,984 + 48·W, relations +5.8 KB + 432 B/height
doubling. E6 (one opening per column) gives nothing (next-row values needed).

**Corrected model** (`l4-study/models-C/ext2.py`, `run_ext2.py` → `run-ext2.txt`;
×15 + coset + multiproof + non-halving + pack, transcript +510 compressions):

| c_sha | settings | combo | + Gruen GKR | + next-row only for 30 % cols | + 230-col final circuit |
|---:|---|---:|---:|---:|---:|
| 19,448 | today 268/48 B, m=3 | 408,800 | 394,976 | 379,520 | 365,600 |
| 19,448 | z=32 + 42 B, m=3 | 345,176 | 331,352 | 315,896 | **301,976** |
| 28,288 | z=32 + 42 B, m=3 | 359,154 | 345,330 | 329,874 | 315,954 |

Sensitivity: each halving of final-circuit cells ≈ −12…−25 KB (the 15·2²⁷ domain cap
then admits a larger final blowup); cells 2²⁵·⁶ → ≈ 275 KB with the same levers.
So < 300 KB now needs, beyond the built levers: Gruen-style GKR (degree-(d−1) round
polys), next-row openings only where referenced, a final circuit with few total columns,
and fewer final cells (cheaper SHA AIR or fewer penultimate compressions). The real
verifier circuit's column/interaction/non-SHA cell counts (recursion lane) decide it.

**Recursion port measured** (`lane/pq-recursion-sha384` @ `5ea64c468`, report
`results/pq-recursion-sha384/README.md`). OpenVM v2.1 `crates/recursion` ported to
SHA-384/Ext12 (byte-identical transcript/Merkle vs `native_sha384_config.rs`, grinding
implemented); verifies real SHA-384/Ext12 child proofs; 4 tamper classes rejected *by the
circuit*. Stock Poseidon2 calibration: fixed point 8.79M cells, 256 KB at 100-bit, 1,537
cols. Ported, proven 4-level chain at a 20-bit query target: 716 → 6,388 → 7,403 → 7,516
compressions, 487–597 KB (compressions converge). 268-bit L1 proven: 1,318,194 B. 268-bit
L2 trace: 30,332 compressions / 958M cells (model 19,688: second round-0 commit for the
child vk/DAG + ≈ 3k blocks absorbing the child's column openings; proving needs ≈ 100 GB).
**Blocker: OpenVM's 46-AIR verifier has 3,481–3,923 columns → 322–365 KB of column
openings alone (+ ≈ 50 KB GKR, L = 25), independent of WHIR.** Columns cost twice:
wire bytes in the final proof and transcript SHA in the parent. ⇒ The final (and
penultimate) layer needs a purpose-built **narrow verifier circuit** (≤ ~500 opened
columns incl. preprocessed, ≤ 2²² interactions, one narrow SHA AIR, Ext12 verifier logic
as a small row-serial ALU), single round-0 commit (SHA `dag_commit`).

**Levers round 2** (`lane/pq-whir-levers` @ `ab3cfd969`, laws in `native/levers_laws.py`):
Gruen GKR + derived claims → **GKR = 48L² + 192L + 152 B** (measured, L = 23: 29,960 vs
44,408 B); Gruen on batch-constraint sumcheck (< 1 KB); next-row openings only for
referenced columns (vk mask; gas-failure5 −7.4 KB, but the L3 SHA AIR references 438/442
columns at the next row → ≈ 0 there; ext2's "next 0.3" rows are void for that AIR);
2-element PoW (z = 32 proves directly: 65.5 s/grind on 8 threads, z = 28 3.8 s);
max_constraint_degree 8 → 4 saves ≈ 3.5 KB. Gate 5 re-measured: 459,923 B (268/48 B) /
**389,561 B (z = 32 / 42 B, z proved)** at 2²⁶·⁴ cells, 460 cols. Model best point with
measured laws: **≈ 325 KB** at 460 final columns. Remaining gap must come from the
narrow verifier circuit (columns, next-row columns, interactions) and fewer cells.

**Weak-binding digests** (`lane/pq-weak-binding` @ `5af744ce6`, `weak-binding/ANALYSIS.md`):
41 B proven now (CMS19 constants and new Thm 4 with K = 0; −3 KB). 26–28 B proven *in
the note* (new, unreviewed Thm 4: QROM BCS with tolerated block equivocation via a
compressed-oracle potential) **conditional on H-rob** (block-robust WHIR rbr) → net
−35…−41 KB; needs position-indexed nodes, 48-B top levels, user U-7 decision. Running:
H-rob proof attempt; adversarial review of Thm 4.

**Slimmer SHA AIR** (`lane/pq-sha384-air2` @ `ed1ddf946`): base-8 digit words (k = 3),
bus residuals instead of operand columns, polynomial carry range checks: **7,524
cells/compression (was 19,448), 171+13 columns (was 442+18), 144 next-row (was 438),
14 interactions/row (was 43), degree 21**. All tests pass (10k vs sha2, 5,921/5,921
mutations, 13/13 bus forgeries). Modelled final layer (ext2 fixed point + measured
laws, 100 other columns): **283,692 B** at z = 32 + 42 B (was 336,453), 335,116 B at
today's settings. Cost: SHA-only prove 10× slower on CPU (degree-21 interpreted Ext12
DAG; k = 2: 291,389 B, 2.4× slower). Non-SHA budget for the narrow verifier: ≈ 100 columns.

**H-rob** (`lane/pq-weak-binding` @ `70bbb8c2e`, `weak-binding/HROB.md`; review 1 in
`REVIEW-1.md`: no fatal flaw in Thm 4, fixes 1–5 applied, H-rob(strong) dropped).
H-rob **fails for WHIR as specified/built**: shift-query answers y_{i,j} are not absorbed
before γ_i, so one equivocated leaf chosen after γ solves the combination equation
(quantum attack ≈ t²/2ⁿ ⇒ no digest < 32 B sound with today's order; 41/42 B unaffected).
**Fix WHIR-Y**: observe y_{i,·} before sampling γ_i (incl. final round): 0 proof bytes,
≈ +90 verifier compressions. With WHIR-Y, Thm R proves H-rob(shift) [T, unreviewed]:
26–27 B digests (c = 11–12, K = 5–7), net −34.8 KB (z = 32 levers) / −39 KB (268-bit).
Residual: [H-M], [H-outer] (outer protocol reads columns via the list at δ₀ + K/B₀),
reviews of Thm 4/Thm R, user U-7 decisions (WHIR-Y, position-indexed nodes, dedup,
48-B top levels, 384-bit FS chain).

**Narrow verifier circuit NV — measured fixed point** (`lane/pq-recursion-sha384` @
`f6596503d`, `results/pq-recursion-nv/README.md`). All non-SHA logic in one 69-column
role-multiplexed AIR (NvAir: verifier program, program binding, hashing glue, transcript
chain, sampling; degree 8, 48 interactions/row) + 5-col byte table + k = 3 SHA AIR:
**258 opened columns (OpenVM port: 3,481–3,923)**. Measured chain at a T = 20 test target,
all proofs verify natively, 7 tamper classes rejected in-circuit: fixed point A2 = A3 →
L1–L3 at **171,797 B** (510 cols incl. both SHA instances in that build, 2²⁵ interactions,
62.9M cells); step-6 build 168,437 B (2²⁴ interactions). 3 h 07 min for six levels,
19.3 GB. **Modelled final layer** (`extrapolate_nv.py`: measured NvAir structure and
per-query program costs + levers, ×15, coset, 42 B, z = 32, multiproof — levers not yet in
the circuit): **308,547 B** (power-of-two heights) / **298,881 B** (padding-free heights);
268-bit no-grinding: 363,519 / 359,535 B. Breakdown: WHIR 215–223 KB (≈ 2²⁵·⁹ cells),
relations 45 KB (25 KB openings, 17 KB degree-21 sumcheck). Remaining levers: next-row
mask (≈ 3 KB), 41-B digests (3 KB), 43-row SHA (≈ 1 KB), padding-free heights (≈ 10 KB),
weak-binding reserve (≈ 35 KB, conditional). Gaps: L2 doesn't yet check L1's app-verifier
program; levers not in circuit (needs levers backend on the CPU backend); real run needs
a ~2^38.8-element streamed LDE (multi-GPU / 100+ GB host).

**User decision 2026-10-17: approve 42-B digests, grinding z = 32, and WHIR-Y; keep going.**
Recorded as U-10 in `docs/zk-formal/V3-D3A-STUDY.md` §D (amends U-7 for the PQ track).
Padding-free heights implemented (`lane/pq-whir-levers` @ `561c934f7`, `tight_heights`:
commit only up to the last non-zero row in power-of-two chunks; zerocheck/GKR unchanged
over a virtual zero tail; measured exact on the dummy) — needs zero-row-valid AIRs; NV
model 308.5 → 298.9 KB.

## 2026-10-18 — correctness proofs; A-IC decision; full-memory run

* Box freed for the real run (arena workers w1–w3 stopped; zkbuild.slice 104G/108G; watchdog LOW=10). Restore afterwards.
* Protocol proof (`lane/pq-final-soundness` @ ae0ae8a7b; PROOF.md, GAPS.md, calc/bound.py): 2⁻¹³⁵·² end to end (2⁻¹³²·⁴ union over 7 layers), straight-line extraction, worst round 2⁻²⁶⁸·⁵⁵ (WHIR round 0, 236.55 + z). Conditional on T\* (G-1 multi-block squeeze not covered by any QROM FS theorem; G-2 PoW bits not tied to query blocks → 2⁻¹⁰⁵ without fix), NV-faithful, Base-faithful, A-IC. Minor: G-9/G-10/G-11.
* Circuit proof (`lane/pq-nv-circuit-soundness`; FAITHFUL.md): NV-faithful F1, F2, F4–F6 proven at 3c9d479ab after 6 soundness fixes (B1 fractional B-field, B2 child height, B3 free base-load coefficients → vacuous PoW / forgeable PVs, B4 42-B tail framing, B5 squeeze ids, B6 job swap; commits 2e36b0228, 09fead0bc, 274fe5ccf). ε_LogUp ≈ 2⁻³¹⁷·⁹. Single-cell perturbation over ~77M cells: no relevant undetected cell. **G1: the app statement was not passed up the recursion** — adopted fix: SHA-384 statement digest at level 1, re-exposed at every level, checked by V_d.
* User decision: accept A-IC as U-11 and fund research for a proven bound (research lane opened).
* Sent to the recursion lane: merge B1–B6 on top of 32fb63327, statement passthrough, T\*, then the real-settings chain.
* A-IC research (`lane/pq-aic-research` @ 0079ed29a, REPORT.md, LEMMA.md): no proven bound can remove A-IC in a query-only oracle model (Thm O; one case of Lemma E.3 sketched). BCG TCC'25, AROM, ROM PCD/accumulation, standard-model FS: none applies. User decision U-12: time-bounded recursive claim (τ = 2¹²⁸), A-IC(τ); final layer gets its own hash prefix. Lane closed.
* **Size regression (2026-10-18):** NV phase-2 `extrapolate_nv2.py` (lane/pq-recursion-sha384 @ 32fb63327+) gives final **323,955 B** at 268/z32/42 B (WHIR 242,562; GKR 32,408 L=24; relations 43,232; stacking 5,680) because the verifier program grew to 181,754 rows → 2^18 (NvAir 341,773 rows, cells 2^26.22). Supersedes the phase-1 298,881 B. 258-bit: 313,359 B. Directed: program < 2^17, tight_heights in the model, next-row-only openings, fewer interactions; MCA upgrade lane (O-1/O-2, −15…−45 KB est.).
* Prover latency (`lane/pq-prover-latency` @ d1a208ef7, LATENCY.md): critical path = zerocheck+GKR of the degree-21 SHA AIR in Ext12 (94–97 % of NV layer time). 4 sequential recursive layers ≈ 2.6 s mid / 0.8 s optimistic on 32 H200; end to end after execution, typical chunk, 32 H200: 0.83 / 2.7 / 15 s (opt/mid/pess). 2^32 grind = 125 s mean on 32 CPU threads (p99 2.5×). z = 24 inner, z = 32 final recommended. Design G (shared base proof) is the only real-time option. Biggest latency lever: cheaper SHA AIR (degree × DAG).
* Literature catalogue + NOVEL-FINDINGS register: lane/research-catalog @ 484ea27f8; prior art lane/novelty-prior-art @ 34920925e.
* Base + aggregation (`lane/pq-base-aggregation` @ 364aa29b3, DESIGN-BASE.md): design G adopted (one shared-transcript base proof over all GPUs → L1 → T1 → T2 → FINAL); no n-to-1 NV layer needed for segments (continuity = global bus terms; base PVs = chunk statement, hashed at L1 under tag 8). k-to-1 L1 (`build_l1_linked`) only for side proofs (P-PERF-8); 2-to-1 L1 measured 21.1M cells, 139,609 B, 845–932 s CPU, ≤5.5 GB; tamper tests pass. Base params pinned (b=1, m=16, k1=1/k=4, 2^24 per slice, z=24 base/inner, z=32 final): bound.py PASS 2^−134.88. MCA upgrade (`lane/pq-mca-upgrade` @ 6841b5f56): DKT26 m=64 → 313,759 B; + beyond-Johnson → 300,733 B (nv2); verification lane/pq-dkt-verify running. Risks: no cluster-wide shared-transcript SWIRL prover; NV can't verify preprocessed children; Base-faithful open for real segment AIRs.
* DKT26 verified (`lane/pq-dkt-verify` @ d9dc1c0e3) and **adopted by the user as U-13** (O-1 m = 64 + O-2 per-round table).
* **First measured real-settings chain** (`lane/pq-recursion-sha384` @ 6af52d94f, 7cdc8c90e; all levers, T\*, B1–B6, statement passthrough, final prefix; m = 3): A1 401,337 B → A2 473,565 → A3 481,125 (fixed point, program 259,430 rows) → **FINAL 416,171 B** at b = 2, log_h 21 (memory-limited; 64.9 GB peak, 45 min). Model matches every component within 0.5 %. Best final shape b = 7–8 needs ≈ 1 TB unstreamed: model 326,547 (m=3) / 316,351 (m=64) / 303,701 (O-2) / **299,277 B (O-2 + program cut)**. GKR L = 25 (full power-of-two heights; model corrected +2.5 KB). Biggest structural lever left: SHA AIR at degree 8 with ≤ 40 rotated columns (≈ −17.5 KB; proof opens 455 columns, 144 rotated from the SHA AIR). NvAir < 2^18 rows or 55 → 49 interactions/row: −2.5 KB.

## 2026-10-18 — O-2 implemented, NvAir L=24 (lane/pq-recursion-sha384 @ ee8fa9c99)

* U-13 O-2 implemented: per-round agreement table (code size, A_i, q_i; bound_mca.py rule,
  margin 0.05, m ≤ 64) serialised into the vk pre-hash; native verifier rejects non-canonical
  tables; NV reads q_i from the child vk. Default for PQ path (`PARENT_O2=0` disables).
  Test `o2_agreement_table` (altered entry / weaker self-consistent table rejected).
  gas-failure5 byte-identical without table (`ba042e71…`).
* NvAir 55 → 49 interactions/row (sample role reads GLUE digest rows directly): total
  2^24.98 → GKR L = 24. Margin is thin: any new NvAir interaction returns L = 25.
  Test `nv_sample_word_source_tamper`. Re-audit items: GLUE `dx` word sends, sample `w0`,
  O-2 table check.
* Extrapolation (best shape): m=3 324,003 / m=64 313,807 / **O-2 301,157 B**
  (WHIR 219,908, GKR 32,408, relations 43,280, stacking 5,344). Still 1.2 KB over;
  SHA AIR v4 (≈ −17.5 KB) is the closing lever.
* Open: check A_i for the real shapes against the DKT certificate grid (lane/pq-dkt-verify).

## 2026-10-18 — O-2 not yet certificate-backed (lane/pq-recursion-sha384 @ cf2262a24)

* With program cut: O-2 + L=24 = 299,277 B (cut worth only −1.9 KB at L=24; L=23 needs
  ≤ ~36 interactions/row + NvAir < 2^18 rows → 296,829 B).
* `dkt_cert_check.py`: no real shape's O-2 thresholds are covered by dkt_certs.json —
  grid A off by one from the backend rule at 2^19/2^20, fold sub-codes s=3,4 missing,
  no canonical certificates off 15·2^27. Until fixed only O-1 (≈313.8 KB) is backed.
* Actions: certificate-gated table with O-1 fallback (soundness fix, adopted; NV lane);
  new certification run on lane/pq-dkt-verify for the exact backend rule and shapes.

## 2026-10-18 — NV re-audit clean (lane/pq-nv-circuit-soundness @ c3c9393e0)

* Re-audit through 2bf42f573 (later commits to cf2262a24 don't touch the circuit): no new
  soundness bugs. Program binding re-anchored on Acc's early row (unpadded program);
  Invariant D* (hash rows = native T* oracle calls) proven; statement passthrough F3
  implemented + proven (`nv_statement_passthrough`). ε_LogUp ≈ 2^-317.6.
* Tests: all nv_ tests except nv_chain/nv_app_binding (over memory cap) pass in both digest
  modes; full perturbation sweep ~75M cells + 8.6M sampled at level 2: clean.
* Harness bug D1 (allowlist masking unnamed cols) fixed; revealed T* ctr/nwit undetected but
  benign. Open: GKR/batch/stacking on differential tests only; lo6 pinned by consumers only;
  carry bounds k=3 only. Re-audit needed if "4 program rows per binding row" lands.

## 2026-10-18 — cert-gated O-2 (59831ffb1) and SHA AIR v4 (lane/pq-sha384-air3 @ 34a427692)

* O-2 table now certificate-gated (fallback Johnson m=64 per round, rule recorded per round
  in vk). Backed figure with no certs: 313,807 B (311,745 B with program cut).
* SHA AIR v4: degree 9 (deg 8 costs +8.7 KB), 2 words/row, 83 cols / 73 rotated (v2.1 171/144),
  128 rows/compression, 17 interactions/row. KAT 1,008 compressions, 6,321/6,321 mutations,
  19 forgeries + padding attacks rejected; NV suite 42/42 both modes. FAITHFUL-v4.md unaudited.
* Bytes vs old v2.1 baseline (L=25, 55 int/row): m=3 315,811 / m=64 304,895 / O-2 292,541 /
  O-2+cut 288,117 (≈ −11.2 KB, not −17.5). Latency tail 2.67 → 2.32 s; CPU 1,024 compressions
  465 s vs 892 s.
* Next: merge v4 into NV with L=24 change, combined bytes (backed O-1 case likely ≈ 300 KB —
  borderline); audit FAITHFUL-v4.

## 2026-10-18 — v4 merged into NV (lane/pq-recursion-sha384 @ f59bc0770)

* Fast NV suite 51/51 both modes. SHA trace 2^20 rows × 17 int → with NvAir 2^19 × 49 total
  2^25.38 (L=25); program cut (NvAir < 2^18 rows) → 2^24.87 (L=24). L=23 out of reach.
* Combined: O-1 backed 304,943 B (no cut, L=25) / 300,399 B (cut, L=24);
  O-2 certified 292,589 / 288,165 B. Program cut is NOT yet implemented → now the priority;
  one certified O-2 round (~3 KB) would also close the gap.
* v4 audit (lane/pq-nv-circuit-soundness d043aa16f §V): no bug; standalone sweep 0 undetected;
  NV-port sweep pending.
* v4 NV-port audit done (lane/pq-nv-circuit-soundness @ 912187d21 §V): full sweep 4 fixtures ×
  2 modes, Sha512Air4/TableAir4 0 undetected; 44/44 + 43/43 tests; port reproducible byte for
  byte; ε_LogUp ≈ 2^-316.8. Next re-audit trigger: program-cut ops on the recursion lane.

## 2026-10-18 — O-2 certified for real shapes (lane/pq-dkt-verify @ 69e5df327)

* 129 certificates (93 round/fold sub-codes + 36 round-0 batching curves) for the backend's
  exact rule `AgreementTable::canonical`; Lean kernel 129/129 (222 theorems, std axioms).
  Old grid off-by-one was a bug in the --grid script. File calc/dkt_certs_o2.json.
* Final b7h20/b8h19, inner b6h19, both b2 chain shapes: covered and full bound passes →
  final O-2 bytes are certificate-backed.
* Base stress b6h21: round 0 must be J(64) (squared O-2 list with 2 commitments → 2^-231.8);
  +2 base queries; needs bound-aware per-round regime (soundness fix, adopted, NV lane).
* E2E vertical slice lane started (lane/pq-e2e-slice, user choice); GPU: CPU-only for now.

## 2026-10-18 — streamed commit: best-shape final measured (lane/pq-stream-commit @ 117d85604)

* All WHIR codewords streamed (recompute on query, top Merkle levels kept, no disk).
  b=2 final streamed is byte-identical (sha256 e5e526a2…), peak 64.4 → 35.5 GB.
* Best shape b=7, ×15, log_h 20, on the measured 7cdc8c90e chain (no O-2/v4/cut):
  m=3 339,747 B (model 339,370), m=64 330,149 B (model 329,478); peak ~39 GB, ~61 min.
  Model validated within 0.2 % at the target shape. GKR temp tables now set the peak.
* Next: re-run the ~3 h chain on the recursion lane's final circuit (v4 + program cut +
  cert-gated O-2) and prove the streamed final → the measured < 300 KB number.

## 2026-10-18 — program cut done (lane/pq-recursion-sha384 @ 3c4324e8c)

* Program rows (Fib probe) 125,782 → 79,840 (−36.5 %): Merkle level 10→5 rows, butterfly 7→5,
  factorised eq, Horner final poly, Horn2 round-0 leaves, cheaper x15 index. NvAir 74 cols,
  49 int, deg 9, 40 ops (table full). Tests: backend 230, fast NV 54 ×2 modes.
* Model at fixed point: NvAir 255,702 rows (< 2^18, margin 2.4 %, relies on v4 DAG correction),
  interactions 2^24.87, L=24 → **O-2 287,037 B / O-1 297,999 B** (penultimate on Johnson).
* Next: stream lane runs the real chain + streamed final on this head (measured number);
  auditor re-audits new ops (§W); DKT lane certifies penultimate b8/n18/k1=2.
* Program-cut re-audit clean (lane/pq-nv-circuit-soundness @ 90d08fa4f §W): binding unchanged,
  Horner-chain completeness argued + builder hardening `assert_horner_chains`, x15 index unique
  (p−1 rejected, completeness loss ≤ #q/p); tests 49/49 + 46/46; sweep 5 fixtures × 2 modes clean
  (new Horn2 fixture; harness `wit` allowlist gap fixed).

## 2026-10-19 — penultimate certification (lane/pq-dkt-verify @ fb0efdb11)

* The modelled penultimate b8 h20 k1=2 is infeasible (domain 15·2^28 > 15·2^27); size_cut3.py
  lacked the log_h+b ≤ 27 bound. Buildable best b7 h20 k1=2 lf6: certified, final stays 287,037 B.
* dkt_certs_o2.json: 173 entries, 164 Lean-kernel proved; 9 round-3 codes (k=2^10, h20 k1=2)
  only engine/#eval checked (kernel OOM at 24 GB) → gated to J64 (+1 query, ≈0 B).
  Decision (soundness rule): certificate gating uses kernel-proved entries only.
* lane/pq-recursion-sha384 @ 819beab10: domain bound in search; penultimate b7 h20 k1=2 lf6
  (q [41,35,27,22→23]); kernel-only gating via NEARPROOF_DKT_EXCLUDE (DKTCertsO2_big.keys);
  loader bug fixed (no longer counts keys inside `_no_certificate`); auditor hardening merged;
  slow app-binding/opening tests pass (17.4 GB). Model 287,037 B; NvAir 255,976 (2^17.97).
  Without O-2: 301,743 B at L=25 — the < 300 KB result now depends on the certificates.

## 2026-10-19 — E2E slice result (lane/pq-e2e-slice @ 480bf27f4)

* Test size, end to end: real direct-Wasm call (Lean fixture) → base (EXEC/CODE/RANGE + STUB
  ChunkStmtAir) → L1 → L2 (bound) → FINAL (bound, fixed point) → native V_d with new
  `check_final_program`. Accepts honest; rejects wrong S_S/ctx/S_0, swapped chunks, tampered
  PV, inner-domain proof, wrong pinned level/program. Sizes: base 54,061 B, NV levels 136,089 B.
* **G1 critical:** with child PoW, the NV program depends on the proof (PoW job ids from global
  squeeze-block count; rejection sampling). Chunks A/B L1 programs differ in 4,609 rows; can't
  pin program → V_d unsound (forged 776-row verify-nothing final accepted without the check).
  Fix assigned to recursion lane (soundness fix, adopted). Stream-lane measurement provisional.
* **G2 high:** real pinned base proof 921,857 B ([536,256,83,50,36]); L1 over it is 623,802
  program rows (ISA ceiling 2^21 NvAir), ~190–230 GB est. — not provable here; app-table
  binding makes L2 carry the L1 program. Needs a size-independent binding mechanism.
* Claim to verify: measured 416 KB chain ran with program binding off at phase A/FINAL.
* G3/G4 stubs (ctx, roots, receipt); G5/G6 code in statement, base vk varies with code length;
  G7 build_l1_linked not ported (28 rejected hunks).

## 2026-10-19 — measured final 287,477 B, provisional (lane/pq-stream-commit @ 89a0045de)

* Chain on 819beab10 + streamed overlays, certs + kernel-only exclude: penultimate b7 h20 k1=2
  q[41,35,27,23(J)], final b7 h20 k1=1 q[41,38,29,23] all O-2. FINAL **287,477 B** vs model
  287,037 (+0.15 %): WHIR 224,610 / GKR 32,408 / relations 24,244 / stacking 6,016.
  NvAir A3 248,964, FINAL 252,636 rows (3.6 % under 2^18); interactions 2^24.87 → L=24.
  1 h 55 min, 25.6 GB peak. A3 child saved (sha256 9ad8ad51…).
* PROVISIONAL: `bind` (child-program binding check) off at A1–FINAL (app table rows present);
  G1 (program depends on child PoW) unfixed. Re-run after G1 + binding-on.
* Infeasible shapes found: b8/h20 (domain), b8/h19 (v4 SHA trace 2^20 > stacked 2^19 → penultimate
  needs log_h ≥ 20; add to model). Backend soundness print (255.1) ignores the O-2 table — fix.

## 2026-10-19 — WASM base first family proven (lane/pq-wasm-base @ 2ba1e2fe7)

* Lean `wasm_base_sound` (no sorry, std axioms): checker-accepted fn + AIR relation + derived PIs
  ⇒ spec `NearSpecV3.Wasm.run` finishes in N−1 steps, gas R·S, stack = public result; explicit
  domain conditions D1–D5, N·(maxFee+1) < p, R·S ≤ g0 < 2^64. Lean→JSON→Rust replay + difftest.
* Proof found a real SHIFT AIR bug (range-checked w·q instead of q) — fixed, no cost change.
* Tests: 47/47 KAT (Python/Lean/Rust), 29/29 tamper; pinned 2^24 proof 948,706 B, 240 s, 9.9 GB.
* Cost: 349 cell-eq/op active (529 padded); worst family op ~500–600 (≈ model 546); univariate
  ≈ 1.6–1.7× cheaper. SHIFT/CMP 2× PERF drafts → first optimisation targets.
* Checkpoint: preprocessed (or PREP-linked) code table REQUIRED before full ISA (code binding via
  PV interactions grows with program; vk per program) → NV must verify preprocessed children
  (also needed for G2 binding). Memory: stack/locals channel proven under D3 (no-discard).

## 2026-10-19 — G1 fixed, binding on everywhere (lane/pq-recursion-sha384 @ 717eb518e)

* G1: PoW witness carried in hash rows, run blocks reuse first block's witness via chain bus;
  program = f(child vk/shape). `nv_program_pow_identity`: 4 PoW children, different transcripts,
  byte-identical programs. NvAir 77 cols / 51 int; ≈ +150 B.
* Binding on at every NV-child level; FINAL now runs the uniform fixed-point program under the
  final domain with binding (old unbound FINAL was a soundness gap in all earlier 287 KB figures).
  V_d (`nv/vd.rs`) test `nv_vd_pinned_program`: forged verify-nothing final rejected.
* Model: final shares penultimate shape → (7,20,1,4,7) 290,477 B (L=25, NvAir ~270k) or
  (7,20,2,4,6) 300,191 B (L=24); ~8k NvAir rows of cuts → ≈ 287.9 KB. Real base app table
  (400–624k rows) → 315.7–321.4 KB → G2 (preprocessed program commitment) required.
* Stream lane re-running non-provisional; auditor §X; preprocessed lane implements G2.

## 2026-10-19 — NV verifies preprocessed/cached children (lane/pq-nv-preprocessed @ 9761585a5)

* No AIR/role change; 8 generator sites (P1–P8); one-commitment programs byte-identical.
  Tests: honest/tampered root/opening/vk/table-swap; cached 3 and 5 commitments; O-2 round-0
  rule; 19,365 single-element mutations 0 mismatches; fast suite 67/67 both modes.
* Cost per extra commitment per round-0 query: 7 + 2^k1·⌈w/2⌉ + 5·depth rows + depth+1 SHA
  compressions (independent of table size → merge fixed tables). L1 over pinned base: +80k rows
  (b=1) per extra commitment.
* G2 via CACHED program commitment (preprocessed would be circular): final ≈ 295.7–296.1 KB
  (293.2 with ~1k row cut); app-table binding with real L1 would be 315.7–321.4 KB.
* Decisions: CODE cached + bound through statement; BYTE/RANGE committed; base stays SWIRL;
  WASM base fan-out approved (div/rem, memory, locals/globals, calls). L1 ISA ceiling fix
  assigned to recursion lane. CPU prover lane started (byte-identical rule).

## 2026-10-19 — WASM base: cached CODE + div/rem (lane/pq-wasm-base @ 603710124)

* CODE cached, `code_root` a statement component; V_d checks sha256(code) = code_hash and
  recomputes code_root; base vk depends only on #locals. Lean hypothesis `CodeOK`. Tamper 30/30
  (a forged unfetched CODE row passes AIR + native verifier, caught only by the code_root check).
  Base proof 1,263 KB pinned (408 s, 12.8 GB) — not sent to V_d.
* div/rem i32/i64 with traps: DIV AIR (95 cols, deg 6) + DRAIN; status 1/2; carry range-check hole
  found pre-proof and fixed; `wasm_base_sound` extended to traps; KAT 63/63; difftest OK.
* Cost: mixed loop 430 cell-eq/op (568 padded); div-only 1,226/row (2.2× model 546).
* Next: shared Lean relation refactor (memory pages, globals, frames) → families 2–4.

## 2026-10-19 — bound chain fails at L3 (lane/pq-stream-commit @ a12b65b77)

* Real-settings chain on 717eb518e (b7 h20 k1=1, all O-2): L1 261,843 B; L2 289,493 B (binds L1
  via app table; NvAir 257,212 rows, interactions 2^25.4 → L=25); L3 builder fails "program
  binding": with tight heights the program depends on the child's committed heights (L1 tiny →
  L2 program 133,154 rows vs L3 142,517). BIND needs equal programs → FINAL/V_d never reached.
  Test nv_vd_pinned_program missed it (debug children with equal heights).
* Assigned to recursion lane with G2 (options: heights as witnesses; per-level pinned program
  constants until convergence; tight heights off). Converged program ≈ 271k NvAir rows (> 2^18).
* Audit §X/§Y (lane/pq-nv-circuit-soundness @ 9eab7f2d2): G1 fix, bound FINAL + V_d, and NV
  preprocessed/cached children — no soundness bug. Top-level: V_d accept under pinned program ⇒
  chain to app proof under app vk with statement digest passthrough; ε_LogUp ≈ 2^-316.6 per level.
  Native R5 (cached trace + tight heights, device path) is a completeness bug → commit cached
  traces non-tight. Note: real-height chains are not buildable yet (L3 heights issue above).

## 2026-10-19 — WASM base families 2–4 (lane/pq-wasm-base @ ce7a815ec)

* Shared relation refactor done; family 2 linear memory (tamper 44/44), family 3 globals
  (proved end to end, tamper 52/52), family 4 calls (CALL/RET/FUNC chips, step_call /
  step_return proven, FUNC table bound through statement; budget hi-part range check added after
  the Lean proof exposed it). KAT 73/73 (incl. recursion fib10, trap two calls deep); difftest OK.
  Call tamper runs in progress. Next: DIV/SHIFT/CMP optimisation.

## 2026-10-19 — G2 built, L3 heights fixed (lane/pq-recursion-sha384 @ 9159123be)

* G2: per-level cached program commitment (P0..P3); child check root = C_M at anchor level,
  else BIND; FINAL single-commitment, pinned by V_d. App table removed. NvAir 76 cols / 48 int.
* Heights: anchors + prover-side tight-height floor (`set_tight_floor`, explicit zero rows, no
  verifier change). Real bound chain with differing heights L1→L5→FINAL converged (96,390-row
  program), V_d accepted (test size, 2 h 43). V_d forgery test passes (prog_log 17).
* Merkle level 4 rows; addresses 20→24 bits (zero cost) → L1 over real base fits the address space.
* Model: FINAL b7 h20 k1=1 k4 lf7 293,101 B at L=24 (NvAir 256,031, 2.3 % under 2^18).
* CPU fast prover (lane/pq-cpu-prover @ 6134476fc) byte-identical on real layers → used for the
  G2 measured chain (stream lane). Auditor §Z on G2.

## 2026-10-19 — G2 GATE (user-defined)

Pass only if all four hold:
1. real-settings FINAL bytes ≤ ~296 KB (model 293,101 B);
2. V_d accepts the real FINAL under the pinned program;
3. forged verify-nothing FINAL rejected by V_d at real settings (and accepted without the program
   check, showing the test is live);
4. the chain reproduces from a clean deps setup: identical proof sha256s from a fresh setup in a
   new directory, by an independent agent, using MANIFEST.json (lane/pq-stream-commit g2-gate/).
Gate run: lane/pq-stream-commit (G2 9159123be + fast CPU prover 6134476fc + streamed overlays).

## 2026-10-19 — classical NEAR AIRs reusable on PQ stack (lane/pq-d1-envelope @ 7cd1a7135)

* Same base field (BabyBear), same row conventions, 1-bit multiplicities (grand product → LogUp,
  D1 mult bound 1.196·10^9 < p). 23/30 nearAirV3D1 tables proven unchanged on SWIRL with real
  D1a fixture traces: 1,261,284 B, 82 s/6 thr, tamper 14/14.
* Overruns: opened columns 5,612 vs 1,024 (SHA-256 table 1,085); 2^22 fixed tables (99.6 % of
  2.5 G cells); AIR count 33+1 vs 32; public tape (64 MiB) → cached table; native Ed25519 in
  verifier (design item); min height 4; per-table height caps to enforce.
* Lean: extractV3 + table/link/factor proofs transfer verbatim; new: generic SWIRL⇒HoldsP lemma,
  multBound < p, vk⇔Lean identity, tape binding (≈ 7–11 agent-days est.).
* Decision (after external advice): port proven state tables (D0a first, then D1), keep
  direct-Wasm for execution, join later. Lane lane/pq-state-port started.