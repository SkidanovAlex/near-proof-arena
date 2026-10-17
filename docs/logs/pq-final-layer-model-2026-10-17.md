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
