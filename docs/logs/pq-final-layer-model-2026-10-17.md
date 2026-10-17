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
