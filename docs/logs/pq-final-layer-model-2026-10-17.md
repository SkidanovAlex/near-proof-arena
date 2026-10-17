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
