# PQ proof-size levers on the SHA-384/Ext12 SWIRL stack: implementation, measurements, spec

Lane `lane/pq-whir-levers`, 2026-10-17. Native prover/verifier only (no circuit).
Every number marked **measured** comes from a run log in `logs/`; **model** numbers
come from `native/levers_model.py` / `native/final_layer_model.py` /
`l4-study/models-C/ext.py`; **extrapolated** numbers apply measured scaling laws
(stated per row). The full tables are produced by `native/levers_measured.py`
(`levers_measured.txt` here).

## Build

```sh
native/setup_levers_deps.sh          # NEARPROOF_PQ_DEPS (default /data/illia/nearproof-deps/pq-levers)
                                     # = setup_native_deps.sh tree + patches/stark-backend-levers.patch
python3 airbender/direct-wasm/prepare_native_sha384_levers.py --literal-source <input> --out <out>
cd $NEARPROOF_PQ_DEPS/native-sha384 && cargo build --release --locked
```

Files: `native/patches/stark-backend-levers.patch` (backend: k1, multiproof,
non-halving domains, `MerkleHasher::hash_coset` hook, lever codec, soundness
calculator, sequential-column LDE), `airbender/direct-wasm/native_sha384_levers_config.rs`
(SHA-384 hasher/transcript: digest width, coset leaves, grinding),
`native_sha384_levers_driver.rs` (env-driven profile, dummy AIR, census, negative tests,
grinding benchmark). Lever environment variables are listed at the top of the driver.

**Defaults are upstream:** with no lever variables, the levers backend + levers driver
re-prove gas-failure5 **byte-identically** (sha256 `ba042e71…`, 378,849 B; transcript
vectors identical to the recorded ones; 10,227 verify compressions). Checked again
after every backend change (`logs/r-default.log`).

## Lever status (gas-failure5 child, measured; model at the measured query schedule)

| lever | parameter | status | bytes (Δ vs 378,849) | verify SHA-384 compressions | model check | negative tests |
|---|---|---|---:|---:|---|---|
| 1 grinding | `query_phase_pow_bits` z (also folding/mu) | done, z ≤ 28 | z=16: 359,489 (−19,360); z=20: 354,561 (−24,288); z=24: 351,073 (−27,776) | 9,684 / 9,541 / 9,443 | auth/leaf/node exact | wrong query/last-round/folding/mu witness rejected |
| 2 digest truncation | Merkle digest 48 or 42 B (SHA-384 truncated) | done | 346,695 (−32,154) | 10,220 | auth exact (5,354 × 42) | encoding provably drops the truncated tail; domain-separated framing (4 distinct node vectors) |
| 3 per-round folding | first-round k1 | done | k1=2: 408,700 (+29,851); k1=1: 485,776 (+106,927) | 10,355 / 12,100 | exact | — (it pays only for wide stacked matrices; see gate 5) |
| 4 list multiplicity | m (ListDecoding) | done (already a backend parameter; now an env knob) | m=8: 370,497 (−8,352) | 9,982 | exact | — |
| 5 coset-as-one-message leaf | one SHA-384 message per WHIR leaf | done | 378,849 (±0, as predicted) | **6,956** (gate 2) | leaf+node 6,212 = model exactly | last coset element mutation rejected |
| — multiproof (implied by the model's auth term) | batched canonical multiproof per round | done | 288,528 (−90,321) | 8,616 (native, dedup) | auth 166,656 vs 167,952 expected | sibling removed/appended/reordered rejected |
| 6a non-halving domains (E5) | keep domain size each round | done | 358,320 (−20,529) | 9,587 | exact | (lever-field mismatch rejected) |
| 6b one opening per column (E6) | — | **skipped: no gain (analysis below)** | | | | |
| all: coset+42 B+multiproof+m=8+z=24 | | | **246,016 (−132,833)** | **4,898** | auth within 0.4 % | 10 cases |
| all + E5 | | | 236,734 (−142,115) | 4,790 | | 10 cases |

Prover time is unchanged except E5 (8 s → 41 s on the child, Ext12 domains stay large).
All runs: 8 threads, CPUs 8–15/24–31, ≤ 24 GB.

### Grinding cost (measured, `logs/r-bench.log`)

SHA-384 PoW attempts (1 compression each): **2.9–5.3 × 10⁷ /s on 8 threads** (Zen 5,
shared machine; the low figure was under contention). Mean grind: z=16 1.5 ms, z=20 16 ms,
z=24 0.35–0.64 s. **Extrapolated z=32: 2³²/(2.9–5.3·10⁷) ≈ 81–148 s per grind on 8 CPU threads**,
i.e. 5–10 min per final proof with 4 query phases (one grind per WHIR round). On an
H200 (SHA-512 ~10¹⁰/s class, not measured) this would be well under a second per round.

### Gate 2 (coset hashing): **confirmed**

Predicted 6,947, **measured 6,956** compressions. Leaf (858 blocks: 82×1 + 194×4) and
node (5,354) counts equal the model exactly; the transcript part is 744 instead of 733
blocks because the new framing prefix draws different challenges and rejection sampling
needed 11 more squeezes (random, not structural). Proof bytes unchanged, as predicted.

## Gate 5: shape-equivalent final layer

Dummy AIR (driver `mod dummy`): **460 columns**, 2^h rows, one degree-2 transition
constraint per column using the next row (as a SHA round AIR does), one balanced LogUp
bus (2 interactions/row). Shape = `levers_model.best()` for 2^26.4 cells with k1 allowed:
**b=8, k1=1, k=3, log_h=19, log_final=9** (q = [69,69,55,46] at 268/m=8; [58,58,47,39] at 226).

**Memory limit:** 2^26.4 cells needs a 2^27 × 169 base-field codeword (≈ 86 GB) plus a
2^26-leaf round-0 tree (k1=1) — far above 24 GB. Peak RSS is ≈ 14 GB of W-independent
state (round-0 tree with 2^26 leaves, round-1 Ext12 codeword on 2^26 points) + 0.55 GB per
stacked column, so **W ≤ 15 was measured** (h = 12, 13, 14 → W = 4, 8, 15; 16.1 / 18.4 / 22.3 GB).
The full-size proof is extrapolated per component with laws that were **exact at all
three widths**: initial = q0·2^k1·W·4 B, stacking = const + 48 B per stacked column,
everything else in WHIR independent of W.

Measured (W ≤ 15) vs model at the same W (`levers_measured.txt`):

| setting | h | W | measured | model | Δ |
|---|---:|---:|---:|---:|---:|
| today 268-bit / 48 B (+m=8, k1=1, coset, multiproof) | 12 / 13 / 14 | 4 / 8 / 15 | 351,788 / 355,580 / 361,220 | 340,609 / 342,817 / 346,681 | +11.2 / +12.8 / +14.5 K |
| z=32-equivalent: 226-bit queries, 42 B (proved at z=24, target 250) | 12 / 14 | 4 / 15 | 291,598 / 304,334 | 283,083 / 288,187 | +8.5 / +16.1 K |
| z=32 at today's 268 (236-bit queries), 42 B | 12 | 4 | 301,222 | 291,363 | +9.9 K |
| upstream, no levers (m=3, b=6, k=3, log_h=21) | 14 | 4 | 477,097 | 461,889 | +15.2 K |

Line by line at h=14, today setting: **auth 187,728 vs 188,736 model (−0.5 %)**,
initial 8,280 = model, codeword 65,280 = model, final poly 24,576 = model, WHIR small
1,363 vs 1,380 — **the WHIR model is accurate**. The gap is entirely in the three
constants the model calibrated on the tiny child:

| component | model constant | measured law | at the 2^26.4 final layer |
|---|---:|---|---:|
| GKR | 8,456 | **72L² + 264L + 248 B**, L = GKR depth (exact on the dummy, L=13–15, and on the L3 SHA-384 AIR lane's runs, L=19/21/23 with 43 interactions/row ⇒ L = log2(rows)+5) | **44,408** (L=23: SHA AIR at 2^18 rows) |
| stacking | 1,840 | 1,984 + 48·W (one Ext12 opening per stacked column) | **10,096** (W=169) |
| relations | 2·cols·48 + 3,112 = 47,272 | 2·cols·48 + 5,784 at h=12, +432 B per doubling of height (degree-2 dummy; the SHA AIR is degree 4: 49,432 at 2^18 with 442 cols) | **52,344** |

**Extrapolated full-size gate-5 proof (2^26.4 cells, W=169, GKR at L=23):**

| | today 268-bit / 48 B | z=32 / 42 B |
|---|---:|---:|
| auth | 187,728 | 142,170 |
| initial (exact law) | 93,288 | 78,416 |
| codeword | 65,280 | 55,296 |
| final polynomial | 24,576 | 24,576 |
| WHIR small (+16 B for a 2-element z=32 witness, analytic) | 1,363 | 1,361 |
| relations | 52,344 | 52,344 |
| GKR (L=23) | 44,408 | 44,408 |
| stacking | 10,096 | 10,096 |
| other | 73 | 67 |
| **total (extrapolated)** | **479,156** | **408,734** |
| model (`levers_model.layer`) | 431,689 | 359,643 |
| upstream without levers, same cells (extrapolated / model) | 625,561 / 582,945 | |

At 2^26.6 cells (W=195): 494,842 / 422,132 extrapolated vs 446,041 / 371,707 model.

**Gate 5 verdict.** The levers deliver what the model says inside WHIR (−146 KB vs
upstream at today's settings, −217 KB with z=32 + 42 B), but the model's non-WHIR
constants are **≈ 47–49 KB too low at final-layer scale** (GKR +36 KB, stacking +8 KB,
relations +5 KB). Carried into the L4-C fixed point (its "levers, COMBO+E5" point is
263,884 B at W=111 and assumes GKR+stacking+other = 11,157 B and relations = 25,192 B,
i.e. 48 B/column after E6): GKR +35,952, stacking +5,472 (W=111), relations +4,172
(measured constant and height growth), other −788 give **≈ 309 KB with E6**; E6 is not
available (below), which adds another +22,980 → **≈ 332 KB. The < 300 KB final layer is
not reached by these levers plus ×15 domains alone; the GKR term is now the largest
correctable item.** (This combination is a
model-level statement: ×15 domains, the penultimate's in-circuit SHA count and the
final circuit's interaction count are not measured here.)

Native verify of the gate-5 proof (measured, with multiproof dedup): 6,399 compressions
(today) / 5,709 (z=32/42 B). The in-circuit verifier without dedup would pay 7,065 /
5,967 Merkle+leaf compressions at W=169 (model, validated exactly on the child) plus
≈ 1,435 transcript compressions (measured; the model's 733 + final-poly term assumes
≈ 925 — the 920 column openings alone absorb 345 blocks).

## Skipped / not available

* **E6, one opening per column: no byte gain.** The zerocheck verifier evaluates the
  (nonlinear) AIR constraints at r on local *and* next-row values, so the prover must
  send both claimed values; a shift sumcheck only replaces the second PCS opening, and
  SWIRL's stacking reduction already batches local and rotated claims into one WHIR
  opening. The backend already sends one value per column for AIRs without next-row
  references (`need_rot`). The model's −14…−22 KB for E6 should be removed. (A per-column
  rotation mask saves only on columns never read in the next row; for the L3 SHA AIR
  most state columns are.)
* **z = 32 proving:** a PoW witness is one BabyBear element (< 2^31 values), so z ≥ 29
  needs a 2-element witness (+4 B per round). Measured at z ≤ 24; the z=32 query
  schedule was proved exactly (target 250 with z=24 gives the 226-bit schedule of
  258−32) and the size difference (+16 B) and time (above) are analytic.
* **E5 at the gate-5 shape:** out of memory (25 GB; the round-1 Ext12 codeword stays at
  2^27 points). Measured instead at log_h = 17 (same b, k1, k): 314,084 → 303,332 B
  (−10,752; codeword −9,984), prover 1.8×, memory 1.65× (`logs/e5-*.log`).

## Spec (for the in-circuit verifier)

All levers are parameters; the defaults reproduce the upstream profile exactly.

**Parameters.** `WhirLevers {k_first, multiproof, keep_domain}` in `WhirConfig.levers`
(serde-skipped when default); SHA levers `{digest_bytes ∈ {48,42}, coset_leaf}`;
grinding `mu_pow_bits`, `folding_pow_bits`, `query_phase_pow_bits` (existing fields);
list multiplicity `m` in `WhirProximityStrategy::ListDecoding {m}`.

**Binding.** If any `WhirLevers` field is non-default, the verifying-key pre-hash uses
version word `0x4c560003` (instead of 3) before `len_u64 || postcard(pre_vk)` and the
lever fields are serialized; proofs carry codec version `0x4c560003`. SHA levers are
bound through the hash framing (every hash, including the vk pre-hash and the transcript
initial state, changes).

**Hash framing.** `H(tag, parts) = SHA-384(prefix32 ‖ tag_u8 ‖ Σ(len_u64le ‖ part))`.
prefix32 = `nearproof-native-sha384-ext12-v4` when digest_bytes=48 and coset_leaf=0,
else `nearproof-sha384-ext12-v5-w{DD}-c{C}` (DD = digest bytes, two digits; C = 0/1),
exactly 32 bytes. Tags: 0 row leaf, 2 transcript init, 3 observe flush, 4 observe
commit, 5 squeeze, 6 coset leaf, 7 PoW.
* **Digest:** the first `w = digest_bytes` bytes of the SHA-384 output (42 B = 336 bits).
  On the wire and when absorbed (tag 4) a digest is exactly w bytes.
* **Node:** `SHA-384(np8 ‖ left_w ‖ right_w)` truncated to w; np8 = `NPQ4NODE` (default)
  or bytes `'N','P','Q','5', w, C, 'N','D'`. 8 + 2w ≤ 104 B: one compression.
* **Leaf, coset_leaf = 1 (lever 5):** one `H(6, [payload])`, payload = the 2^k rows of
  the fold coset in coset order t = 0..2^k−1 (row index `y + t·2^(log_dom−k)` for leaf
  y), each row as canonical u32 LE words: round 0 = the W stacked-matrix columns of one
  commitment (each commitment has its own tree), later rounds = the 12 base coordinates
  of one Ext12 value. Cost ⌈(payload + 58)/128⌉ compressions (k=3 Ext12: 4; round 0
  with k1=1, W=169: 12).
* **Leaf, coset_leaf = 0 (upstream):** each row hashed with tag 0, then a binary subtree
  pairing t = (2i, 2i+1) upward (2^k − 1 nodes).
* **Tree:** leaves y ∈ [0, 2^(log_dom−k)); node(l+1, i) = node_hash(node(l,2i), node(l,2i+1));
  path = siblings bottom-up; root = commitment.

**Transcript** (unchanged except PoW): 48-byte state; `observe` appends the canonical
u32 LE word to `pending`; a squeeze or commit first flushes (`state = H(3,[state,pending])`
if pending is non-empty); `observe_commit(d)`: flush, `state = H(4,[state, d_w])`;
`sample`: if the 12-word cursor is exhausted `state = H(5,[state])`; take the next u32 LE
word n, accept iff n < 4,026,531,842, return n mod p; `sample_bits(b) = sample() & (2^b−1)`.
**PoW** `check_witness(z, w)`: z = 0 accepts and changes nothing; else flush,
`s' = H(7, [state, w_u32le])` (101-byte message, one compression), accept iff the first z
bits of s' (MSB-first, bytes 0, 1, …) are zero; then `state = s'` and the cursor is
exhausted. Witness: one canonical BabyBear element (z ≤ 28 implemented). Order (backend):
mu PoW before μ; folding PoW after observing each sumcheck round's (s(1), s(2)) and before
α; query PoW after the round's commitment + OOD value (final polynomial in the last
round) and before the query indices.

**WHIR schedule.** Rounds n = 1 + ⌈(h − k1 − log_final)/k⌉ if k_first ≠ 0, else
⌈(h − log_final)/k⌉; round i folds k_i (k_0 = k1, others k); log_dom_0 = h + b,
log_dom_{i+1} = log_dom_i − s (s = 1 halving, s = 0 keep_domain); rate_0 = b,
rate_{i+1} = rate_i + k_i − s; q_i = ⌈(target − z_query)/bits(rate_i)⌉ with
bits(ρ) = −log2(2^(−ρ/2)(1 + 1/(2m))) in the list regime. Query index
`sample_bits(log_dom_i − k_i)`; point ω_{log_dom_i}^index; folded point (·)^(2^k_i).
Round-0 commitment trees have 2^k1 rows per leaf; the round-i codeword tree (opened in
round i+1) has 2^k rows per leaf. The final check uses t = Σ k_i and slices alphas after
Σ_{r≤i} k_r. log_final_poly_len = h − Σ k_i.

**Multiproof** (final layer only; data-dependent, not meant for the circuit): per tree
per round, process levels leaf → root; at each level iterate the known node indices in
ascending order; a node whose sibling is not known emits that sibling's digest (next
from the stream); parents become known. Duplicate query indices collapse (their leaf
digests must agree). The verifier must consume the whole stream and end at the root.

**Lever proof format** (`WhirProof::encode_levers`, `proof.rs`): k_first u8,
multiproof u8, keep_domain u8, then the upstream fields with each tree's paths encoded as
either `u32 count + digests` (multiproof) or `u32 depth + q·depth digests`.

## Blockers / next steps

1. **GKR term (≈ 44 KB at L=23)** is the largest item the model missed. Levers to test:
   fewer interactions per row in the SHA AIR (each halving ≈ −3.5 KB), or a shallower /
   batched GKR. Needs the recursion lane's final-circuit interaction count.
2. **Stacking openings (48 B × W)**: larger log_h (×15 domains lift log_h + b ≤ 27)
   reduces W and these bytes together with the initial term.
3. Update `levers_model.py` / `ext.py` constants: GKR(L), stacking(W), relations(h, degree),
   remove E6, transcript ≈ 1.4k compressions at final-layer shape; re-run the L4 fixed point.
4. z ≥ 29 needs a 2-element PoW witness (backend `query_phase_pow_witnesses` type).
5. Full-size gate 5 (W=169) needs ≈ 100 GB or a streamed commit (per-column LDE into
   incremental per-leaf SHA states, ≈ 3.6 GB for 2^24 states; recompute opened rows).
