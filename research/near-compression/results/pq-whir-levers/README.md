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
All runs: 8 threads, CPUs 8–15/24–31, ≤ 24 GB. Upstream backend tests on the patched
tree: 40 lib + 102 integration tests pass (`cargo test -p openvm-stark-backend --tests`).

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

## Round 2 (coordinator request after gate 5): GKR, zerocheck, next-row, wide PoW

All behind default-off `WhirLevers` flags (`gruen_gkr`, `gkr_derive_claims`, `gruen_zerocheck`,
`next_mask`, `wide_query_pow`) plus the `max_constraint_degree` parameter; gas-failure5 at defaults
re-proved byte-identically after every step. Laws for fixed points: `native/levers_laws.py`
(self-checking); tables: `levers_measured.txt` (round-2 section first).

| lever | effect (measured) | law | negative tests |
|---|---|---|---|
| Gruen GKR (send s(1), s(2); verifier rebuilds s from `eq(ξ_t,X)·t(X)`) + derived claims (p_xi_1 per layer, root q0) | child GKR 8,456 → 5,784 B; dummy L=9/11/13: 5,768 / 8,072 / 10,760; **SHA AIR 2^18 (L=23): 29,960 vs 44,408 upstream** | **48L² + 192L + 152** (was 72L² + 264L + 248) | s(1), s(2), root and layer claims, dropped s(3) / derived fields set non-zero |
| Gruen batch-constraint sumcheck | −48 B per round in which no trace is exhausted (dummy: all rounds; SHA AIR: 4 rounds, the table AIR has 64 rows) | relations law below | dropped eval set non-zero, batch eval |
| `max_constraint_degree` = real degree | the parameter, not the AIR, sets the round degree; our driver used 8: d=8 → 4 saves 2.5 KB at 2^12 rows, ≈ 3.5 KB at 2^17.5 | relations law | — |
| next-row mask (per column, from the symbolic DAG at keygen, in the vk) | child: 116 of 271 rotated columns, relations −7.4 KB; **L3 SHA AIR: 438 of 442 main + 16 of 18 table columns are read at the next row** → −0.3 KB there | relations law (rot_cols) | vk mask dropping a read column (rejected), rotated claim removed / changed |
| two-element query PoW witness | z=32 proven in a real proof (gate 5); **z=28: 3.8 s mean of 8 grinds; z=32: 65.5 s mean of 3** (8 threads; expected 2^z/(4.8–5.6·10⁷/s) = 4.8–5.7 s / 77–90 s); +4 B per round | — | first element changed, element missing |

Relations law (exact on the dummy and child; SHA AIR 48,940 vs 48,956 measured):
`48·Σ_cols(1+rot_c) + 48·((d+1)(2^l_skip−1)+1) + 48·((d+1)·n − g) + 96·airs + 24 (+4 lever format)`,
n = max log2(rows) − l_skip, g = Gruen rounds. Stacking: `352 + 96·n_stack + 48·W` (exact, W=4..28).

**Gate 5 re-measured** (same shape, h=14, W=15; `logs/g6-*.log`): 268-bit/48 B **350,713 B**
(was 361,220; GKR 20,408 → 13,832, relations 50,808 → 47,356); **z=32 / 42 B, really proved
with z=32: 293,903 B** (four grinds 28–276 s, 592 s total under contention; 23 negative cases).
Extrapolated to 2^26.4 cells (W=169, GKR at L=23):

| | 268-bit / 48 B | z=32 / 42 B |
|---|---:|---:|
| WHIR (auth + initial + codeword + final poly + small) | 371,752 | 301,396 |
| relations (d=4, Gruen) | 48,038 | 48,038 |
| GKR (L=23, Gruen + derived) | 29,960 | 29,960 |
| stacking | 10,096 | 10,096 |
| **total (extrapolated)** | **459,923** | **389,561** |
| round 1 | 479,156 | 408,734 |

**Second data point: the real L3 SHA AIR at 2^18 rows** (n=4096 compressions, 2^26.8 cells, 467
columns over 3 AIRs; at b=3, log_h=22 because the final shape needs ≈ 100 GB): 743,353 B total,
**GKR 29,960 = law at L=23 exactly, relations 48,956, stacking 3,616 = law**; 14.8 GB, 323 s.
Its WHIR part is not at the final-layer shape (b=3); the non-WHIR parts are shape-independent and
confirm the laws on a real circuit.

**For the ext2 fixed point.** ext2's "+gruen" rows use 48L² + 264L + 248; measured is
48L² + 192L + 152 (−1.8 KB more at L=24). ext2's relations (2·48·cols + 5,784 + 432·(h−12)) assume
d=8 and no Gruen; with d=4 and Gruen the law gives ≈ −4.3 KB at h≈17.5. **ext2's "next 0.3" rows
are not available for the SHA AIR** (438/442 columns rotated); only a narrower or re-laid-out AIR
gets there. Applying the measured laws to ext2's `L m=3 combo` point (345,176 B, c_sha 19,448):
≈ 345,176 − 15,648 (GKR) − 4,300 (relations) ≈ **325 KB** (model + measured laws, not a proof).

### Other non-WHIR candidates (item 4)

| candidate | estimate | status |
|---|---:|---|
| degree parameter = real AIR degree | −3.5 KB at d 8→4 | done (config) |
| Gruen zerocheck | −48 B × rounds with all traces active (≤ 0.8 KB) | done |
| derive the last AIR's numerator/denominator terms from the GKR claims | −96 B | not done (tiny) |
| strip eq_uni from the univariate skip round | −(2^l_skip−1)·48 = −144 B | not done (tiny) |
| derive one stacking opening from the stacking-sumcheck check | −48 B | not done (tiny) |
| stacking openings 48·W: reuse stacking coefficients as WHIR batching coefficients | up to −8 KB at W=169 | **not sound without a proximity-gap argument for structured coefficients**; larger log_h (×15 domains) shrinks W soundly |
| fewer interactions per SHA-AIR row (GKR depth) | −2.4 KB per halving at L=23 (43 → 11/row: L 23→21, −4.6 KB) | AIR lane |
| narrower final AIR (columns × 2 openings) | −96 B per column removed (230 cols: −22 KB) | AIR lane |
| GKR: 3 claims/layer and 2 values/round are minimal for this protocol | — | — |

### Round-2 spec additions

* **Lever header:** lever-format proofs carry `CODEC_VERSION_LEVERS` then 4 bytes
  `k_first, multiproof, keep_domain, flags` (flags bit 0 gruen_gkr, 1 gkr_derive_claims,
  2 next_mask, 3 gruen_zerocheck, 4 wide_query_pow); the WHIR body no longer repeats them.
* **GKR (Gruen):** layer j, round t: s(X) = eq_pre·eq1(ξ_t, X)·t(X), eq1(ξ,X) = (1−ξ)(1−X) + ξX,
  eq_pre = Π_{u<t} eq1(ξ_u, r_u); the proof (and transcript) carry s(1), s(2) only; the verifier sets
  s(0) = claim − s(1), t(k) = s(k)/(eq_pre·eq1(ξ_t,k)) for k = 0,1,2, claim' = eq_pre·eq1(ξ_t,r)·t(r)
  (quadratic interpolation); any zero divisor rejects.
* **GKR (derived claims):** proof omits root q0_claim and every layer's p_xi_1; the verifier computes
  root p_xi_1 = −p_xi_0·q_xi_1/q_xi_0, q0 = q_xi_0·q_xi_1, layer j ≥ 1
  p_xi_1 = (claim'/eq − λ·q_xi_0·q_xi_1 − p_xi_0·q_xi_1)/q_xi_0, then observes exactly the upstream
  sequence (q0, p0, q0, p1, q1 per layer). Wire: pow witness, u32 layers, per layer p0, q0, [p1], q1,
  [q0_claim], rounds.
* **Gruen zerocheck:** rounds t < g = min over traces of max(n_trace, 0) carry s(1..d) (d values); the
  verifier rebuilds s(d+1) = eq1(d+1)·s'(d+1) from s'(k) = s(k)/eq1(ξ_{l_skip+t}, k), k = 0..d.
  Wire: after n_max and s_deg, u32 g', then rounds (the first g' without their last, zero, value).
* **next_mask:** `StarkVerifyingParams.rot_mask = Some(per part (common, preprocessed, cached),
  per column bool)` (serde-skipped when None, so upstream vks are unchanged); column openings per part
  are `[c_0, (r_0 if rot_0), c_1, ...]`; the stacking reduction includes a rotated claim exactly where
  the mask is set.
* **wide PoW (SHA-384 config):** s' = H(7, [state, w0_le32 ‖ w1_le32]) (105-byte message, one
  compression), accept iff the first z bits of s' are zero; s' becomes the state. Query-phase
  witnesses are 2 field elements per round. The soundness calculator counts it as exactly z bits for
  z > 30 (a single-field-element model caps at log2 p).

## Round 3: padding-free (non-power-of-two) trace heights (`tight_heights`)

**Where SWIRL needs powers of two (v2.0.1).** Trace heights are 2^k: the zerocheck/batch-constraint
sumcheck runs over the hypercube {0,1}^(k−l_skip) × the univariate skip domain D (|D| = 2^l_skip),
the GKR runs over Σ interactions × 2^k leaves, and `TraceVData` only carries `log_height`. Stacking
(`StackedLayout::new`) puts every column as one slice of exactly 2^k rows, aligned to 2^k, sorted by
height (perfect packing), and the stacking reduction's kernel for a slice is a product
`eq_D(Z, r_0) · eq(x, r[1..1+n]) · eq(x_high, b_slice)` that relies on that alignment. So a 1.3·2^k
AIR commits 2^k·... = 2^(k+1) rows today: there is **no padding-free packing in the backend**.

**Options considered.**
* *Circuit-level split* (one AIR as two AIRs of heights 2^k and 2^(k−2)): every extra AIR instance
  re-pays its column openings (`2 × 48 B` per rotated column): NvAir 69 columns → +6.6 KB, the
  171-column SHA AIR → +16 KB per extra piece, plus 2 EF per AIR in the batch proof. At the NV shape
  this eats most or all of the ≈ 10 KB. **Rejected.**
* *Masked tail in one slice* (kernel `· [x < H]`): needs the tail space to be reused by other columns
  at unaligned offsets, which breaks the product kernels. Rejected for the chunk scheme below.
* **Chunked columns (implemented).** Only the commitment changes; the zerocheck and GKR still run
  over 2^k with a *virtual zero tail*.

**Mechanism.** With `WhirLevers.tight_heights`, each common-main trace commits only
`H = last non-zero row + 1`, rounded up to a multiple of 2^l_skip (`tight_height`). Each column is
split into the power-of-two chunks of H's binary decomposition (descending, each ≥ 2^l_skip). Chunk i
holds column rows [o_i, o_i + 2^(l+m_i)), and each o_i is a multiple of its own size. All chunks of
all columns are sorted by size and packed greedily, so every slice stays aligned and packing stays
perfect. The stacking reduction treats each chunk as an ordinary slice of height 2^(l+m_i) at point
r[..1+m_i], scaled by `c_i = eq(bits(o_i/2^l) above m_i, r[1+m_i..1+n_T])`, and shares the column's
λ power. The rotation (next-row) kernel of a chunk is `c_i` times its own cyclic kernel plus one
first-row term `eq_D(ω r_0, 1) · eq_D(Z, 1) · eq(x, 0) · δ_i`, with
`δ_i = eq(bits((o_i/2^l − 1) mod 2^n_T), r[1..1+n_T]) − c_i · Π_{t<m_i} r[1+t]`. That term is needed
because the predecessor of a chunk's first row is the previous chunk's last row (or, for the first
chunk, the column's last virtual row). For a whole column, `(c, δ) = (1, 0)`, so one formula covers
every slice. The prover tracks the correction through round 0 (`eq_D(z,1)` at x = 0), the PLE fold
(`· eq_D(u_0, 1)`) and the MLE rounds (`· (1 − u_t)` while the chunk has variables). `TraceVData`
carries H (encoded only in the lever format; 0 = none), it is observed in the transcript after
`log_height`, and proof shape requires `H = Some(h)` with 2^l_skip | h and 0 < h ≤ 2^log_height for
every lever-mode trace of height ≥ 2^l_skip with common-main columns.

**Soundness.** The opened column is, by definition of the kernels, "the committed rows followed by
zeros up to 2^k". The batch-constraint sumcheck, GKR and column-opening claims are unchanged and still
prove that this full 2^k-row trace satisfies the AIR and the buses. So the statement proved is the
upstream statement for a trace whose padding rows are zero. A dishonest H, or a non-zero tail, can only
make an honest proof fail (completeness), not make a false one pass. H is bound in the transcript and
the vk/version (lever header bit 5). Requirement for circuits: **all-zero rows must satisfy the AIR**
(an `is_real` column gating constraints and bus counts, as the driver's dummy does), otherwise
the prover simply cannot use the lever for that AIR. Note the L3/air2 SHA AIRs pad with non-zero
segments today, so `tight_height` returns their full height (measured: `logs/sha-tight.log`, no saving,
verifies).

**Measured** (`logs/t1,t2,tg-*.log`; gas-failure5 at defaults still `ba042e71…`; 142 upstream tests pass):

| run | rows (real / 2^k) | W | total | initial | stacking | negative tests |
|---|---|---:|---:|---:|---:|---|
| dummy 17 cols, b=2 | 700 / 1,024, pow2 | 2 | 285,993 | 22,080 | 1,600 | |
| same, tight (6 chunks per column) | 700 / 1,024 | 1 | 273,229 | 11,040 | 1,552 | 19 (24 with all round-2 levers) |
| same, tight at full height | 1,024 / 1,024 | — | verifies | | | 16 |
| gate-5 shape + all levers, pow2 | 12,780 / 16,384 | 15 | 353,497 | 8,280 | 2,704 | |
| gate-5 shape + all levers, **tight** | 12,780 / 16,384 | 12 | **350,789** | 6,624 | 2,560 | 24 |

Committed rows drop exactly to H (rounded to 2^l_skip); the byte saving is exactly
`ΔW × (q0 · 2^k1 · 4 + 48)` (initial + stacking openings), plus query-position noise in auth
(gate-5: −1,656 − 144 deterministic, −912 auth noise).

**At the NV final-layer shape.** Their model's "none" heights are exactly what this mechanism
commits: NvAir at 2^17.57 and SHA at 2^17.67 rows instead of 2^18. That takes cells from 2^25.91 to
2^25.55, the stacked width from 121 to 94, and keeps relations and GKR unchanged (zerocheck/GKR still
over 2^18, as the model assumes). The model's −9.7 KB (308,547 → 298,881 B at L) is −8.4 KB of WHIR
(initial ∝ W, plus the fixed point) and −1.3 KB of stacking. Those are exactly the W-proportional laws
measured above. **Expected saving ≈ 9.7 KB at L, ≈ 4.0 KB at T**, provided the NV AIRs accept zero
padding rows. In-circuit cost is small: c_i and δ_i depend only on (AIR, chunk), not on the column, so
the verifier computes them once per chunk; each extra slice costs one more `eq_mle(b)` term and a few
Ext12 multiplies. With ~8 chunks per column that is ≈ 2,000 slices × a few Ext12 ops ≈ 0.3 % of the
circuit. Rounding H to a coarser multiple, e.g. 2^(k−3) (≤ 3 chunks, < 1 % rows wasted), would cut this
further but needs a granularity parameter (not implemented).

**Spec additions.** Lever header flags bit 5 = `tight_heights`. `TraceVData`: after `log_height` (and
cached commitments) the lever format writes `u32 H` (0 = none). Transcript: `observe(H)` right after
`observe(log_height)` (or after the preprocessed commit) for every present AIR with `H` set. Layout:
for each trace in height order, for each column, chunks of H's binary decomposition (descending sizes
2^e, e ≥ l_skip, offsets o accumulated); stable sort of all chunks by size descending; greedy packing
into columns of 2^(l_skip+n_stack) rows. Kernel factors as above (`StackedSlice::chunk_factors`).

## Blockers / next steps

1. **GKR term (≈ 44 KB at L=23)** is the largest item the model missed. Levers to test:
   fewer interactions per row in the SHA AIR (each halving ≈ −3.5 KB), or a shallower /
   batched GKR. Needs the recursion lane's final-circuit interaction count.
2. **Stacking openings (48 B × W)**: larger log_h (×15 domains lift log_h + b ≤ 27)
   reduces W and these bytes together with the initial term.
3. Update `levers_model.py` / `ext.py` constants: GKR(L), stacking(W), relations(h, degree),
   remove E6, transcript ≈ 1.4k compressions at final-layer shape; re-run the L4 fixed point.
4. ~~z ≥ 29 needs a 2-element PoW witness~~ done in round 2 (`wide_query_pow`).
5. Full-size gate 5 (W=169) needs ≈ 100 GB or a streamed commit (per-column LDE into
   incremental per-leaf SHA states, ≈ 3.6 GB for 2^24 states; recompute opened rows).
