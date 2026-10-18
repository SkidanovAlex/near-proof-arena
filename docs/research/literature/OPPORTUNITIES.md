# Literature opportunities — unexploited items, ranked

Status: 2026-10-18, `lane/research-catalog`. Derived from [CATALOG.md](CATALOG.md) (tags in brackets).
Ranked by expected impact on the three goals: **S** = final proof < 300 KB, **L** = real-time proving
on a few H200s, **P** = soundness ≤ 2⁻¹²⁸ against 2⁶⁴ quantum queries from proven bounds (U-1…U-12).
Byte estimates are first-order and come from our own models
(`lane/pq-native-hermetic:docs/logs/pq-final-layer-model-2026-10-17.md`, `extrapolate_nv.py`). None is
measured. The baseline is the narrow-verifier (NV) final layer, modelled at **298.9–308.5 KB** with
×15 domains, coset leaves, 42-B digests, z = 32 and m = 3, conditional on T\* and A-IC. Because the
margin below 300 KB is a few KB, every proven-bound saving below matters.

## Summary table

| rank | id | item | goal | expected effect | confidence |
|---:|---|---|---|---|---|
| 1 | O-1 | Johnson-regime **line-MCA** at agreement √ρ+η instead of BCGM's (1+1/2m)√ρ ([BCHKS25] Thm 4.6, [DKT26] Thm 5.12 + fold corollaries, [Hab25]) | S, P | ≈ 0.22 more bits per query, ≈ 10–15 % fewer WHIR queries; ≈ −15…−25 KB | high (proven, any characteristic) |
| 2 | O-2 | **Beyond-Johnson, proven**: [DKT26] first-order threshold a₁(ρ) < √ρ, Lean-checked in ArkLib, needs char p > max(k−1, B∂), which holds for BabyBear | S | a further ≈ 9 % bits per query (combined ≈ 19–29 % fewer queries than BCGM m=3); ≈ −30…−45 KB in total with O-1, minus OOD/list-size costs | medium (new, Sept 2026; constants at a 2⁻²⁶⁸ target untested) |
| 3 | O-3 | Close the WHIR-theorem and batching-term gaps: read the **Tartu thesis** [Pus26] (claims corrections to WHIR soundness); re-pin [BCGM25] v5; apply [Jo26a] interleaving invariance | P (+S) | closes GAPS S-12 open item; dropping the width factor may let m = 8 pass at ×15 (≈ −4…−8 KB) | high for P; medium for S |
| 4 | O-4 | **Per-round GKR or Logup\* virtual outputs for the SHA-512 AIR** ([Sou25-logupstar], [Thaler13], [Ceno24], [Keccacheck25], [LLZ20-GKRhash]) | S, L | commit ≈ 0.7–2k instead of 7.4k cells per compression; each halving of final-layer cells ≈ −12…−25 KB | medium (design study needed; KRS-style binding care) |
| 5 | O-5 | **zip** proof compression for hash-based SNARGs [zip25] | S | claims ~60 % of original size; impact unknown until read | low (mechanism and QROM status unread) |
| 6 | O-6 | **QROM proofs for the transcript gaps**: frozen-chain lemma for G-1, CMS19-lifting corollary for G-2, [CDHZ25] commutator constants, [MS26] PoW-counting template | P | turns T\* (implemented) into a published-style statement; may tighten the t² constant | medium |
| 7 | O-7 | **GPU reuse for H200**: stark-backend `cuda-backend` (whir/gkr/zerocheck/stacking kernels) [stark-backend], sp1-gpu kernels [SP1-GPU], cuPQC batched SHA-512 [cuPQC], sumcheck small-field optimisations [DDBDT26], native recompilation [OVM21] | L | real-time path; the CUDA backend has no SHA-2 Merkle or Ext12 kernels yet | high (code exists, Apache/MIT) |
| 8 | O-8 | **soundcalc + EF comparison**: add a NEAR Proof config to [soundcalc]; compare against EF M3 and the [zkDTVM] SWIRL root (128-bit classical, 200 KiB) | P (communication) | legible classical numbers; separate QROM layer | high |
| 9 | O-9 | **Soundness hygiene from 2025–26 incidents**: generated-statement FS attacks [Fen26]/[KRS25]; transcript injectivity [P3-CVE26]; null-child aggregation [ZisK-GHSA26]; composite union bound [Ziren26]; LogUp characteristic bound [EH24]; small-field list-size term [FS25] | P | prevents known failure classes; mostly checks | high |
| 10 | O-10 | **Formal reuse**: [simple-rbr-fri] + [BCGM25] for folding rbr; [DKT26] ArkLib certificates; [Mar26-IsaSTARK]; [CertiPlonk]/[Clean] for AIRs | P | shorter route to a Lean-checked WHIR rbr bound | medium |
| 11 | O-11 | **Lattice watch**: [LaBinius26] (< 100 KiB PQ SHA-256 proofs), [Akita26] | S | benchmark to beat on bytes; no QROM proof (NF-9) | low for our contract |
| — | — | Rejected after reading: capacity-regime folding [LXYYZ26]/[GG25] (more bytes/bit at our rate, NF-10), threshold halving [CF26] (worse than Johnson), Ligerito/Blaze/TensorSwitch (prover-oriented, larger proofs) | — | — | — |

## Details

### O-1 — Line-MCA at the Johnson radius instead of BCGM m = 3
* **What.** PROOF.md Lemmas 4.2–4.3 use [BCGM25] Thm 9.2. Its agreement is (1+1/2m)√ρ: a 7/6 factor at
  m = 3. [BCHKS25] Thm 4.6 and [DKT26] Thm 5.12 give line (mutual) correlated agreement at √((k−1)/n)+η
  in every characteristic, with exceptional count O_ρ(n/η³). [DKT26] Cor. 7.5/7.7 (interleaving) and
  Cor. 7.8 (depth-h multilinear fold, cost hE/q) cover WHIR's batching and folding. [Hab25] is an
  independent MCA-to-Johnson source. With |Ext12| ≈ 2³⁷², η ≈ 2⁻¹²…2⁻¹⁵ fits the 2⁻²⁶⁸ per-round
  budget.
* **Effect.** Per-query bits at the BCGM radius vs √ρ: 0.78→1.0 (ρ=¼), 1.28→1.5 (⅛), 1.78→2.0 (1/16),
  2.28→2.5 (1/32). WHIR is 215–223 KB of the NV point, mostly query-driven, so ≈ 10–15 % fewer queries
  is worth ≈ 15–25 KB.
* **Next step.** (1) Check that SWIRL's WHIR fold matches DKT26's equality-polynomial fold model (they
  apply it to a WHIR deployment). (2) Re-run `calc/bound.py` (lane/pq-final-soundness) and
  `native/levers_laws.py` with E from DKT26 App. B and the cross-round terms (eqs. 93–94). (3) If the
  margin holds, replace Lemma 4.3's source and note it in GAPS S-14.

### O-2 — Proven beyond-Johnson agreement (DKT26 first-order threshold)
* **What.** [DKT26] proves list decoding and MCA at agreement a₁(ρ) < √ρ by a first-order hidden-derivative
  argument, for arbitrary evaluation sets (so ×15 cosets qualify), provided char p > max(k−1, B∂) with
  B∂ = O(1/η₁). BabyBear's p ≈ 2³¹ exceeds k−1 for every domain we can use, and B∂ is far below 2³¹.
  Parameter certificates are formally verified in ArkLib, and a checker is public
  (github.com/quangvdao/rs-beyond-johnson). Binary fields are excluded ([DKTZ26] counterexamples).
* **Effect.** −log₂ a₁ = 1.093 / 1.648 / 2.197 / 2.740 bits per query at ρ = ¼, ⅛, 1/16, 1/32
  (Johnson: 1.0 / 1.5 / 2.0 / 2.5). The cost is a list size of O(n/η₁²) instead of O(1/η): probably 2 OOD
  samples per commitment (≈ 48 B each) and re-checked 2(t+u′)Λ′/q terms. They report 4.6–11 % proof-size
  savings at fixed 128-bit classical targets (ZisK, LambdaVM, ProveKit).
* **Next step.** Run their `scripts/check_main_certificates.py` and finite tuner at our (n, k, A), with
  q = p¹² and a 2⁻²⁶⁸ per-round target. Their certificates used q ≈ 2¹⁹²–2²⁵⁴ and a 128-bit target, so
  check that the hidden O_ρ constants survive. Then model the NV final layer. This needs a user decision
  only if it is treated as a contract change: it is a proven bound, so U-2 is satisfied.

### O-3 — Theorem hygiene: Tartu WHIR corrections, BCGM v5, interleaving invariance
* **Tartu thesis.** Puškin (Univ. of Tartu, Feb 2026, supervisor Lipmaa) re-proves WHIR rbr soundness and
  "corrects technical inaccuracies present in the original presentation". GAPS S-12 says these were
  never located. The record is <https://hdl.handle.net/10062/119861>; the repository refused automated
  downloads. **Next step:** fetch the PDF manually and diff its rbr bounds against PROOF.md Lemmas 4.3–4.7.
* **BCGM revisions.** ePrint 2025/2051 has five revisions (last 2026-05-19, "major revision"). **Next
  step:** re-verify Def. 9.1 / Thm 9.2 numbering and constants against v5.
* **Interleaving.** [Jo26a] shows affine-line MCA is exactly invariant under interleaving (seed set ≤ q).
  The ×15 caveat (m = 8 misses 2⁻²⁶⁸ by 2.4–7.5 bits at W ≈ 530–600) comes from the batching term with
  the column count W. **Next step:** check whether Jo26a (or DKT26 Cor. 7.5/7.7) removes the W factor;
  if so, m = 8 returns (≈ −4…−8 KB) and the batching margin grows.

### O-4 — Stop committing SHA intermediates
* **What.** Our AIR2 (7,353 main cells per compression) is already at the level of the best SHA-256 AIRs
  (ZisK ≈ 7.3k, Stwo ≈ 7.8k, Plonky3 ≈ 7.7k) for 2.5× the work, and 2.6× below OpenVM's SHA-512 AIR
  (18,963). Further gains must come from not committing values:
  * (a) [Sou25-logupstar]: commit only digit indices; the Σ/σ/Ch/Maj outputs become virtual T[I]
    polynomials opened by one extra sumcheck.
  * (b) Per-round data-parallel GKR ([Thaler13], [Ceno24], [Keccacheck25]): commit only round-boundary
    words (new a, e and W per round, ≈ 0.7k cells plus carries) and prove the round function as a
    shallow layered circuit batched over 80·N rounds (≈ 40 KB of GKR proof, independent of N).
    L4-C killed GKR over all 80 rounds; the per-round variant with committed boundaries is untested.
* **Caution.** A circuit that computes the FS hash in-circuit is the [KRS25]/[Fen26] setting. The GKR
  circuit must be fixed and bound into the transcript before the first challenge (already true for the
  NV vk under PROOF.md §6.5).
* **Next step.** A paper estimate in `l4-study/models-C/ext2.py`: count AIR2 columns that are pure
  functions of other digits (candidates for (a)); model (b)'s cells, interactions and GKR bytes against
  the NV fixed point. Also compare spread-table encodings [Halo2-t16] with base-8 digits.

### O-5 — zip compression
* [zip25] (Fenzi–Zhang) claims non-recursive, black-box compression of hash-based SNARG proofs to
  ≈ 60 % of size, from standard assumptions. If it composes with Merkle-path-dominated WHIR proofs and
  holds in the QROM at 2⁶⁴ queries, it is worth more than O-1 and O-2 together. **Next step:** read the
  PDF (ePrint blocked automated fetches) and record its mechanism, its assumption, and its QROM status.

### O-6 — Proofs for G-1 / G-2 in the literature's terms
* No published QROM theorem covers multi-call challenges (G-1) or grinding (G-2). This is confirmed by the
  QROM search and by `research/novelty/PRIOR-ART.md` §1–2. T\* is already implemented
  (lane/pq-recursion-sha384 @ 46b7e62e2). Three routes would make the proof reviewable or tighter:
  * G-1, existing chain: split H into H₀ (tags ≠ 5) and H₅. Freeze H₅ (the bounds are
    information-theoretic), treat the chain as post-processing Φ_{H₅}(H₀(x)) of a single oracle output,
    and show by Chernoff that the bad-set density stays ≈ ε_rbr. Fallback: CFHL21 transition capacity.
  * G-2: PoW and query seed computed on the same input (or the same call) make one wide-output RO, so
    the CMS19 lifting lemma gives O(t²·2⁻ᶻ·ε). [MS26] is the compressed-oracle PoW-counting template.
    [HKKTW26] gives clean classical constants.
  * Constants: compare CMS19 with [CDHZ25] (EUROCRYPT 2026), whose commutator bound and modular
    extended-BCS analysis may improve the t³/2ⁿ term and give adaptive extraction.
* **Next step.** Write the 2-page frozen-H₅ lemma and the G-2 corollary as a PROOF.md appendix. Ask the
  final-soundness lane to cross-check against CDHZ Thm 11.3.

### O-7 — GPU code to reuse on H200
* `openvm-org/stark-backend` v2.0.x `crates/cuda-backend` (Apache/MIT) has whir.cu, merkle_tree.cu,
  logup_zerocheck/gkr.cu, zerocheck_round0.cu and stacked_reduction.cu. It is the same protocol as our
  pinned backend, but has no SHA-2 Merkle kernel or Ext12 arithmetic.
* sp1-gpu (`logup_gkr`, `zerocheck`, `merkle_tree`, `challenger`) is a second reference. ZisK
  pil2-proofman has open BLAKE GPU kernels as structural references.
* NVIDIA cuPQC v0.6 does batched SHA-512 and Merkle trees (no SHA-384 mode, but SHA-384 is the SHA-512
  compression with another IV). Useful for grinding (z = 32 at ≈ 65 s per round on 8 CPU threads today)
  and leaf hashing; the license must be checked first.
* Prover algorithms: [DDBDT26] small-value sumcheck rounds in the base field (2–3×); [MoHW26] shows
  sumcheck beats NTT for high-degree constraints (our degree-21 SHA AIR); OpenVM 2.1 native
  recompilation [OVM21] halved GPU count for execution and trace generation.
* Latency bars: OpenVM 2.1 at 9.7 s P99 on 4×5090; ZisK at 9.62 s on 4×5090; Airbender Prime, 99 % of
  blocks under 10 s on one RTX PRO 6000 (all classical-security, ≤ 128-bit, Ethereum blocks).
* **Next step.** Port the stark-backend CUDA path to SHA-384/Ext12: SHA-512-compression Merkle/leaf
  kernel, Ext12 field ops, and the levers (×15 LDE, coset leaves, two-element PoW). Benchmark on one
  H200 against the CPU numbers in `results/pq-recursion-nv/`.

### O-8 — soundcalc and the EF real-time targets
EF's published targets are the closest external analogue of our contract:

| item | EF ([EF-RTP25], [EF-SEC25], [EF-SPRINT26]) | ours | comparison |
|---|---|---|---|
| latency | P99 ≤ 10 s on mainnet blocks (not 12 s); worst-case blocks treated as DoS vectors [EF-BENCH25] | real-time, chunks up to 1 Pgas | define P99 **and** worst-case chunk latency |
| proof size | ≤ 300 KiB = 307,200 B (M3, Dec 2026); ≤ 600 KiB at M2 | < 300,000 B | ours 2.3 % stricter |
| security | ≥ 128-bit "provable" per soundcalc: classical rbr, UDR or Johnson (JBR); capacity regime removed | ≤ 2⁻¹²⁸ vs 2⁶⁴ **quantum** queries, proven only | ours strictly stronger; EF has no PQ requirement; EF's leanVM claims 64-bit QROM |
| conjectures | none (JBR counts as proven) | none | same; our m = 3 list regime is JBR |
| setup | no trusted setup, including wrappers | hash-only | same |
| recursion | formal recursion-soundness argument (W3, Dec 1 2026) | A-IC(τ) under U-11/U-12 | comparable; we state the assumption explicitly |
| hardware | ≤ $100k CAPEX, ≤ 10 kW | a few H200 machines | ours exceeds the EF envelope; NEAR gas ≠ Ethereum gas |

Already at ≤ 300 KiB and 128-bit classical provable: [zkDTVM] (SWIRL+WHIR root with a SHA-256 Merkle
root, 200 KiB, JBR m = 2, queries [77, 38, 26], 20-bit grinding, 326 columns); ZisK/Venus (269 KiB
expected, 313 KiB worst case). None is assessed for quantum security.
**Next step.** Add a `nearproof` TOML to soundcalc (templates: `openvm2`, `zkdtvm_v080`) with Ext12,
42-B digests and z = 32 to get EF-legible classical numbers, and publish the QROM layer (PROOF.md)
separately. soundcalc defers quantum compilation and cites [CDHZ25].

### O-9 — Hygiene checks prompted by 2025–26 incidents
* **Generated statements.** [Fen26] extends [KRS25] to program-generated instances. Chunk validation runs
  user contracts, which is that setting. Mitigation: bind the full statement (vk, chunk header, state
  roots, all public inputs) and all witness commitments before the first challenge. PROOF.md §6.5 found
  no missing absorption; record Fen26 as the citation.
* **Transcript injectivity.** [P3-CVE26] (distinct transcripts, identical challenges). Our GAPS G-9 is a
  known non-injective preamble case (malleability only); fix it.
* **Aggregation.** [ZisK-GHSA26]: null children disabled the aggregate checks. Cross-shard aggregation
  must use canonical, transcript-bound padding children. [Ziren26]: add an explicit union-bound term
  for the number of composed proofs (PROOF.md already unions over 7 layers; shards add more).
* **LogUp characteristic bound.** Multiplicity sums must stay below p ≈ 2³¹ unless [EH24] is used. Check
  that the backend enforces it on summed heights × interactions, in both the NV circuit and the Lean
  statement.
* **Small-field list size.** [FS25]: for extension codes over BabyBear, list sizes follow the base field.
  Check that no Λ/|F| term uses extension-field heuristics. Proven Johnson and DKT26 list bounds are
  unaffected.
* **Citations.** Cite [CDDGS25] by ePrint 2025/947; arXiv 2411.05360 v2 was withdrawn. Update WB and LQP.

### O-10 — Formal reuse
* [simple-rbr-fri] (Lean 4, FRI rbr after [GMW25]) takes MCA as an axiom that [BCGM25] or [DKT26]
  would discharge. It is the nearest template for a Lean WHIR rbr proof.
* The [DKT26] ArkLib certificates give Lean-checked parameter certificates directly.
* [Mar26-IsaSTARK] is the closest end-to-end mechanised STARK soundness proof (classical ROM only).
* No QROM mechanisation exists anywhere, so the QROM step stays a paper proof; state that split
  explicitly.
* [CertiPlonk] (Plonky3 symbolic AIR extraction, already applied to OpenVM) and [Clean] are candidate
  routes for extracting our AIRs to Lean.

### O-11 — Lattice watch
[LaBinius26] (Osadnik–Seiler, Sept 2026) proves SHA-256/Keccak/BLAKE3 in < 100 KiB, and [Akita26]
reaches 58–68 KB openings. Neither has a QROM proof (consistent with NF-9), and binary-field
beyond-Johnson counterexamples [DKTZ26] constrain LaBinius parameters. Keep them as the byte benchmark,
not as a route under U-2.

## Findings that bear on what we rely on

1. **Beyond-Johnson is no longer conjecture-only.** The 2026-10-17 model log (iterations 6–7) treats
   "beyond Johnson" as capacity-regime research not usable under U-2. [DKT26] proves a beyond-Johnson
   threshold in large characteristic, BabyBear included. This is an upside (O-2), not a soundness
   problem. `examples/stark-plonky3/README.md` cites DKT26 only as "line-MCA".
2. **WHIR soundness corrections exist and are unread.** [Pus26] claims corrections to WHIR's
   presentation; GAPS S-12 rates Thm 5.2 as proven. Until the thesis is diffed (O-3), S-12 carries an
   unknown.
3. **No contradiction found** for BCIKS20's Johnson regime, BCGM Thm 9.2, WHIR's proven regime, non-power-
   of-two (15·2ᴺ) domains, LogUp-GKR or Gruen. Every 2025–26 counterexample (CS25, DG25, KKH26, Kam26,
   DKTZ26, FS25) targets the capacity regime, beyond-Johnson in characteristic 2, or conjectured
   parameters.
4. **EF numbers.** Real-time means P99 ≤ 10 s (not 12 s); the size cap is 300 KiB (307,200 B). "Provable"
   in EF's sense is classical; no external system has a numeric quantum bound.
5. **Withdrawn citation.** arXiv 2411.05360 (CDDGS) v2 was withdrawn; use ePrint 2025/947.
