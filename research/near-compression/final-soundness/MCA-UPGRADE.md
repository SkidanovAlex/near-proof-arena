# MCA upgrade for the PQ final layer (O-1, O-2, O-3)

Lane `lane/pq-mca-upgrade` (from `lane/pq-final-soundness` @ f8c168f98), 2026-10-18. Research
only; no backend change is made here.

Companion files in `calc/`:
* `bound_mca.py` and its output `bound_mca.out`: the per-round bound with the best proven input
  for every WHIR round.
* `dkt_certs.py` and `dkt_certs.json`: 36 first-order certificates plus a 51-code grid, produced
  and re-checked with the DKT26 authors' engine.
* `size_mca.py` and `size_mca.out`: final-layer bytes through `extrapolate_nv.py`,
  `extrapolate_nv2.py` and `ext2.py`.

`GAPS.md` rows S-12 and S-14 are updated; S-26 and S-27 are new.

## 0. Bottom line

| result | what it gives us | verdict under U-2 |
|---|---|---|
| **DKT26 Thm 5.12** (Johnson line MCA) + Cor 7.7/7.8 (interleaving, folds) | Line MCA at √ρ + η. The error is **linear in n** and **42 bits** smaller than BCGM even at BCGM's own radius, so m = 64 costs nothing. Worst non-query move 2⁻²⁸⁹·⁷. | **Usable now** as a Lean-checked [P′] bound: the theorem statements are checked in ArkLib @ a5aa267. Before PROOF.md cites it as [P], two checks: build ArkLib at the pin with `#print axioms`, and an independent read of Thm 5.12 and Cor 7.7 (preprint, not refereed). |
| **DKT26 first order** (Thm 5.8, Prop 5.10, Lemmas 5.9/5.11, Cor 7.3/7.5/7.7) | Agreement **below √ρ**: a_i/√ρ_i = 0.77–0.90 is certified. List ≤ 2⁴³·⁴, MCA error ≤ 2⁻²⁸⁰·⁷. BabyBear qualifies: p = 2³⁰·⁹ > max(k−1, B∂). | **Usable after review.** The theorems are Lean-checked, but our 36 integer certificates are checked only by the authors' exact-arithmetic Python. Very new; AI-assisted discovery and formalisation (their §1.1). |
| **BCHKS25 Thm 4.6** (powers MCA up to Johnson) | Same regime as DKT for powers batching, error O(n/η⁵). | Usable after review: preprint, and the §4 proof is a sketch. **Not needed**: a first-order powers-curve certificate covers batching. |
| **Hab25 Thm 2** | Lines only, at BCGM's radius with BCGM's constant. | Not applicable: no gain, superseded. |
| **BCGM v5** | Def 9.1 / Thm 9.2 unchanged. Our local copy is v5. CCC 2026 states it only as an informal "Theorem 5". | Current basis; unchanged. |
| **Jo26a** (interleaving invariance) | Correct and domain-agnostic, already used inside DKT Cor 7.7. It does **not** remove the W in err⋆_{W−1}: that W is the powers degree, not an interleaving width. | Not applicable to the m = 8 question. That question is moot anyway, since O-1 replaces m = 3 by m = 64. |
| **Pus26** (Tartu thesis; full text obtained) | Corrected WHIR Thm 5.3: **no term is larger** than ACFY Thm 5.2. Adds explicit hypotheses, all met here. | Closes GAPS S-12; nothing we rely on changes. Its "smaller" Thm 5.7 combination error is not adopted. |

**Queries** (backend schedule logic, 236 query bits + z = 32):

| layer | today, BCGM m = 3 | O-1 (Johnson, m = 64) | O-1 + O-2 (first order) |
|---|---|---|---|
| final (b8, k1 1, k3) | 42 / 38 / 31 / 26 = 137 | 40 / 37 / 30 / 25 = 132 | **38 / 35 / 29 / 24 = 126** |
| bits per query | 5.731 / 6.231 / 7.731 / 9.231 | 5.942 / 6.442 / 7.942 / 9.442 | 6.214 / 6.743 / 8.140 / 9.834 |
| inner NV (b6, k4) | 50 / 46 / 33 / 26 = 155 | 48 / 44 / 32 / 25 = 149 | 45 / 41 / 31 / 24 = 141 |
| bits per query | 4.731 / 5.231 / 7.231 / 9.231 | 4.942 / 5.442 / 7.442 / 9.442 | 5.245 / 5.759 / 7.614 / 9.835 |
| ε_rbr (worst move) | 2⁻²⁶⁸·⁵⁵ | 2⁻²⁶⁸·⁰⁶ | 2⁻²⁶⁸·⁰¹ |
| end to end (Thm 6.4/7.4) | 2⁻¹³⁵·²³ (union 2⁻¹³²·⁴²) | 2⁻¹³⁴·⁷³ (2⁻¹³¹·⁹³) | 2⁻¹³⁴·⁶⁹ (2⁻¹³¹·⁸⁹) |

**Bytes** (final layer; inner and final layers re-tuned together; `size_mca.out`). The target is
300,000 B.

| model | final target | today | O-1 alone | O-2 on top of O-1 | O-1 + O-2 |
|---|---|---:|---:|---:|---:|
| `extrapolate_nv` (the ~299 KB headline) | 226 bits (model default) | 298,881 | 292,458 (−6.4 KB) | −6.0 KB | 286,458 (−12.4 KB) |
| `extrapolate_nv` | **236 bits (= PROOF.md)** | **305,906** | **297,807 (−8.1 KB)** | −4.1 KB | **293,698 (−12.2 KB)** |
| `extrapolate_nv2` (phase-2 laws) | 236 | 323,955 | 313,759 (−10.2 KB) | −13.0 KB | 300,733 (−23.2 KB) |
| `extrapolate_nv2` | 226 | 313,359 | 304,767 (−8.6 KB) | −10.3 KB | 294,491 (−18.9 KB) |
| `ext2` (gate-5 laws, c_sha 7,524) | 236 | 279,720 | 271,659 (−8.1 KB) | −8.0 KB | 263,648 (−16.1 KB) |

"O-2 alone" is not a separate configuration. The first-order agreement lies below √ρ, so it
already contains O-1's (1+1/2m) gain. The "O-2 on top of O-1" column is the marginal value.

**Two findings change the headline:**

1. **The ~299 KB headline uses a 226-bit final-layer query target.** That is a 258-bit
   per-round target: `score_designs.settings('L')`, inherited from the October lever model.
   PROOF.md proves U-6 only with a 268-bit target in *every* layer: a 2⁻²⁵⁸ round gives
   2⁻¹²⁴·⁷ end to end. At 236 bits the same model is **305,906 B, over the target today**.
   O-1 alone brings it to 297,807 B (2.2 KB margin) and O-1 + O-2 to 293,698 B (6.3 KB margin).
2. **The savings are 2–3× smaller than OPPORTUNITIES.md estimated** (−15…−25 KB for O-1,
   −30…−45 KB combined). The catalogue scaled from rates ¼…1/32, where a query is worth 1–2.5
   bits. Our ×15 rates are 2⁻⁹·⁹…2⁻¹⁸·⁹, where a query is worth 4.7–9.8 bits. The same +0.22
   (O-1) and +0.3…0.4 (O-2) bits per query are therefore only 2–4 % and 5–8 % fewer queries.

## 1. The results, read in full text

Sources:
* DKT26: the authors' repo PDF (identical to ePrint 2026/2056 v1, 16 Sep 2026, 145 pp.).
* BCHKS25: the Toronto PDF and ECCC TR25-169.
* Hab25 and Jo26a: ePrint PDFs via archive.org mirrors.
* BCGM: v5 PDF, the Feb 2026 version and the CCC paper.
* Pus26: the DSpace bitstream via a Wayback snapshot.

Notation: n = |L|, k = dimension, D = k − 1, ρ = k/n, ρ₋ = D/n, A = the integer agreement
threshold, a = A/n = 1 − δ, q = |F| = p¹².

### 1.1 DKT26: Dao, Kominers, Thaler, ePrint 2026/2056

Status: one version, received 2026-09-16, labelled "Preprint". It is **not peer reviewed**. The
authors state that GPT-5.6 Sol, GPT-6 Astra and Claude Fable 5.1 "discovered and refined the
main results" and wrote the Lean formalisation (§1.1, "AI assistance").

**Thm 5.12, quantitative Johnson MCA, every characteristic** (p. 53).
* Hypotheses: any field, any n distinct points, 1 ≤ D ≤ n − 2, a = √ρ₋ + η₀ ≤ 1. No condition on
  the characteristic, extension degree or domain structure.
* Parameters: A = ⌈an⌉, m = max(⌈√ρ₋/(2η₀)⌉, 3), t = m + ½, B_jet = ⌈t/√ρ₋⌉ − 1,
  B_Z = ⌈t²/(3ρ₋)⌉ − 1.
* List: |L| ≤ min(B_jet, ⌊n(A−D)/(A² − nD)⌋).
* Full agreement-set line MCA: |E| ≤ B_cf := E_ord(D, A, n; B_jet, B_Z) < 8nt³/(3ρ₋). The
  error is |E|/q.
* The conclusion is exactly WHIR Def 4.9 / BCGM Def 3.14 MCA: the candidate's agreement set
  equals the common agreement set of the witnesses.
* Lean: `johnson_lineMCA_probability` bounds `mcaError (AffineLineGenerator F)` by
  johnsonE0/|F|.
* At our parameters: E/q = 2⁻³⁰²…2⁻³¹⁴ at m_DKT ≤ 64, and still 2⁻²⁸⁶ at m = 3000. BCGM at
  m = 3 is 2⁻²⁶⁹·⁶…2⁻²⁸⁰. bound_mca.py uses the larger of the two printed E_ord forms (Lemma 5.3
  and the Thm 5.8 display). I checked (68) numerically against E_ord at n = 2¹⁶, 2²⁰ for
  ρ ∈ {½ … 1/256}: it holds.

**First order: Thm 5.7/5.8, Prop 5.10, Lemma 5.9 (successive stages), Lemma 5.11 (finite list).**
* Hypotheses: a > a₁(ρ) (eq. 31; a₁/√ρ → 1/√2 as ρ → 0), characteristic 0 or
  p > max(k − 1, B∂), any n distinct points. A support certificate (m, B∂, B_jet) must satisfy
  N_coef > n·R_loc and give a challenge height B_Z (63/64).
* Then:
  * Λ ≤ L of Lemma 5.11;
  * line exceptional count ≤ max_d min_L E_d(L) of (59);
  * the curve version for powers of degree ℓ is Cor 7.3 / Lemma 5.9, linear in ℓ;
  * width independence for interleaved codes is Cor 7.5 (lists) and Cor 7.7 (MCA);
  * an h-level fold costs h·E/q (Cor 7.8).
* Lean statements: `firstOrderBranch_finiteLength_*`, `exists_exceptional_retainedSquarefreeCurveMCA_sharp_*`,
  `uniformExactInterleavedPowerAgreement_of_scalar_arbitrary`, `tensorFoldBad_card_le`,
  `fullSetLevelWitness_interleaved_of_exactAgreement`.
* BabyBear: char(Ext12) = p = 15·2²⁷ + 1 > 2²¹ ≥ k for every code here, and every certificate
  has B∂ ≤ 192, so the hypothesis holds.

**Applicability to WHIR.**
* Domains: any set of distinct points, so ×15 cosets and their 2^s-power images qualify.
* Fold sub-rounds: WHIR's fold sub-round is a line over the 2-interleaved code C^(i,s), so Cor 7.7
  applies; DKT §8.2 applies it to a deployed WHIR (ProveKit).
* OOD, shift queries and γ: DKT does not bound these. They come from WHIR Thm 5.2 (= Pus26 Thm 5.3)
  with DKT's list sizes as inputs.
* μ batching of the W stacked columns is a degree-(W−1) powers curve, covered by Cor 7.3.

**Certificates at our parameters** (`dkt_certs.py`: the authors' `tune_first_order_mca.py` @
60b7257, derivative-weighted support, tight Taylor model as in their application checkers):
* q = p¹² = 2³⁷⁰·⁸⁸, n ≤ 15·2²⁷ (the models' largest final-layer domain; bound.py's base stress
  shape also reaches it).
* Every code each planned round needs is certified: C^(i,s) for s = 0…k_i, plus the
  powers-curve batching at ℓ = W − 1 = 140. That is 36 certificates.
* Ranges: E/q from 2⁻²⁸⁰·⁷ to 2⁻³⁰⁴·⁹; lists from 2³¹·⁹ to 2⁴³·⁴; m = 4…26; B∂ ≤ 52.
* The legacy Taylor model gives the same worst values.
* A grid at the size-model rule a = (a₁(ρ)/√ρ + 0.05)·√ρ certifies all 51 codes
  (k = 2⁸…2²⁴ and two fold levels each): E/q ≤ 2⁻²⁸¹, list ≤ 2⁴³·⁶.
* **So "beyond Johnson" is usable at a 2⁻²³⁶ (2⁻²⁶⁸ with z) per-round target.** The 370-bit field
  absorbs the O(n²/η⁴) constant with more than 10 bits to spare.
* Only a < a₁ is out of reach. Hence 38/35/29/24 is the floor for the final layer: the next
  query count down would need a < a₁(ρ) in every round. The one exception is inner round 2, where
  a = 0.750√ρ (q = 30) found no certificate in the search box.

### 1.2 BCHKS25: ePrint 2025/2055, ECCC TR25-169

Preprint (Nov 2025); no venue found.
* **Thm 1.5** (CA, lines): a > (2(m+½)⁵ + 3(m+½)γρ)/(3ρ^{3/2})·n + (m+½)/√ρ, with
  m = max(⌈√ρ/(2η)⌉, 3).
* **Thm 4.6** (list/mutual CA for u₀ + z u₁ + … + z^M u_M): |E| ≤ M·(same), but with
  m = max(⌈√ρ/η⌉, 3), twice Thm 1.5's m. bound_mca.py uses the stated (larger) m.
* Hypotheses: any field, any D ⊆ F_q, deg ≤ k convention.
* The proof of Thm 4.6 is a one-paragraph sketch.
* Negative results (Thm 1.6, 1.9, 1.13) are at or beyond the list-decoding radius or near
  capacity; they do not touch a ≥ √ρ.
* At m_B = 128 (backend m = 64): W = 141 batching 2⁻²⁸⁰·⁵, W = 601 2⁻²⁸¹·⁴. At m = 1024 it fails
  (2⁻²⁶⁰·⁶), so BCHKS caps m around 250.

### 1.3 Hab25: ePrint 2025/2110

Preprint, outline proof, lines only. Thm 2 gives |E| ≤ ((m+½)/√ρ)⁷(ρn)²/3 at γ = 1 − (1+1/2m)√ρ:
BCGM's constant again. It is superseded by BCHKS Thm 4.6 and DKT Thm 5.12. No use for us.

### 1.4 BCGM: ePrint 2025/2051 v5 (19 May 2026), CCC 2026 (LIPIcs.CCC.2026.24)

* The local copy is byte-identical to v5.
* Def 9.1 / Thm 9.2 / Lemma 9.3 are unchanged from the Feb 2026 version (word diff: typos).
* err = (m+½)⁷/(3ρ^{3/2})·d·n²/|F| for γ ≤ 1 − (1+1/2m)√ρ, integer m ≥ 3, any D ⊆ F, any
  characteristic, |F| > (m+½)²n.
* The CCC paper has only "Theorem 5 (informal)" and defers to the ePrint. So cite ePrint v5
  Def 9.1 / Thm 9.2. **Nothing we rely on changed.**
* BCGM has no RS bound parameterised by η beyond the m knob. Its Thm 8.2 is for general codes and
  reaches only ≈ 1.5-Johnson.

### 1.5 Jo26a: ePrint 2026/891 (v1 May 2026; Aug revision non-technical)

* Thm 4.2/4.4: ε_G(C^{≡s}) = ε_G(C) when |Ω| ≤ q, for lines and powers (Cor 4.5).
* Cor 4.8/4.9: BCGM's bounds carry over to interleaved codes with no s factor.
* It removes interleaving-width union bounds only. The W − 1 in our batching term is the powers
  *degree*, so Jo26a cannot remove it.
* DKT Cor 7.7 already uses Jo's projection argument.

### 1.6 Pus26: Puškin, MSc thesis, Univ. Tartu, Feb 2026 (98 pp.; full text obtained)

Corrections to ACFY:
* Claim 4.15: typos.
* Lemma 4.10: min/max swap in B⋆.
* Lemma 4.21: MCA needed only for the folded code C′ = RS[L^(2), m−1], plus B⋆(C′,2) ≥ ρ.
* Thm 4.20: adds min_i B⋆(C^(i),2) ≥ ρ.
* Query/indexing bookkeeping.
* Thm 5.6 → 5.7: a claimed smaller combination error (t−1)/|F| with no ℓ. Its state function is
  exact membership, and the combined code's proximity step normally costs a list union. **Not
  adopted.**

Its WHIR theorem (Thm 5.3, pp. 70–71):
* ε^fold_{i,s} ≤ d·ℓ_{i,s−1}/|F| + err⋆(C^(i,s),2,δ_i);
* ε^out_i ≤ 2^{m_i}ℓ²/(2|F|) (s OOD samples: (2^m/|F|)^s);
* ε^shift_i ≤ (1−δ)^t + ℓ(t+1)/|F|;
* ε^fin ≤ (1−δ)^t.

**No term is larger than in ACFY Thm 5.2.** The new hypotheses are:
* char ≠ 2;
* list-decodability of every C^(i,s), s = 0…k_i;
* B⋆ ≥ ρ, printed as "≥ δ_i", a typo per its own proof.

All hold for us: a₁(ρ) > ρ. bound_mca.py certifies lists for all s = 0…k_i, including the fully
folded code that bound.py did not list separately.

## 2. The upgraded per-round bound (`calc/bound_mca.py`)

For each round, bound_mca.py takes the best bound that applies, with the same moves as bound.py:
* q_i = ⌈236 / −log₂ a_i⌉.
* Fold move s of round i is charged max_s E(C^(i,s))/|F| + 3ℓ_i/|F|.
* OOD: ℓ²/2·(2^{m}/|F|)^{u}, with u = 1 sufficient everywhere (worst 2⁻²⁷¹·⁹).
* γ: ℓ_{i+1}(t_i + u)/|F|.
* PIOP: the ℓ₀ terms (worst LogUp 2⁻²⁷⁹·² with ℓ₀ = 2⁴⁰).
* μ batching: the first-order curve certificate at ℓ = W − 1. Final layer 2⁻²⁸²·¹ (O-2) / 2⁻²⁸⁹·⁷
  (O-1); inner layer 2⁻²⁸³·⁰ / 2⁻²⁹³·⁶; base stress (W = 601) 2⁻²⁸⁷·⁵.

Agreement ratios a_i/√ρ_i for O-1 + O-2:

| layer | ratios | lists ≤ |
|---|---|---|
| final | 0.835, 0.818, 0.879, 0.768 (a₁/√ρ = 0.750, 0.743, 0.729, 0.720) | 2⁴⁰·⁰, 2⁴¹·⁰, 2³⁸·⁶, 2⁴³·⁴ |
| inner | 0.817, 0.809, 0.895, 0.768 | 2³⁹·⁶, 2³⁹·⁸, 2³⁵·⁹, 2⁴¹·⁴ |

* Each ratio is the largest that reaches that query count.
* The base layer stays at O-1 (two commitments square ℓ₀ in the PIOP terms).
* The worst move of every layer is a query move at ≈ 2⁻²⁶⁸·⁰ (O-1 r3: 236.06 + 32).

## 3. Backend change (one formula, shared by prover, native verifier and NV circuit)

* **O-1:** `WhirProximityStrategy::ListDecoding { m: 64 }` instead of `{ m: 3 }`, for every PQ
  layer. `ProximityRegime::max_agreement_f64` already returns √ρ(1 + 1/2m), so
  q_i = ⌈(security_bits − query_phase_pow_bits)/(−log₂(√ρ_i(1+1/128)))⌉ follows from the existing
  code (U config.rs:332-346, 405-457). No code change, but:
  * the vk / pre-hash constants change;
  * the NV circuit's per-round query constants follow;
  * the BCHKS-based `soundness/calculator.rs` is unaffected (not the proof).
* **O-2:** a new strategy variant carrying explicit per-round agreements,
  `Certified { agreement: Vec<(A_i, n_i)> }`, with q_i = ⌈236 / −log₂(A_i/n_i)⌉ and A_i from
  `dkt_certs.json` (final: A = 27,128,239 / 18,792,001 / 7,139,336 / 2,205,154 at
  n = 2,013,265,920). The table must be bound into the vk pre-hash (cf. G-10).
* Proof bytes: for 1 OOD sample per round, no new bytes.
* Size model: `bits()` becomes rate/2 − log₂ c(ρ), with c = 1 + 1/128 (O-1), or
  a₁(ρ)/√ρ + 0.05 (O-2 rule, plus a 48 B/round OOD reserve).

## 4. Exact PROOF.md edits (to apply when O-1 / O-2 is adopted)

1. **§1.1, bullets 2–3.** Replace "q_i = ⌈236/(−log₂ α_i)⌉ with α_i = √ρ_i·(1 + 1/(2m))
   (config.rs:332-346, 405-457). m = 3 (ListDecoding)." with:

   > q_i = ⌈236/(−log₂ a_i)⌉, where a_i = A_i/n_i is the agreement at which round i is analysed:
   > a_i = √ρ_i(1 + 1/128) (ListDecoding m = 64; O-1) or the certified first-order A_i of
   > calc/dkt_certs.json (O-2). Queries: final [40, 37, 30, 25] (O-1) / [38, 35, 29, 24] (O-2);
   > inner [48, 44, 32, 25] / [45, 41, 31, 24].

2. **§4, preamble.** Replace "δ_i = J_m(ρ_i), ℓ_i = m/ρ_i" with:

   > δ_i = 1 − a_i; C^(i,s) = RS[L_i^(2^s), m_i − s], s = 0..k_i; ℓ_i = max_s of the list bound
   > of C^(i,s) at agreement ⌈a_i|L_i^(2^s)|⌉. That is DKT26 Thm 5.12 eq. (67) (O-1) or
   > Lemma 5.11 with Cor 7.5 (O-2), valid at every interleaving width.

3. **Lemma 4.1, paragraph 3.** Replace "BCGM Thm 9.2 and the Johnson bound hold for arbitrary
   evaluation sets." with:

   > DKT26 Thm 5.12 and Thm 5.8/Prop 5.10 hold for any n distinct points. The first-order ones
   > need char > max(k−1, B∂): p = 2³⁰·⁹ > 2²¹ ≥ k, B∂ ≤ 192.

   Add Pus26's hypotheses (list decodability of every C^(i,s); MCA radius B⋆ ≥ ρ; char ≠ 2).

4. **Lemma 4.2.** Replace the BCGM batching bound with:

   > ε_μ ≤ E_{W−1}/|F| + ℓ₀(W−1)/|F|, where E_{W−1} is the full agreement-set exceptional count
   > of the powers curve of degree W−1 at agreement a₀. It is given by DKT26 Lemma 5.9 /
   > Cor 7.3, with the support certificate in dkt_certs.json, and is valid at any a₀ > a₁(ρ₀),
   > hence also for O-1. [P′ DKT26; Lean `exists_exceptional_retainedSquarefreeCurveMCA_sharp_at`]

5. **Lemma 4.3.** Replace with:

   > ε_fold(i,s) ≤ max_{s′} E(C^(i,s′))/|F| + 3ℓ_i/|F|. E is B_cf of DKT26 Thm 5.12 (O-1) or the
   > certified (59) bound (O-2). It is transferred to the 2-interleaved fold word by Cor 7.7
   > with no width factor. [P′ DKT26; Lean `johnson_lineMCA_probability`,
   > `fullSetLevelWitness_interleaved_of_exactAgreement`]

6. **Lemma 4.4.** Use ℓ_i²/2·(2^{m_i}/|F|)^{u_i}, with u_i = 1 (sufficient: worst 2⁻²⁷¹·⁹).

7. **Lemma 4.5.** Write (1−δ_i)^{t_i} = a_i^{t_i}.

8. **§5.** Replace the numbers table and its three bullets with the bound_mca.out values:
   * ε_rbr = 2⁻²⁶⁸·⁰⁶ (O-1) / 2⁻²⁶⁸·⁰¹ (O-1+O-2);
   * worst non-query move 2⁻²⁸⁹·⁷ / 2⁻²⁷¹·⁹ (OOD r1);
   * delete "m = 8 would push it above 2⁻²⁶⁸, so m = 3 is required".

9. **§0 and §9.** Total 2⁻¹³⁴·⁷³ / 2⁻¹³⁴·⁶⁹ (union over 7 layers 2⁻¹³¹·⁹³ / 2⁻¹³¹·⁸⁹); margin
   6.7 bits (3.9 with the union).

10. **References.** Add:
    * [DKT26] ePrint 2026/2056, Thms 5.8, 5.12, Prop 5.10, Lemmas 5.9, 5.11, Cors 7.3, 7.5, 7.7,
      ArkLib @ a5aa267;
    * [Pus26] Tartu MSc 2026, Thm 5.3.

    Re-pin [BCGM] as ePrint v5 (19 May 2026), Def 9.1 / Thm 9.2.

    Tags: S-14 becomes [P′] with a Lean check unless the U-2 reading below is accepted.

## 5. Risks

* **Not peer reviewed.** DKT26 is four weeks old, has one ePrint version, and the authors report
  AI-assisted discovery and formalisation. BCHKS25, Hab25 and Jo26a are also preprints. Only
  BCGM (CCC) is refereed.
* **What the Lean check covers.** It covers the *theorem statements* we use:
  * Johnson line MCA with its finite count;
  * first-order line/curve MCA from a support certificate;
  * interleaving and folds.

  The artifact's checker compares statement excerpts with the pinned ArkLib objects. It does not
  build Lean. We did not build ArkLib or check for `sorry`/axioms. Our 36 integer instances are
  checked by Python exact arithmetic only (`dkt_certs.py --check`; the authors' engine). To close:
  * build ArkLib @ a5aa267 and `#print axioms`;
  * confirm that `johnsonE0` equals the E_ord we use;
  * either port the certificate inequalities for our 36 tuples to `norm_num`, or re-implement
    (59)/(61)–(63) independently.
* **First-order lists are large (≤ 2⁴³·⁴).** One OOD sample suffices only because |F| = 2³⁷⁰·⁹.
  On a smaller field the OOD and γ terms would fail first.
* **The bound.py shapes are not the model's optimum.** Final b = 8/k = 3 in bound.py vs
  b = 7/k = 4 in `extrapolate_nv2`. Certificates must be regenerated for whatever shape is
  finally pinned (`dkt_certs.py`, minutes).
* **The size models use the O-2 grid rule, not the exact per-round table.** Batching
  certificates exist only for the bound.py shapes.
* **U-2 reading.** "Proven, also provable in Lean". DKT Thm 5.12 meets this literally. PROOF.md's
  [P] tag additionally wants refereed work, so adopting O-1 is a user decision on that point. It
  is a source change, not a domain or spec change.

## 6. Reproduce

```
cd research/near-compression/final-soundness/calc
python3 -I bound_mca.py                     # tables of section 0/2 (reads dkt_certs.json)
python3 -I size_mca.py                      # bytes (git show of the model branches)
python3 -I dkt_certs.py <rs-beyond-johnson@60b7257> --check   # re-verify the 36 certificates
python3 -I dkt_certs.py <...>               # regenerate after a shape change; --grid for the model rule
```
