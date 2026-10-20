# Gate 1: WHIR soundness on 15·2^N evaluation domains (paper check)

Date: 2026-10-17. Lane `lane/pq-x15-domains`. Status labels used below:
- **[proven]**: a published theorem applies, verbatim or with the stated edit.
- **[checked]**: the proof was read here and the edit below is enough.
- **[computed]**: arithmetic from `rbr_x15.py` (output in `rbr_x15.out`).
- **[measured]**: run on this host.
- **[open]**: not settled.

## Setting

- BabyBear: p = 15·2^27 + 1. |Ext12| = p^12, so log2|F| = **370.88**. Earlier notes used 372 = 12·31; that is 1.1 bits optimistic.
- Evaluation domain of round i: D_i is the multiplicative subgroup of order n_i = 15·2^(N−i). Write D_i = ⟨ζ⟩ × H_(N−i), where ζ = g^((p−1)/15) and g is the field generator. Equivalently, D_i is the disjoint union of the 15 cosets ζ^a·H.
- Folding map: x ↦ x^(2^k).
- The trace domain (the hypercube 2^n and the univariate-skip subgroup 2^l_skip) is unchanged. Only the RS evaluation domain grows.
- Contract: proven bounds only. Per-round (rbr) error ≤ 2^-258 to 2^-268, so that the CMS19 rbr→QROM loss leaves ≤ 2^-128 at 2^64 quantum queries.

Sources read:
- **WHIR**: ePrint 2024/1586, the 21 Nov 2024 version (web.archive snapshot).
- **BCGM**: Bordage–Chiesa–Guan–Manzur, ePrint 2025/2051, the 19 May 2026 version. Thm 9.2 is the MCA theorem the contract relies on (CCC 2026 Thm 5).
- **BCHKS25**: Ben-Sasson–Carmon–Haböck–Kopparty–Saraf, ECCC TR25-169, Thm 1.5. The pinned stark-backend calculator uses it.
- I could not locate the "Tartu corrections" referenced in C-invention.md, so they are not covered here.

## Where WHIR uses "smooth" (= power-of-two order)

WHIR §3 defines smooth: "L is smooth if it is a multiplicative coset of F* whose order is a power of 2". Def 4.2 and Construction 5.1 require it. Searching the paper for every use of the hypothesis gives exactly four properties of L:

| # | Property used | Where | Holds for 15·2^N? |
|---|---|---|---|
| P1 | x ∈ L ⇒ −x ∈ L (needs 2 \| \|L\|) | Def 4.14 (Fold), Claim 4.15, Claim 4.22, footnote 6 | yes, since −1 ∈ H |
| P2 | \|L^(2^j)\| = \|L\|/2^j and L^(2^j) is again a multiplicative coset (needs 2^j \| \|L\|) | §2.1 ("since L is smooth … \|L^(i)\| = \|L\|/i"), Construction 5.1 domains, Thm 4.20 codes C^(i) | yes for j ≤ N |
| P3 | Block(L,k,z) = {y : y^(2^k) = z} are disjoint and each has exactly 2^k elements (the fibres are cosets of μ_(2^k) ⊆ L) | Def 4.16, Claim 4.19 ("Since C is smooth … disjoint sets each of size 2^k") | yes, since μ_(2^k) ⊆ H for k ≤ N |
| P4 | Degree bound 2^m, so RS = multilinear evaluations via pow(x,m) | Def 4.2 | yes: this is a degree condition, not a domain condition |

None of the four uses the odd part of |L|. For our domains, P1–P3 hold whenever 2^(max k_i) divides |L_i|, which holds because N − i ≥ k_i in every round.

## Verdict per lemma

| Lemma / theorem | Domain hypothesis in the source | Verdict for D = 15·2^N |
|---|---|---|
| WHIR Thm 4.3 (Johnson list size 1/(2η√ρ)) and Lemma 4.4 (interleaved list size) | any RS code; depends only on ρ | **holds verbatim** [proven] |
| WHIR Def 4.14 / Claim 4.15 (folding a codeword gives a codeword on L^(2^k), ĝ = f̂(α,·)) | P1, P2 | **holds with the edit** "L is a multiplicative coset of order c·2^K, c odd, k ≤ K". The proof is a pointwise identity at x and −x. [checked] |
| WHIR Claim 4.19, Thm 4.20, Lemma 4.21, Claims 4.22–4.23 (block distance; folding preserves list decoding given MCA) | P1–P3 | **holds with the same edit** [checked] |
| WHIR Lemma 4.24 / 4.25 (OOD sampling; ACFY24 Lemma 4.5), error 2^m·ℓ²/(2\|F\|) | any RS code, list size ℓ | **holds verbatim** [proven] |
| WHIR Thm 5.2 sumcheck terms d·ℓ/\|F\| (ε_fold, sumcheck part) | none | **holds verbatim** [proven] |
| WHIR Thm 5.2 ε_shift = (1−δ)^t + ℓ(t+1)/\|F\| and ε_fin = (1−δ)^t | the z_(i,j) are **uniform** on L_(i−1)^(2^k) | **holds with a modification**: queries must be exactly uniform over a set of size 15·2^(N−i−k). This uses the exact sampler described below, which is implemented. [checked] |
| WHIR Thm 5.2 as a whole (rbr soundness of Construction 5.1) | smooth L_0…L_(M−1); MCA for C^(i,s) = RS[F, L_i^(2^s), m_i − s] | **holds with the edit** "smooth" → "multiplicative subgroup or coset of order c·2^K with K ≥ k_i + i", plus the exact sampler. The theorem keeps its error terms, evaluated at the true n_i = 15·2^(N−i) and ρ_i = 2^(m_i)/n_i. [checked] |
| WHIR Thm 5.6 (batching t constraints, error (t−1)ℓ/\|F\|) | none beyond list decodability | **holds verbatim** [proven] |
| **MCA: BCGM Thm 9.2 (CCC 2026 Thm 5)**, error (m+½)^7/(3ρ^(3/2))·d·n²/\|F\| for γ ≤ 1 − (1+1/2m)√ρ, m ≥ 3 | Def 3.8: RS[F, D, k] for **any D ⊆ F**. Lemma 9.3's proof is Guruswami–Sudan interpolation over arbitrary D (BCIKS20 Thm 5.1 §6.2) plus the zero-evading Lemma 5.3; it needs only \|F\| > (m+½)²n | **holds verbatim** [proven]. Neither multiplicative structure nor smoothness is assumed. BCGM Def 3.14 (MCA) matches WHIR Def 4.9's "proximity generator with mutual correlated agreement" term for term (∃T with \|T\| ≥ (1−γ)n, combined word in C\|_T, some u_j\|_T ∉ C\|_T). D ⊆ F_p ⊂ Ext12 is allowed, since D is any subset of the code's field. |
| BCHKS25 Thm 1.5 (CA up to Johnson, a > (2(m+½)^5 + 3(m+½)γρ)/(3ρ^(3/2))·n + (m+½)/√ρ) | RS[F_q, D, k], **any D** | **holds verbatim** (CA). The backend applies Haböck's extension to get MCA; that step is unchanged by the domain. BCHKS25 §1.4.3 / Thm 1.13 give negative examples on multiplicative subgroups *beyond* the Johnson radius (δ − 2/b). They apply equally to 2^N subgroups and do not reach our radius. |
| CMS19 rbr → QROM | domain-free | **holds verbatim** |

**Nothing is open at the level of theorems** [checked]. The 15·2^N domain changes only the numbers n and ρ that enter the existing error terms. Two engineering items are needed for the theorem to apply:
1. exactly uniform query sampling over 15·2^j indices;
2. a fold-coset layout and Merkle binding over 15·2^j leaves.

Both are designed and implemented below.

## Power-of-two structure in the protocol and backend (stark-backend v2.0.1 @ d667af5)

| Place | 2-adic assumption | Status in the x15 patch |
|---|---|---|
| `prover/stacked_pcs.rs::rs_code_matrix` | one radix-2 DFT of size 2^(h+b) | replaced (for c > 1) by 15 radix-2 **coset** DFTs with shifts ζ^a, stored coset-major |
| `MerkleTree::new` | height padded to `next_power_of_two` with zero rows; fold coset = rows i + j·H/2^k | **silently wrong for 15·2^L**: it would pad to 16·2^L and pair non-fibres. New `new_with_cosets` builds each coset block exactly as upstream, concatenates the blocks, and pads odd-length upper layers with the fixed digest H(""). Depth is L − k + ⌈log2 15⌉ = L − k + 4. |
| `ColMajorMatrix::new` | asserts power-of-two height | `new_any_height` added for RS matrices |
| `prover/whir.rs`, `verifier/whir.rs` | `two_adic_generator(L)`, `sample_bits(L−k)`, codeword `dft`, tree height `1<<L` | replaced by `odd_domain::{query_root, sample_query_index, rs_encode}` and height `c<<L` |
| `binary_k_fold` | `two_adic_generator(k)` for the fibre ω_(2^k) | unchanged (μ_(2^k) ⊆ H) |
| `verifier/proof_shape.rs` | Merkle depth L − k (− round) | + ⌈log2 c⌉ |
| `transcript::sample_bits` | x mod 2^j of a uniform x ∈ [0,p): residue 0 is heavier by 1/p (the calculator charges for this) | for c > 1, the new `sample_index_exact(n)` rejects x = p−1 and returns x mod n. Because n \| p−1 = 15·2^27, this is exactly uniform. |
| soundness calculator and `WhirConfig::queries` | integer log_inv_rate; n = 2^(…) | for c > 1: real-valued rate 2^-b/15 and n = 15·2^(…) in BCHKS25, the list size, the query bits (no bias term), OOD and γ |
| transcript extractor | one sample per query index | refuses c ≠ 1 |
| zerocheck, stacked reduction, univariate skip (`two_adic_generator(l_skip)`), `eval_to_coeff_rs_message` | trace domain only | unaffected (the trace domain stays 2^n) |
| `cpu-backend` / `cuda-backend` crates | own LDE/Merkle code | not patched. They would ignore c, so their proofs would fail the x15 verifier (fail closed). They need porting before use. |
| `memory_metering.rs` | 2^(h+b) sizes | not updated (estimates only) |

The query sampler matters because WHIR's (1−δ)^t needs exactly uniform z. Reducing a 64-bit word mod 15 would add a statistical distance of about 2^-60 per query, which is far above the 2^-258 per-round budget. The rejection rule above is exact. An in-circuit verifier may *reject the proof* on x = p−1 instead of resampling. That keeps soundness exact and costs completeness of about q/p ≈ 2^-25 per proof.

## Per-round errors at the model's parameters [computed]

`rbr_x15.py` evaluates every term of WHIR Thm 5.2:
- ε_fold = 3ℓ/|F| + ε_MCA(d=1), over all sub-rounds s ≤ k_i of all rounds i, on L_i^(2^s);
- ε_out = 2^(m_i)·ℓ²/(2|F|);
- ε_shift = (1−δ)^t + ℓ(t+1)/|F|;
- ε_fin = (1−δ)^t.

Other inputs:
- ℓ = m/ρ, the Johnson bound at η = √ρ/2m, with δ = 1 − (1+1/2m)√ρ, which equals BCGM's γ bound.
- The initial **μ-batching** of the W stacked columns uses the powers generator of degree W−1, so it costs ε_MCA(d = W−1). Earlier notes omitted this term.
- t is chosen as ⌈target / per-query bits⌉. Targets: 268 (T), or 236/226 with z = 32 grinding (L).

Shapes are the models-C fixed point at the measured c_sha = 19,448 with 460 columns. n_0 = 15·2^27 = 2^30.91 in every row.

Worst **non-query** term (log2) under **BCGM Thm 9.2**, the contract bound:

| scenario | W | m = 3 | margin to 2^-268 | m = 8 | margin to 2^-268 / 2^-258 |
|---|---:|---:|---:|---:|---:|
| T ×15 final (b7, h20, k4) | 151 | μ −274.4 (fold −280.6) | +6.4 | μ −265.5 (fold −271.7) | −2.5 / +7.5 |
| T ×15 penultimate (b9, h18, k3) | 601 | μ −269.4 | +1.4 | μ −260.5 | −7.5 / +2.5 |
| L ×15 final | 133 | μ −274.6 | +6.6 | μ −265.6 | −2.4 / +7.6 |
| L ×15 penultimate | 529 | μ −269.6 | +1.6 | μ −260.6 | −7.4 / +2.6 |
| T COMBO+E5 final (non-shrinking) | 96 | fold −270.1 | +2.1 | fold −261.2 | −6.8 / +3.2 |
| T COMBO+E5 penultimate | 191 | μ −272.6 | +4.6 | μ −263.6 | −4.4 / +5.6 |
| L COMBO+E5 final | 86 | fold −270.1 | +2.1 | fold −261.2 | −6.8 / +3.2 |
| L COMBO+E5 penultimate | 342 | μ −270.2 | +2.2 | μ −261.3 | −6.7 / +3.3 |
| stress: n = 2^30.91, ρ = 2^-11.91 | 111 | μ −273.4 (fold −279.1) | +5.4 | μ −264.4 (fold −270.2) | −3.6 / +6.4 |
| same shape, power of two (n = 2^27, ρ = 2^-8) | 111 | μ −287.0 | +19.0 | μ −278.1 | +10.1 |

- OOD terms are ≤ 2^-314 everywhere.
- The query terms equal the design target (2^-268, or 2^-258 including grinding).
- Under BCHKS25, which is linear in n, every non-query term is ≤ 2^-294 (m = 3 or 8). That gives a margin of ≥ 26 bits.

Readings:
1. **m = 3 is required under BCGM** if the per-round target is 2^-268. m = 8 fails 2^-268 by 2.4–7.5 bits. The failing term is μ-batching (d = W−1), or the late-round fold MCA under non-shrinking domains (ρ^(-3/2) grows by 2^(4.5) per round while n stays the same). m = 8 passes 2^-258 with 2.5–7.6 bits to spare. The model's m = 3 penalty is about +4 KB.
2. At equal n and ρ, a 15·2^N domain and a (hypothetical) 2^(N+3.9) domain give identical errors: the bounds depend only on n and ρ. Against the power-of-two domain with the same 2-adic shape (same h and b), the ×15 domain loses 13.6 bits: n² grows ×225 and ρ^(-3/2) grows ×58. That loss is the price of the 15× lower rate, which is what buys the ≈ 1.95 extra bits per query.
3. The tightest rows with m = 3 are the penultimate μ-batching at W ≈ 530–600 (+1.4 bits) and E5 (+2.1 bits). To widen them: a W-way independent-challenge batching does not help (error Σd_i = W, the same). Options that do help:
   - a few bits of μ-PoW;
   - fewer stacked columns (a taller stacking height);
   - or the BCHKS25-based bound, if the contract admits it.
4. The L4-C note's "m = 8 → 2^-270.9" figure used |F| = 2^372 and only round 0. Recomputed over all rounds with |F| = 2^370.88, the figure is 2^-270.2. The μ term then dominates at 2^-264.4.

## Gate 1 verdict

- **Theorem level: PASS** [checked]. Every lemma WHIR's soundness uses holds for 15·2^N domains:
  - verbatim: list decoding, OOD, sumcheck, batching, BCGM MCA and BCHKS25 CA, which are stated for arbitrary evaluation sets;
  - with one definitional edit ("smooth" → order c·2^K, 2^k | order): folding, block distance, folding preserves list decoding, Thm 5.2;
  - with exactly uniform query sampling over 15·2^j indices: Thm 5.2's shift and final terms.
- **Parameter level: PASS with m = 3** [computed]. Every non-query term is ≤ 2^-269.4 at all model shapes, with a minimum margin of 1.4 bits at the penultimate μ-batching. **m = 8 does not meet 2^-268** under BCGM; it does meet 2^-258.
- Not a proof artefact: these are pen-and-paper checks of published proofs, not a mechanised proof. A written lemma "WHIR Thm 5.2 for c·2^K domains" should be added to the security write-up before adoption.
