# Gaps, ratings and code-vs-proof mismatches

Companion to `PROOF.md` (lane `lane/pq-final-soundness`, 2026-10-18).

Ratings:
* **proven**: a published, refereed theorem applies as used.
* **proven-with-new-lemma-here**: the proof is written in PROOF.md, but it is new and has not
  been reviewed.
* **relies-on-unreviewed**: it rests on a preprint, a project note, or code and tests without
  a written proof.
* **open**: not proven, or contradicted by the code as written.

## A. Proof steps

| # | step | where | rating | notes |
|---|---|---|---|---|
| S-1 | Oracle split by framing, truncation (narrow 336 b / wide 384 b) | Lemma 1.1 | proven-with-new-lemma-here (elementary) | Node prefix under the 42-B lever is `NPQ5‖0x2a‖C‖ND`, not `NPQ4NODE` (SHA:35-37); still disjoint from the framed `n…` prefix. |
| S-2 | rbr-KS definition, list-form ⇒ rbr-KS, union over list | Def 2.1, Lemmas 2.3–2.4 | proven-with-new-lemma-here | Lemma 2.4 = HROB Lemma 4.7 at m = 0. |
| S-3 | Gruen rounds, derived claims, masked/zero claims, WHIR-Y absorption | Lemma 2.5 | proven-with-new-lemma-here | Gruen's own soundness remark is informal (ePrint 2024/108 App. A.3). |
| S-4 | LogUp α, β | Lemma 3.1 | proven-with-new-lemma-here (standard) | Proves balance **mod p** only; intended semantics pushed to NV-faithful (F4). |
| S-5 | Fractional GKR | Lemma 3.2 | proven-with-new-lemma-here (standard) | |
| S-6 | Zerocheck point = GKR point (implicit claims) | Lemma 3.3 | proven-with-new-lemma-here | Needed because ξ reuses GKR randomness. |
| S-7 | λ sampled before the per-AIR claims | Lemma 3.4 | proven-with-new-lemma-here | **Sound as is**, because λ only enters claim-independent terms and the claims are fixed before μ. |
| S-8 | Univariate-skip zerocheck | Lemma 3.5 | proven-with-new-lemma-here (standard) | d = 21. |
| S-9 | Program binding as part of the relation | Lemma 3.6 | proven-with-new-lemma-here | Without it a valid trace with a different program could pair with false program openings. NV must arithmetise V′ (F2). |
| S-10 | Stacking + tight heights kernel identities (multilinear form) | Lemma 3.7 (a), (b) | proven-with-new-lemma-here | |
| S-10′ | The same identities in the code's univariate-skip encoding (`chunk_factors`, rotation correction δ_i) | Lemma 3.7 remark | **relies-on-unreviewed** (code + 24 tamper tests) | If (b) were mis-encoded, transition constraints across chunk boundaries could go unchecked. Needs a line-by-line derivation or a Lean/symbolic check (G-6). |
| S-11 | Next-row mask | Lemma 3.8 | proven-with-new-lemma-here | Requires the mask ⊇ the DAG's offset-1 reads (keygen computes it). |
| S-12 | WHIR Thm 5.2 rbr (Johnson regime, list form) | Lemmas 4.3–4.7 | proven (WHIR, Eurocrypt 2025 / ePrint 2024/1586) | The "2026 Tartu corrections" mentioned in earlier logs were not located by anyone; not covered. |
| S-13 | WHIR on 15·2^K domains | Lemma 4.1 | relies-on-unreviewed (x15 SOUNDNESS.md, re-checked here) | One definitional edit of WHIR's hypothesis. |
| S-14 | MCA in the Johnson regime, explicit constant | Lemmas 4.2–4.3 | proven (BCGM, CCC 2026; Def 9.1 / Thm 9.2 of the ePrint full version) | The CCC "Thm 5" numbering is unverified; the ePrint numbering is verified. |
| S-15 | Grinding inside one call | Lemma 5.1 | proven-with-new-lemma-here | **Holds only under T\*-2** (G-2). |
| S-16 | One-layer rbr-KS error ε_rbr = 2⁻²⁶⁸·⁵⁵ | Thm 5.2, bound.py | proven-with-new-lemma-here | Worst move: WHIR query, round 0, inner NV. |
| S-17 | Counter mode ≡ one long-output call (t → 2t) | Lemma 6.3 | proven-with-new-lemma-here (elementary) | Needs T\*. |
| S-18 | Multiproof ⇒ per-leaf paths | Lemma 6.2 | proven-with-new-lemma-here | |
| S-19 | QROM BCS straight-line KS for layer families (K = 0, two-level chain) | Thm 6.4 | **proven-with-new-lemma-here**, built on weak-binding Thm 4 / Lemmas 1–2 (relies-on-unreviewed: one adversarial review, REVIEW-1) | Same t²ε shape as CMS19 Thm 8.6, Fractal Thm 10.1 and CDHZ Thm 11.3 (cross-checks 2⁻¹³⁷·⁵ / — / 2⁻¹³⁰·⁴). The highest-value item to review or formalise. |
| S-20 | Recursive composition, one database, straight-line | Thm 7.4 | proven-with-new-lemma-here, **given A-IC** | Error is independent of d. |
| S-21 | NV circuit arithmetises V′_{i−1} faithfully | Lemma 7.1 (F1–F6) | **relies-on-unreviewed** (circuit lane, in progress) | Exact required form stated. |
| S-22 | Layer-0 AIRs encode chunk validation | Lemma 7.2 | **relies-on-unreviewed** | Out of scope here. |
| S-23 | In-circuit SHA-384 ≡ random oracle (A-IC) | Assumption 7.3, §8 | **closed: unprovable in any query-only oracle model** (Thm O, `lane/pq-aic-research` LEMMA.md); adopted as A-IC(τ), U-11/U-12 | User decision 2026-10-18: the recursive claim is time-bounded (τ = 2¹²⁸) under A-IC(τ). U-2 not met on this point, by necessity. |
| S-24 | Base-layer parameters (W, degree, interactions, commitments) | bound.py | **open** (not pinned) | A stress shape (W = 601, 2 commitments) passes at 2⁻²⁶⁸·⁵⁵. Re-run with the real app vk. |
| S-25 | Efficient extraction | §7.3 | proven (GS list decoding) / not needed | The theorem only uses existential extraction. |

## B. Code-vs-proof mismatches (tree U = stark-backend-unified, SHA = native_sha384_levers_config.rs)

| # | severity | what | where | consequence | fix |
|---|---|---|---|---|---|
| **G-1** | **proof gap (open)** | Challenges are squeezed through a sequential chain σ_{j+1} = H(5, σ_j); the challenge words are the chain states themselves. Query moves need 4–7 blocks; an Ext12 sample needs 2 blocks about 54 % of the time. | SHA:160-171 (in-circuit twin likewise) | No QROM theorem (CMS19, CDHZ, Thm 6.4) covers multi-call challenges. The worst-case-over-database transition loses ≈ ε^{1/k}. Not an attack: nested amplitude amplification suggests only a poly(k) loss, but that is unproven. The U-10 basis ("Grover-tight") silently assumed one call ([H-M] in the weak-binding notes). | **T\*-1**: B_j = H(5, κ‖le32(j)) from the post-absorb key κ; next state = last block consumed. 0 proof bytes, 0 extra compressions (input +4 B). Native verifier, prover and NV circuit must change together. |
| **G-2** | **proof gap (open); breaks the grinding credit** | PoW bits are the leading bits of the absorb output s′ = H(7, σ‖w); query indices come from later calls H(5, s′), … | SHA:142-186; U whir.rs:175-196 | Lemma 5.1 fails. The provable per-round error is the ungrinded 2⁻²³⁶·⁵⁵, which gives 2⁻¹⁰⁵ total: **fails U-6**. | **T\*-2**: B_j = H(7, σ‖w‖le32(j)); PoW on the first z bits of B₁; indices from the remaining words. Honest grind cost unchanged (1 compression per attempt). |
| G-3 | info | WHIR-Y present only in the unified tree | U whir.rs:315-320; absent from the levers-only and x15-only patches | None if production uses U. At 42 B, WHIR-Y is not needed for soundness (PROOF §4, Lemma 4.6 remark); it is needed for any digest < 256 b. | Pin U as the production tree. |
| G-4 | info | Node hashes carry no position or tree tag | SHA:91-99 | None at 42 B (K = 0 tolerates no collision anyway; |Chg| ≤ 3t′ accounted). Required only for weak-binding < 41 B digests. | — |
| G-5 | ok | λ sampled before the per-AIR claims | batch_constraints.rs:311 vs 315-320 | Sound (Lemma 3.4). | — |
| G-6 | relies-on-unreviewed | tight-heights kernel in the univariate-skip encoding | stacked_pcs.rs:90-103, stacked_reduction.rs:220-236 | See S-10′. | Write the derivation or check it symbolically. |
| G-7 | ok | ×15 sampler: native re-samples on p − 1, circuit rejects | U traits.rs:62-71; NV verifier.rs:244-249 | Both exact (Lemma 4.1). | — |
| G-8 | ok | Merkle multiproof | whir.rs:470-515 | Sound (Lemma 6.2); duplicate leaves must agree (checked). | — |
| G-9 | low | For a trace with common_main = 0, both `tight_height = None` and `Some(h)` pass, and the absorbed word count differs: the preamble encoding is non-injective. | proof_shape.rs:561-569; proof.rs:559-561; mod.rs:149-152 | Semantically irrelevant (no columns to chunk), so no state-function ambiguity. Malleability only. | Reject `Some` when common_main = 0. |
| G-10 | low | The verifier trusts the vk pre-hash (does not recompute it from the vk); `c` (odd factor) is `serde(skip)` and not in the pre-hash. | mod.rs:129; config.rs:203 | The verifier uses its own params, so it is sound. For recursion the pre-hash and all params must be constants of the parent program, and of the native V_d (NV-faithful F2). | Bind `c` in the pre-hash. |
| G-11 | low | PoW witness neither absorbed nor checked when bits = 0 | traits.rs:83-85; SHA:173, 182 | Proof malleability only (e.g. logup pow_bits = 0). | Require a zero witness. |
| G-12 | info | The soundness calculator ignores digest truncation, multi-target Merkle terms and WHIR-Y; its comment "Merkle proofs are observed before γ" is wrong. Its γ batch counts q + 1 in the final round (conservative). | calculator.rs:356-545, 482 | The calculator is not a proof. Use `calc/bound.py`. | Fix the comment; add the hash terms. |
| G-13 | info | Only the first WHIR round's fold is configurable (k₁); there is no per-round vector | config.rs:472-478 | Matches the analysed protocol. | — |

## C. What would close the contract

1. Implement T\* (G-1, G-2) in prover, native verifier and NV circuit. Re-measure: the size is
   unchanged; the SHA count should change by under 1 %.
2. Independent review, or Lean formalisation, of Theorem 6.4 and weak-binding Lemmas 1–2 (S-19).
3. The circuit lane's NV-faithful proof, in the form of Lemma 7.1 (S-21), and Base-faithful (S-22).
4. The univariate-skip derivation of the tight-heights kernel (S-10′).
5. Pin the app-layer parameters and re-run `calc/bound.py` (S-24).
6. ~~A user decision on A-IC (S-23)~~ Decided 2026-10-18 (U-11, U-12: A-IC(τ), τ = 2¹²⁸, final-layer prefix). Original text:: accept it as the U-1/U-7 in-circuit-RO assumption, which
   leaves U-2 unmet for the recursive step, or keep the final claim to non-recursive proofs. No
   known technique removes it for hash-only recursion.
