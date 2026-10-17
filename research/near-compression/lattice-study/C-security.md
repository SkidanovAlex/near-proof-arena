# C — Security of a lattice-based final wrap under the NearProof contract

Contract being checked: failure ≤ 2^-128 against ≤ 2^64 **quantum** RO queries (QROM), PQ end to end,
**proven** soundness bounds only, SHA-384 as RO, exact-witness knowledge soundness composable with the
inner STARK, eventual Lean formalization.

Sources were fetched to `lattice/pdf/` (PDF + pdftotext): 2022/1341 LaBRADOR, 2024/1293 Greyhound,
2024/257 LatticeFold, 2025/247 LatticeFold+, 2025/294 Neo, 2026/242 Neo+SuperNeo, 2024/1964 Lova,
2024/1972 RoK-Paper-SISsors, 2025/1220 RoK-and-Roll, 2026/575 RoKoko, 2026/156 Hachi,
2019/834 CMS19, 2019/190 DFMS19, 2020/282 DFM20, 2021/1377 AFK22, 2023/1945 AFKR (JoC 2025),
2023/1256 BGTZ23, 2022/889 LMS22, 2021/1543 LMS21.

Labels: **[P]** proven (published theorem), **[O]** known open (literature says so), **[I]** my inference.

---

## Q1. Fiat–Shamir in the QROM for multi-round lattice arguments

### What exists
- **[P] DFMS19 (2019/190), Σ-protocols (one challenge round):** FS adversary → interactive adversary,
  success ε_FS ≤ (2q+1)^2 · ε_int (measure-and-reprogram). Also Liu–Zhandry 2019/262.
  Knowledge soundness in QROM follows only if the *interactive* protocol has post-quantum
  knowledge soundness (needs quantum rewinding, e.g. collapsing + special soundness, Unruh).
- **[P] DFM20 (2020/282), multi-round public-coin:** loss **(2q+n+1)^{2n}** for n challenge rounds
  (lines ~94, 532, 708 of the text); the authors show O(q^{2n}) is optimal *in general*. Works for
  computationally sound arguments (generic reduction). For q = 2^64 and n challenge rounds the loss is
  ≈ 2^{130 n}.
- **[P] CMS19 (2019/834), BCS of IOPs:** soundness error **O(t^2 ε_rbr + t^3/2^λ)** (Thm 8.6; big-O
  constants). Requires *statistical* round-by-round soundness of an *IOP* whose oracles are
  Merkle-committed with the RO. Also gives knowledge soundness from rbr-knowledge soundness.
- **[P] BGTZ23 (2023/1256):** (k_1..k_μ)-special soundness ⇒ rbr soundness with ε_i = (k_i−1)/|C_i|,
  hence (via CMS19) special-sound IOPs are QROM-**sound** after BCS. But Thm 1.3: special soundness
  does **not** imply rbr **knowledge** soundness, so no QROM knowledge soundness follows. Moreover
  the theorem is for unconditional special soundness of IOPs; lattice protocols are only
  *computationally* special sound (extractor outputs witness **or** an MSIS solution), and their
  commitments are Ajtai, not RO-Merkle — so CMS19/BGTZ23 do not apply as stated. [I]
- **[P] LMS22 (2022/889, TCC'22):** post-quantum knowledge soundness of *interactive* lattice
  Bulletproofs (recursive special soundness + "fold-collapsing" Ajtai hash), assuming
  **(Ring-)LWE** (not MSIS alone). Remark 1: explicitly leaves open making lattice Bulletproofs
  non-interactive in the QROM ("we leave open the problem of extending this to the quantum setting").
- **[P, classical only] ROM results with round-independent loss:** AFK22 (2021/1377):
  FS of (k_1..k_μ)-special-sound protocols has knowledge error (Q+1)·κ; AFKR (2023/1945, JoC 2025)
  extends to (Γ_1..Γ_μ)-special soundness; FMN24 (JoC, "Lattice-based polynomial commitments…",
  §8) covers coordinate-wise special soundness (CWSS) used by LaBRADOR-family proofs.
- **[O] Explicit statement of the gap (AFKR 2023/1945, §1, lines 475–485):** "[DFM20] … with an
  exponential loss in the number of rounds for multi-round protocols, [LMS22] … Bulletproofs-like
  interactive protocols are knowledge sound against quantum adversaries … many of the classical
  knowledge soundness results for (the Fiat–Shamir transformation of) interactive proofs do not have
  closely-matching quantum counterparts (yet)."
- **[O] Paper-by-paper:**
  - LaBRADOR (2022/1341): only mentions FS for proof size; knowledge soundness proven interactively,
    classically (Thm 5.1, ε0 = 2^-125; Thm 6.2). No ROM or QROM FS theorem.
  - Greyhound (2024/1293): "can be transformed … using Fiat-Shamir" (l.495); cites AFK22 classically.
    No QROM.
  - LatticeFold (2024/257) Remark 3.3: "The knowledge analysis of the Fiat-Shamir transformed version
    of Πfold is left as future work." LatticeFold+ / Neo / SuperNeo: "plausible post-quantum
    security", interactive analyses, no QROM FS theorem found.
  - RoK-Paper-SISsors (2024/1972, p.49): "we can **heuristically** assume that the tree-special
    soundness extractors from [AFK22] are applicable … heuristically, there is an extractor for the
    Fiat–Shamir-compiled protocol" (classical ROM, heuristic). Hachi (2026/156): ROM via FMN24 §8.
    RoKoko (2026/575): BLAKE3 FS, no analysis. Lova: nimue, no QROM.
  - Searches found no paper proving QROM (knowledge) soundness with explicit losses for LaBRADOR,
    Greyhound, LatticeFold(+), Neo, SuperNeo, Lova, RoK*, Hachi. **None exists to my knowledge as of
    2026-10.**
- **Context [P]:** Dupuis–Lamontagne–Salvail, "Fiat-Shamir for proofs lacks a proof even in the
  presence of shared entanglement" (Quantum 8:1568, 2024; arXiv 2204.02265): a negative result for
  standard-model (non-idealized) FS for proofs, even allowing shared entanglement — i.e. we cannot
  expect to escape an idealized-oracle model; it does not affect QROM results.

### Losses that would apply and per-round soundness needed
- **[P] Only proven QROM route today:** DFM20 generic, loss (2q+n+1)^{2n}, plus a *separate*
  post-quantum (quantum-rewinding) soundness proof of the interactive protocol, which for LaBRADOR
  does not exist (LMS22 covers simpler Bulletproofs and needs LWE). LaBRADOR has ~4 challenge rounds
  per level (JL projection, two aggregations, amortization) × ~6–8 recursion levels ⇒ n ≈ 25–35 ⇒
  loss ≈ 2^{3000+}. Unusable. [I on round count]
- **[I] If a CMS19-style result (O(t^2 ε_rbr)) were proven for computational lattice arguments:**
  need t^2·ε_i ≲ 2^-128 with t = 2^64 ⇒ **ε_i ≲ 2^-256 per round** (minus constants, so ≈ 2^-260).
  Compare: LaBRADOR JL projection failure ≈ 2^-128 per invocation; challenge sets |C| ≈ 2^128
  (Neo §6.1: |C| = 2^128, |K| ≈ 2^128); interactive ε0 = 2^-125. All would need roughly squaring
  (bigger projections ~2×, extension degree ~2×, challenge spaces 2^256).
- **[I] Even the classical ROM (AFK) bound (Q+1)κ needs κ ≤ 2^-192.** Current lattice parameter sets
  (2^-125 … 2^-128) do not meet our target even classically.
- **[I] DFM20 with very few rounds:** if the wrap could be collapsed to n=1 challenge round,
  loss ≈ 2^130 ⇒ interactive error ≤ 2^-258 and post-quantum interactive soundness still needed.

---

## Q2. Relaxed vs exact extraction

- **[P] LaBRADOR:** principal relation proven with **norm slack √(128/30) ≈ 2** (Thm 5.1); Remark 5.2:
  under recursion, MSIS norm bounds must grow by this factor. Extraction is *computational*: extractor
  outputs a slack-witness or an MSIS solution (via weak openings of Ajtai commitments).
- **[P] LaBRADOR binary-R1CS reduction (§6, Thm 6.2) recovers an EXACT witness:** binarity is proven
  as ⟨a, ã − 1⟩ = 0 mod q, and since ‖a‖² < q (with slack factor), the identity holds over Z ⇒
  coefficients ∈ {0,1}; products via a+b−2c ∈ {0,1}; F2-linear constraints via random combinations
  (error 2^-l). Conditions n+3k < q, 6k < q, and n+3k < 15q/128 for slack. Soundness relies on
  MSIS with l∞-bound 1.
- **[P] Greyhound:** extracts only relaxed openings R*: c_i·s_i short with ‖c_i‖_1 ≤ κ̄ (l.749–760).
  The opened polynomial is determined (c_i invertible) but not guaranteed short.
- **[P] LatticeFold/LatticeFold+:** "relaxed binding" commitments, but range proofs (sumcheck-based /
  purely algebraic in +) force extracted witnesses to be valid **low-norm** witnesses of the original
  relation. Neo: intermediate steps are "ϕ-relaxed knowledge sound" (large-norm witnesses), composition
  theorem (Thm 5) restores knowledge soundness for the original CCS relation.
- **[I] Implications for our wrap:** an exact accepting STARK proof *can* be extracted if the wrap
  relation is binary R1CS (or equivalent) whose constraints imply the integer/F2 constraints despite
  slack (LaBRADOR §6 style), with every verifier check (SHA-384 bit-circuit, field arithmetic of the
  inner STARK via bit decomposition / range checks) encoded so that "valid mod q with norm < √q-ish"
  ⇒ "valid over Z". This is a design obligation, provable on paper. But:
  1. "Knowledge soundness" is only "witness **or** MSIS break", so the end-to-end bound must add an
     MSIS advantage term for an extractor whose running time is ≈ Q·Πk_i·T_A (CWSS amortization makes
     some k_i ≈ r+1). See Q3 on what bit-security that implies.
  2. The extractor is classical rewinding; for quantum adversaries a quantum-rewinding extractor is
     needed and does not exist for LaBRADOR (Q1).
  3. **[O] Oracle-relativization:** the wrap circuit evaluates SHA-384 concretely to verify the inner
     STARK, while the inner STARK's soundness is proven with SHA-384 as a (Q)RO. No RO-model SNARK can
     prove statements about its own oracle; recursive composition proofs in idealized models need
     relativized/arithmetized-RO models (Chiesa–Ojha–Spooner; Chen–Chiesa–Fenzi–Zhang AROM,
     EUROCRYPT'23), classically only. This gap exists for any wrap of a hash-based proof (STARK→STARK
     too), not only lattices.

---

## Q3. Concrete MSIS/MLWE hardness

- **[P/heuristic split]** There is no proven concrete lower bound for MSIS (it would imply P≠NP-type
  separations). Worst-case→average-case reductions (Langlois–Stehlé 2015 for modules) are asymptotic
  and loose; nobody sets parameters from them. Parameters are set with the **lattice estimator**
  (Albrecht et al., malb/lattice-estimator) or core-SVP (ADPS16): heuristic models (GSA, sieving cost,
  dimensions-for-free), i.e. **conjectured**, not proven. LaBRADOR uses core-SVP with **classical
  BDGL 0.292β** (l.1713); Neo uses the estimator plus a δ = 1.0045 root-Hermite rule of thumb (2018/773).
- **[I] Numbers:** 2^{cβ} ≥ 2^128 ⇒ β ≥ 439 (c=0.292, classical), β ≥ 483 (c=0.265, Laarhoven
  quantum sieve), β ≥ ~498 (c≈0.257, Chailloux–Loyer 2021 quantum-walk sieve; Bonnetain et al. 2023
  ≈0.2563). So "128-bit" lattice parameters in these papers are ≈116-bit under 0.265 core-SVP.
  Quantum exponents assume QRAM; core-SVP ignores poly factors and memory (conservative in that sense).
- **[I] Success-probability regime:** our contract asks Pr ≤ 2^-128 for 2^64-query adversaries. An
  MSIS term in the bound must therefore satisfy Adv_MSIS(T ≈ 2^64·K) ≤ 2^-128. Under a generic
  T/ε ≥ 2^λ notion this is λ ≈ 192 bits, not 128. Lattice attacks are believed not to trade
  time for tiny success probability gracefully, but that belief is itself heuristic. By contrast,
  SHA-384-as-QRO gives provable *generic* bounds inside the model: collisions O(t^3/2^384) ≈ 2^-192,
  preimages O(t^2/2^384).
- **[I] Assumption comparison:** both are unproven; SHA-384-as-QRO is an idealization of a heavily
  analysed, structure-free primitive; MSIS is a structured algebraic assumption whose concrete
  estimates move with cryptanalysis (estimator revisions, dual-attack debates for LWE, quantum-sieve
  exponent improvements). A lattice wrap **adds** an assumption (MSIS; LWE too if LMS22-style
  collapsing were used) on top of the QRO, so the system is no longer "hash-only". Unusual SNARK
  parameter regimes (large norm bounds approaching √q or q, l2 vs l∞, d = 64 rings, q ≈ 2^32/2^64,
  per-level ranks) get much less cryptanalysis than ML-KEM/ML-DSA parameters.
- **[P] Chen 2024 (eprint 2024/555):** claimed a poly-time quantum algorithm for LWE with polynomial
  modulus-to-noise ratio (⇒ GapSVP/SIVP at ~Õ(n^4.5) approx). A bug in Step 9 was found by Hongxun Wu
  and independently Thomas Vidick; on 2024-04-18/19 the author stated the claim does not hold. No
  replacement attack. [I] Lesson for SNARKs: such an attack would have hit large-approximation-factor
  regimes first — exactly where lattice SNARK MSIS instances (large β/q) sit — not ML-KEM.

---

## Q4. Formalization

- **[P]** No machine-checked proof (Lean/Coq/Isabelle/EasyCrypt) of soundness for any lattice SNARK
  (LaBRADOR, Greyhound, LatticeFold, Neo…) or of an MSIS-based Ajtai commitment's binding in a SNARK
  context was found.
- **Adjacent work [P]:** EasyCrypt Dilithium (Barbosa et al., CRYPTO'23, 2023/246): mechanized **ROM**
  proof; the formalization effort *found a gap* in the CMA→NMA step of existing ROM and QROM
  Fiat–Shamir-with-aborts proofs (QROM fix on paper only). EasyCrypt ML-KEM/Kyber proofs (Almeida
  et al., CRYPTO'23/'24; ROM). EasyPQC (CCS'21) adds some quantum reasoning to EasyCrypt. MPC-in-the-head
  ZK in EasyCrypt (arXiv 2104.05516; non-lattice). Lean: **ArkLib** + VCV-io (Verified-zkEVM):
  IORs, sumcheck, rbr knowledge soundness, FS/BCS, FRI/STIR/WHIR in progress — classical oracle model,
  no QROM, no lattices.
- **[I]** A Lean formalization of a lattice wrap would require building, from scratch: QROM machinery
  (compressed oracle / measure-and-reprogram), quantum rewinding (absent even on paper for LaBRADOR),
  module-lattice algebra (cyclotomic rings, operator norms, invertibility of challenge differences),
  and the JL-projection probability bound. The hash-only path (CMS19-style BCS for the STARK) is far
  closer to ArkLib's existing scope.

---

## Bottom line [I]
Under the contract "proven QROM bounds only", a LaBRADOR/Greyhound/LatticeFold/Neo-family final wrap
**cannot currently be certified**: (a) no QROM FS theorem exists for these multi-round lattice
arguments (DFM20's generic loss is 2^{~130·n}); (b) even their *interactive* post-quantum knowledge
soundness is unproven (LMS22 covers only simpler Bulletproofs, under LWE); (c) their per-round errors
(~2^-128) miss even the classical-ROM requirement (2^-192) and a hypothetical CMS-style QROM
requirement (~2^-256); (d) MSIS concrete security is heuristic and, for our failure-probability
regime, arguably needs ~192-bit estimates. Exact-witness extraction *is* achievable by design
(LaBRADOR §6 binary trick), so (Q2) is not the blocker; (Q1) and (Q3) are. Adopting a lattice wrap
would require either relaxing the contract to "conjectured/heuristic FS security" for the wrap layer
or a new research result (QROM FS for computationally special-sound multi-round arguments with
round-independent loss, plus a quantum-rewinding extractor).
