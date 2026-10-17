# Weak-binding Merkle digests in the QROM: what is proven, what digest width it buys

Date 2026-10-17. Lane WB (`lane/pq-weak-binding`). Research and proof only; no code changes.

Tags:
* **[P]** proven in the cited source, with a statement that matches how it is used here.
* **[T]** theorem or lemma proven *in this note*. The proof is complete as written, but it has not been
  peer-reviewed or formalized.
* **[H]** hypothesis. Stated precisely, not proven.
* **[I]** inference or calculation.

Scripts are in `calc/` (stdlib Python only):
* `wb_bound.py` evaluates Theorem 4 and finds the minimal digest width n.
* `cap_cost.py` computes the bytes for the block structure.
* `net_saving.py` combines the two.
* `main_table.txt` and `shift_table.txt` are their outputs.

Contract: U-2 (proven bounds only), U-6 (failure ≤ 2⁻¹²⁸ against t ≤ 2⁶⁴ quantum queries), U-7 (SHA-384,
with truncation under discussion).

## 0. Verdict

> **Update 2026-10-17 (HROB.md and REVIEW-1.md).** The H-rob question is now settled.
> * **The shift variant is the headline.** H-rob(strong) is not credible (REVIEW-1 item 9), so the "strong"
>   columns of §6 are superseded.
> * **H-rob fails for WHIR as built**, both Construction 5.1 and OpenVM v2.0.1. The y-values of the
>   shift queries enter the γ-combination without being absorbed first. A QROM attack with success
>   ≈ t²/2ⁿ (HROB §2) forces n ≥ 256 for that transcript order.
> * **H-rob(shift) is proven [T] for WHIR-Y**, which absorbs the query answers before γ. That costs 0 proof
>   bytes (HROB Theorem R). The radius shift costs a few queries.
> * **Under the proven statement:** 26 B at block level c = 11 (K = 7, queries 70/70/57/48), net
>   **39.4 KB** against 42 B with exact byte counts. Alternatively 28 B at c = 10 (37.5 KB).
> * REVIEW-1 fixes 1–5 are applied below: the F formula, σ₀ in wide-bad, oracle index in positions,
>   deduplicated openings, and the κ_⊥ < i case of Claim F.
> * The table that follows is the original verdict, kept for the record. Where it disagrees with
>   HROB.md, HROB.md wins.

| question | answer |
|---|---|
| Is QROM soundness of BCS/Fiat–Shamir with weakly binding Merkle trees published anywhere (2019–2026)? | **No.** The state of the art is CMS19 Thm 8.6: O(t²ε + t³/2^λ), which needs collision-free databases. CY21a/CY21b do weak binding in the *classical* ROM only and leave the QROM open. |
| Smallest digest width proven today (U-2), using only WHIR's ordinary round-by-round (rbr) soundness, which the current 42-B plan already needs | **41 B (n ≥ 324 bits).** Proven by CMS19's explicit constants and, independently, by Theorem 4 here with K = 0 (constant 10 instead of 24). This saves **≈ 3 KB** against 42 B. |
| Smallest width with tolerated equivocation, *proven here* [T] but **conditional on H-rob** (block-robust rbr soundness of WHIR) | **26–28 B** (n ≈ 205–221 bits; table in §6). Blocks are level-8 to level-10 subtrees, and the tree levels above the blocks use full 48-B digests. Net final-layer saving ≈ **35–41 KB** against 42 B, after paying ≈ 4–12 KB for the wide top levels. |
| Hard floor of this method | ≈ 203 bits (26 B), set by 3·log t + log(10e²) − 2 log K + 128/(K+1). |
| Which of the three L4-B lemmas are closed? | **L1 (collision counting): closed [T]** (Corollary 3). Inversions need no counting lemma, because the potential method in Theorem 4 absorbs them. **L2 (multi-round FS with state restoration and weak binding): closed [T]** (Theorem 4). **L3 (robust WHIR query soundness): closed [T] only for the abstract query step** (Lemma 5). The step from WHIR's actual state function to the block-robust form (fold, OOD and sumcheck steps; the query-step agreement set) is **open [H]**. |
| What U-2 admits *now* | **41 B.** 26–28 B needs (i) H-rob proven for WHIR, (ii) review or formalization of Theorem 4, and (iii) a U-7 amendment: position-indexed truncated nodes, untruncated top levels and Fiat–Shamir (FS) chain. |

## 1. Literature check (2019–2026)

Sources fetched (archive copies in the lane scratchpad): CMS19 (ePrint 2019/834), CY21a (2021/188),
CY21b (2021/281), CFHL21 (2020/1305), BGTZ23 (2023/1256), Faisal (2023/421), Liu–Zhandry (arXiv 1811.05385),
and Hamoudi–Magniez (arXiv 2002.08944v5). Abstracts only for Chiesa–Hu (2026/2099) and the SoK (2026/1367).

### 1.1 Quantum (multi-)collision finding

* **[P] BHT98 and Zhandry (compressed oracle, CRYPTO 2019; ePrint 2018/276).** Finding one collision with t
  queries succeeds with probability Θ(t³/2ⁿ). The compressed oracle gives a perfect purification of the
  random oracle in which the oracle's "database" D can be measured as an analysis device.
* **[P] Liu–Zhandry, "On finding quantum multi-collisions" (EC 2019).**
  * Finding one k-collision (k inputs, one output) needs Θ(N^{½(1−1/(2^k−1))}) queries, for constant k and
    constants that depend on k.
  * The proof bounds amplitudes on databases that hold r (k−1)-collisions and s k-collisions.
  * As stated, it is an algorithmic bound for constant k and is not directly usable for counting "how
    many collisions does the database contain".
* **[P] Hamoudi–Magniez (TQC 2021).**
  * Thm 4.5: finding K *disjoint* collision pairs succeeds with probability ≤ O(T³/(K²N))^K.
  * More useful here, **Prop 4.3 is database-level**: in the recording model, ‖Π_{≥k}|φ_t⟩‖ ≤ C(t,k)·(4√(t/N))^k,
    where Π_{≥k} projects onto databases with ≥ k disjoint collisions.
  * This is the closest published form of L1 for collisions. Corollary 3 below is the same idea with a
    different count (position-wise *excess*, where a k-wise collision counts k−1, matching CY's "collision
    score") and constant √10.
* **[P] CFHL21 (Chung–Fehr–Huang–Liao, EC 2021).**
  * A framework that reduces quantum query bounds to classical "transition capacities".
  * Lemma 4.3 gives the explicit one-point matrix of the compressed oracle, used in Lemma 1 below.
  * Cor 4.2 (Zhandry) links the real oracle to the measured database.
  * Thm 5.29: collision probability ≤ O(t³/N).
* **Inversions.** No published QROM bound counts *inversions* (outputs that hit an earlier input). CY21a's
  inversion score (Lemma 2.4.2, ≤ (2t²/2^λ)^k/k!) is a classical query-trace argument. "Inversion" depends on
  query order, so it is not a property of the compressed database. This is why L1 was listed as open.
  **Theorem 4 avoids needing it** (§4).

### 1.2 BCS/Fiat–Shamir in the QROM, and weak binding

* **[P] CMS19, Thm 8.6.**
  * Statement: BCS on an IOP with rbr soundness ε is sound against t-query quantum attackers with error
    O(t²ε + t³/2^λ).
  * The proof (§8.5.1) gives ω*_D ≤ 6(t²ε + 4t³/2^λ). It uses the lifting lemma ω*_D ≤ 6t²·(I(P|Q̄) + I(Q)) with
    I(P|P̄_col) < ε + (2t+1)/2^λ and I(P_col) < t/2^λ.
  * It then applies √ω*_O ≤ √ω*_D + √(q log ℓ/2^λ).
  * This is a **zero-tolerance** analysis: one database collision, or one "y ∈ S(D)" event (an inversion of
    any stored chunk), counts as a loss. Both cost t·t²/2^λ.
  * It is the source of today's "n ≥ 3·64 + 128 + c" rule, and t³ is tight for one *untargeted* bad event
    (BHT, multi-target Grover).
* **[P] CY21a, tight Micali (TCC 2021), classical ROM.**
  * Error t·ε_PCP + C·t/2^λ with C ≤ 12·l·log|Σ|, for λ ≥ 2 log t + 6.
  * Ingredients: per-node domain separation, a tree game with collision and inversion budgets, and
    "reverse soundness".
  * Open items stated there: IOPs/BCS and adaptive soundness. The QROM is not treated.
* **[P] CY21b, subquadratic SNARGs (CRYPTO 2021), classical ROM.**
  * Construction: a Merkle *cap* (the tree chopped at level i*), a "permuted robust" PCP, and a cap
    soundness game.
  * Quote: "we leave it for future work to adapt [CMS19] to our construction."
  * Theorem 4 below is, in effect, that adaptation for multi-round BCS. Our cap blocks are CY's blocks, and
    WHIR's uniform queries replace CY's random permutation.
* **[P] BGTZ23 (2023/1256), Faisal (2023/421), Chiesa–Hu (2026/2099), "Quantum rewinding for IOP-based
  succinct arguments" (arXiv 2411.05360), SoK 2026/1367.**
  * None proves BCS/FS soundness in the QROM with weakly binding commitments.
  * BGTZ23 restates CMS19's t³/2^λ term.
  * 2411.05360 is about interactive (Kilian) arguments.
  * Chiesa–Hu build extractable vector commitments for quantum states. Their abstract does not mention weak
    binding.
* **Search result.** No 2021–2026 work found that analyses QROM BCS with "somewhat binding" Merkle
  commitments. Searched: ePrint and arXiv for CY follow-ups, "collisions and inversions", QROM BCS, weak or
  relaxed binding, WHIR/STIR analyses. The question is open in the literature. §3–§5 give a solution modulo H-rob.

## 2. Model

* **Oracles (domain-separated, modelled as independent random oracles).**
  * *Narrow Merkle* positions, output {0,1}ⁿ (truncated SHA-384), N := 2ⁿ.
  * *Wide* positions, output {0,1}³⁸⁴: the top tree levels and the FS chain.
  * *FS steps* x = (σ_{r−1}, msg_r) ↦ (σ_r, c_r). Here σ_r ∈ {0,1}³⁸⁴ and c_r is that round's full challenge,
    including any PoW bits, from one call to an extendable-output oracle.
  * **[H-M]** One-call challenges are a modelling assumption. Today's 268-bit/42-B analysis already makes it.
* **Positions.**
  * A Merkle node of IOP round i, oracle (tree) index o, level ℓ, index j, has position p = (i, o, ℓ, j).
    The position is part of the hashed input ("position-indexed", as in CY). The oracle index is needed
    when one round commits several trees (REVIEW-1 item 3); otherwise one excess entry could put blocks
    of two trees into Coll and break |Coll| ≤ e(D) in Claim W.
  * **Deduplicated openings (spec requirement, REVIEW-1 item 4).** The verifier opens each leaf index of
    a tree at most once per proof: it deduplicates repeated query indices, or rejects a proof whose
    repeated openings of one index disagree. Without this, a collided node lets two openings of one leaf
    disagree, and no single τ_T explains the accepted run (Claim W step 4).
  * A narrow node input is (p, v_L, v_R) with v_L, v_R ∈ {0,1}ⁿ. A leaf input is (p, data).
  * **Blocks.** For a block level c, the 2^c subtrees rooted at level c are round i's *blocks*. All
    positions at level ≥ c are narrow. Positions at levels < c are wide ("wide top"). The variant that
    puts the 2^c block roots directly into msg_r (a "cap") behaves identically in the proof.
  * Leaves are WHIR folding cosets, so a block is a union of cosets.
* **Transcripts and the rbr state function.**
  * state is a state function of the IOP in the CMS19 Def 8.3 sense. A **block modification** τ_T of a
    transcript τ replaces the oracle strings on the leaves of the blocks in T by arbitrary values.
  * "Doomed" means state = 0.
* **Compressed oracle notation (CFHL21 §4).**
  * D = database; Ȳ = Y ∪ {⊥}; D|^x = databases that agree with D off x.
  * cO_{xŷ} acts on register x only. ψ_s = adversary-plus-database state after s queries, supported on |D| ≤ s.
  * Π_S = projector onto databases with property S (diagonal).

**Definition (block-robust rbr error) [this note].**
* For m ≥ 0, ε_rob(m) is the supremum, over x ∉ L, over prefixes τ at a verifier move, and over block sets C
  such that *every* τ_T with C ⊆ T and |T| ≤ m is doomed, of
  Pr_c[ ∃ T ⊇ C, |T| ≤ m : state(τ_T ‖ c) = 1 ].
* ε_rob(0) = ε_rbr is ordinary rbr soundness. Write ε̂(m) := max_{m' ≤ m} ε_rob(m').
* With z bits of PoW, the bad set is also intersected with "PoW holds", which multiplies the bound by
  2^{-z} (the PoW bits are independent output bits).

## 3. Tools

**Fact A [P] (Zhandry; CFHL21 Cor 4.2).**
* If A outputs points x₁..x_ℓ and claimed values y₁..y_ℓ, let p be the probability that y = H(x) and
  (x, y) ∈ R in the real model.
* Let p' be the probability that y = D(x) and (x, y) ∈ R for the measured compressed database.
* Then √p ≤ √p' + √(ℓ/N_min).

**Fact B [P] (CFHL21 Lemma 4.3).**
* For ŷ ≠ 0, the one-point unitary cO_{xŷ} on C^{Ȳ} has entries γ_{⊥,⊥} = 0, |γ_{⊥,r}| = |γ_{u,⊥}| = 1/√M
  (for u, r ∈ Y), and |γ_{u,r}| ≤ 3/M for u ≠ r in Y. Here M = |Y|.
* For ŷ = 0 it is the identity.

**Lemma 1 (one-query transition bound) [T].**
Fix a point x with output alphabet of size M, a database D₋ₓ that is undefined at x, and ŷ. Let
κ: databases → ℤ, κ_r := κ(D₋ₓ[x↦r]) for r ∈ Ȳ, and for i < j let A := {r : κ_r ≥ j}, B := {r : κ_r = i}
(disjoint). Then:

(a) if ⊥ ∉ A: ‖A·cO_{xŷ}·B‖² ≤ 10|A ∩ Y|/M;
(b) if ⊥ ∈ A: ‖A·cO_{xŷ}·B‖² ≤ 10|B|/M;
(c) if ⊥ ∉ A ∪ B: ‖A·cO_{xŷ}·B‖² ≤ 9|A||B|/M².

Consequently:
* If there is a set Chg ⊆ Y with κ_r = κ_⊥ for all r ∉ Chg, then ‖A cO B‖² ≤ 10|Chg|/M.
* If κ_r ≥ κ_⊥ for all r, then (a) applies whenever B ≠ ∅.

*Proof.*
1. Bound the operator norm by the Frobenius norm: ‖A cO B‖² ≤ Σ_{u∈A, r∈B} |γ_{u,r}|².
2. Case (a). Each u ∈ A is in Y. The entry γ_{u,⊥} contributes 1/M (only if ⊥ ∈ B). Each r ∈ B ∩ Y
   contributes ≤ 9/M², and |B ∩ Y| ≤ M. Total ≤ |A|(1/M + 9/M) = 10|A|/M. This is CFHL21 eq. (8).
3. Case (b). Then ⊥ ∉ B. Each r ∈ B gets 1/M from u = ⊥ and ≤ 9|A ∩ Y|/M² ≤ 9/M from the rest.
4. Case (c). Every term is ≤ 9/M².
5. Consequences. Since A ∩ B = ∅, at most one of A, B contains values r with κ_r = κ_⊥. That one may contain
   ⊥; the other set lies inside Chg. Apply (a) or (b) accordingly. Monotonicity rules out ⊥ ∈ A with B ≠ ∅. ∎

The full query operator acts as Σ_{x,ŷ} |x,ŷ⟩⟨x,ŷ| ⊗ cO_{xŷ}, and cO_{xŷ} changes only register x of D. So
for diagonal Π, ‖Π_{≥j} cO Π_{=i} P_{≤s}‖ is the maximum over (x, ŷ, D₋ₓ with |D₋ₓ| ≤ s) of the
block norms in Lemma 1.

**Lemma 2 (path lemma) [T].**
*Statement.*
* Let κ take values in {0, …, K+1} with κ(∅) = 0. Let ψ_s be the state after s queries of any t-query
  adversary run against the compressed oracle.
* Suppose that for all s < t and 0 ≤ i < j ≤ K+1, ‖Π_{κ≥j} cO Π_{κ=i} P_{|D|≤s}‖ ≤ G_{i,j}.
* Then ‖Π_{κ≥K+1} ψ_t‖ ≤ A_t := Σ_{m≥1} C(t,m)·W_m, where W_m = Σ over chains 0 = i₀ < i₁ < … < i_m = K+1 of
  ∏_k G_{i_{k−1}, i_k}.

*Proof.*
1. Let a_s(j) := ‖Π_{≥j}ψ_s‖. The adversary's unitaries do not act on D, so they commute with Π.
2. Write ψ_s = Π_{≥j}ψ_s + Σ_{i<j} Π_{=i}ψ_s. Then
   a_{s+1}(j) = ‖Π_{≥j} cO ψ_s‖ ≤ a_s(j) + Σ_{i<j} G_{i,j} ‖Π_{=i}ψ_s‖ ≤ a_s(j) + Σ_{i<j} G_{i,j} a_s(i).
   Here a_s(0) ≤ 1, a_0(j) = 0 for j ≥ 1, and Π_{=i}ψ_s = Π_{=i}P_{≤s}ψ_s.
3. Let Â_s(j) := Σ_m C(s,m)·W_m(j), where W_m(j) is the chain sum ending at j and W_0(0) = 1.
4. Â satisfies the recursion with equality: Σ_{i<j} G_{i,j} Â_s(i) = Σ_m C(s,m−1) W_m(j), and
   C(s,m) + C(s,m−1) = C(s+1,m).
5. By induction, a_s ≤ Â_s. ∎

**Corollary 3 (L1 for collisions: database collision excess) [T].**
*Statement.*
* Let e(D) := Σ_p (|D_p| − |Im D_p|) be the position-wise excess over the narrow positions. A k-wise
  collision at one position counts k−1.
* After t queries, the measured database satisfies Pr[e(D) ≥ k] ≤ (Σ_{j=0}^{⌊k/2⌋} C(t,k−j)·C(k−j,j)·
  (10t/N)^{(k−2j)/2}·(3t/N)^j)².
* In our range this equals C(t,k)²(10t/N)^k·(1 + 2^{−50}) ≤ (10e²t³/(k²N))^k.

*Proof.*
1. Take κ = min(k, e).
2. For a narrow point x at position p, assigning r ∉ Out_p(D₋ₓ) leaves e unchanged, and |Out_p| ≤ |D₋ₓ| ≤ t.
   Also κ_r ∈ {κ_⊥, κ_⊥+1}.
3. So G_{i,i+1}² ≤ 10t/N by Lemma 1, and G_{i,i+2} ≤ 3t/N by Lemma 1(c), from moves between two non-⊥ values.
   Larger jumps are 0. Wide and FS points do not change e.
4. Apply Lemma 2. ∎

Numbers [I] at t = 2⁶⁴: log₂ Pr[e ≥ k] for k = 1, 2, 3, 4, 6, 8:

| n | k = 1 | 2 | 3 | 4 | 6 | 8 |
|---|---:|---:|---:|---:|---:|---:|
| 208 | −12.7 | −27.4 | −43.2 | −59.9 | −95.1 | −132.0 |
| 224 | −28.7 | −59.4 | −91.2 | −123.9 | −191.1 | −260.0 |
| 336 | −140.7 | −283.4 | −427.2 | −571.9 | −863.1 | −1156 |

At 26 B, collisions *happen* (about 2⁻¹³). The question is only what each one buys the adversary.

## 4. Theorem 4: QROM soundness of BCS with tolerated equivocation (L2) [T]

**Setting.**
* BCS compilation of a public-coin IOP with the oracles, positions, blocks and FS chain of §2.
* An adversary makes ≤ t queries and outputs a proof. The verifier evaluates ℓ oracle points.
* x ∉ L. The cap K ≥ 0 is a free parameter.

**Statement.** Pr[verifier accepts] ≤ (A_t + √(ℓ/N))², where A_t is the chain sum of Lemma 2 with
G_{i,j} = G_{j−i} and

* G₁ = max(√(10t/N), Γ(1)),
* G₂ = max(3t/N, Γ(2)),
* G_d = Γ(d) for d ≥ 3,
* Γ(d) := √(10·(2^{−z}·ε̂(K+1−d) + (2t+1)/2³⁸⁴)).

Optimise over K. With K = 0 this is the zero-tolerance bound ≈ 10t²·max(t/N, ε_rbr), proven by this note
with ordinary rbr only. That gives the 41-B row of §0.

**Definitions used in the proof.**
* *Transcripts in D.* σ-chains in D_fs that start at σ₀ and end at an FS entry, with the challenges
  c_1..c_r and the messages they contain. If D_fs or the wide region has a collision, **or σ₀ ∈ Out_fs**
  (some FS output equals the initial state; REVIEW-1 item 2), set κ := K+1 ("wide-bad"). Without the σ₀
  clause, σ₀ could be reached at two depths and one FS point could create two transcripts (Claim F step
  3). Collisions are counted across the whole wide region, so Claim W′'s Chg is the set of outputs over
  the whole wide region plus Chunk_p, still of size ≤ t + 1.
* *Canonical extraction.* For round i, block b, and the block-root value v named by the (wide or cap) parent
  of transcript τ, extract top-down from narrow entries at the matching positions.
  * At each reached node value at position p, take the lexicographically smallest preimage at p with that
    output.
  * Leaf data of the reached leaves form the block string. Unreached or undefined nodes give a fixed
    default string.
  * A reached node is *collided* if it has ≥ 2 preimages at p. Coll(τ) is the set of blocks of τ's
    oracles that contain a reached collided node.
* *Robust level.* F(τ) := max{ m ≥ −1 : every τ_T with Coll(τ) ⊆ T and |T| ≤ m is doomed }. This is
  vacuous for m < |Coll(τ)|, so F ≥ |Coll(τ)| − 1. F(τ) = +∞ exactly when every admissible τ_T is
  doomed for every m. For a prefix with no oracle, τ_T = τ for all T, so the formula gives F = +∞ if
  state(τ) = 0 and F = −1 if state(τ) = 1. (An earlier draft set F = +∞ for every oracle-free prefix;
  that was wrong, REVIEW-1 item 1: it misses a lucky challenge at an oracle-free verifier move.)
* *Potential.* κ(D) := min(K+1, max_τ (K − F(τ))⁺ + e(D)) when D is not wide-bad. The max over the empty
  set is 0. So κ(∅) = 0.

**Claim W (acceptance implies κ = K+1).**
1. By Fact A, it suffices to bound Pr[the measured D contains an accepting proof consistent with D].
2. Take its transcript τ (FS consistency puts its chain in D_fs).
3. In every block b ∉ Coll(τ), every opened path runs from the block-root value down through reached nodes
   with unique preimages. So the opened leaves equal the canonical string.
4. Blocks where an opening deviates contain a reached collided node: the first node where the opened
   preimage differs from the canonical one. So the accepted transcript is τ_T with T = Coll(τ).
5. Accepting means state = 1, so F(τ) ≤ |Coll(τ)| − 1 ≤ e(D) − 1. The second inequality holds because each
   block of Coll holds its own excess entry, and positions are per block.
6. Hence (K − F)⁺ + e ≥ K + 1.

**Claim M (narrow points).** For a narrow x at position p in block b of round i, let
Chg := Out_p(D₋ₓ) ∪ Chunk_p(D₋ₓ). Chunk_p is the child chunk at p of entries at the parent position, or of
the cap or wide entries that feed b. Then |Chg| ≤ |D₋ₓ| ≤ t, because these are images of disjoint entry sets.
* (i) If r ∉ Chg, x is unreached and creates no collision, so κ_r = κ_⊥.
* (ii) If r ∈ Out_p, then e grows by 1. Every τ that reaches value r at p already had it reached through
  its old preimage, so b joins or stays in Coll(τ).
  * Contents of blocks in T ⊇ Coll are irrelevant, so F_new ≥ F_old.
  * F_new ≤ F_old + 1: a witness set T₀ ∌ b for F_old extends to T₀ ∪ {b}.
  * Every τ that does not reach r is unchanged. So κ_r − κ_⊥ ∈ {0, 1}.
* (iii) If r ∈ Chunk_p \ Out_p, e is unchanged and only block b's extraction changes for each τ, because the
  subtree under p lies in b.
  * If b ∉ Coll before and after: for T ⊇ Coll with |T| ≤ F_old − 1, the new τ_T is an old τ_{T∪{b}}, so
    F_new ≥ F_old − 1. Symmetrically F_old ≥ F_new − 1.
  * If b enters Coll: as in (ii), F_new ∈ [F_old, F_old + 1]. So κ_r − κ_⊥ ∈ {−1, 0, 1}.
* So κ_r ∈ {κ_⊥−1, κ_⊥, κ_⊥+1}. Lemma 1 gives G_{i,i+1}² ≤ 10t/N. Lemma 1(c) gives G_{i,i+2} ≤ 3t/N, since
  both A and B ⊆ Chg and ⊥ ∉ A ∪ B. Jumps ≥ 3 are impossible.

**Claim W′ (wide points).**
* Chg := Out_p ∪ Chunk_p, of size ≤ t, out of 2³⁸⁴ values. Outside Chg the point is unreached and creates no
  collision, so κ_r = κ_⊥.
* Any jump is allowed, but G² ≤ 10t/2³⁸⁴ by Lemma 1.

**Claim F (FS points).**
1. *Monotonicity.* For x = (σ_prev, msg), κ_r ≥ κ_⊥ for all r. Adding an FS entry only adds transcripts or a
   σ-collision. It changes neither e nor any existing F. So Lemma 1(a) applies, and it suffices to bound
   Pr_r[κ_r ≥ j | κ_⊥ = i].
   *The other values of κ_⊥ (REVIEW-1 item 5).* Take A = {r : κ_r ≥ j} and B = {r : κ_r = i}, with i < j.
   * If κ_⊥ ≥ j, monotonicity gives B = ∅, so the block norm is 0.
   * If κ_⊥ = i, then ⊥ ∈ B and Lemma 1(a) gives ‖A cO B‖² ≤ 10·Pr_r[κ_r ≥ j].
   * If i' := κ_⊥ < i, then ⊥ ∉ A ∪ B and Lemma 1(c) gives ‖A cO B‖² ≤ 9|A|/M = 9·Pr_r[κ_r ≥ j]. Steps
     2–5 below, run with i' in place of i, bound this by (9/10)·Γ(j − i')². Γ is non-increasing in its
     argument, because ε̂ is non-decreasing, so the bound is ≤ Γ(j − i)².
2. *Bad σ.* Let r = (σ, c). If σ ∈ Out_fs ∪ PrevState(D_fs) ∪ {σ₀}, a set of size ≤ 2t+1, anything may
   happen. That has probability ≤ (2t+1)/2³⁸⁴.
3. *Otherwise exactly one new transcript appears*, or none if σ_prev is not reachable. It is τ′‖c with
   τ′ = τ‖msg, where τ is the unique chain prefix ending at σ_prev. Uniqueness holds because D is not
   wide-bad.
4. *Robustness of the prefix.* From κ_⊥ = i we get F(τ) ≥ L := K − i + e. Prover moves preserve doom, so
   F(τ′) ≥ L. Proof: for T ⊇ Coll(τ′) with |T| ≤ L, the restriction T ∩ old ⊇ Coll(τ) and τ_{T∩old} is doomed.
5. *Bounding the new transcript.* κ_r ≥ j requires F(τ′‖c) ≤ K − j + e. That is, there is a T ⊇ Coll(τ′)
   with |T| ≤ m := K − j + e + 1 and state(τ′_T ‖ c) = 1.
   * Since m ≤ L, every τ′_T with T ⊇ Coll and |T| ≤ m is doomed.
   * The definition of ε_rob with C = Coll(τ′) then bounds the probability by 2^{−z}ε_rob(m).
   * Since e ≤ i, m ≤ K + 1 − (j − i), so the bound is ≤ 2^{−z}ε̂(K+1−(j−i)). Hence G_{i,j} ≤ Γ(j−i).

**Conclusion.** Each query point is of exactly one type, so G_{i,j} is the maximum of the type bounds.
Lemma 2 gives ‖Π_{κ=K+1}ψ_t‖ ≤ A_t. Claim W and Fact A finish the proof. ∎

**What the proof does *not* need.**
* No count of inversions. An inversion is just a transition of κ, charged by Lemma 1 at |Chg|/N, at most
  t/N per query.
* No reverse-soundness argument.
* No assumption on tree depth or proof length. Depth does not appear: a block event gives the adversary a
  whole block, whatever its size.
* State restoration and Grover appear only as the C(t,m)·(√·)^m amplitude sums.

## 5. Block-robust query soundness (L3) and the "e out of q" question

**Lemma 5 (abstract query step) [T].**
*Hypothesis on the state function.* A verifier move draws q i.i.d. uniform leaves of a round oracle split
into B equal blocks. For every robustly doomed prefix (with forced set C, at level m), the event
state(τ_T ‖ c) = 1 implies every queried leaf lies in A ∪ leaves(T). Here A is a leaf set of density ≤ α
that depends only on τ.

*Conclusion.*
ε_q(m) ≤ Σ_{k=0}^{q} C(q,k)·α^{q−k}·min((1−α)^k, C(B,m)·(m/B)^k).

*Proof.*
1. Condition on which k queries miss A. Their positions are i.i.d. uniform on A^c.
2. They are covered by some m blocks either trivially (k ≤ m, probability ≤ 1), or with probability
   ≤ C(B,m)·(m/(B(1−α)))^k by a union bound over T.
3. Multiply by α^{q−k}(1−α)^k and sum over k. ∎

**Answer to (b), "equivocating e leaves".**
* Suppose the adversary can equivocate e *queried* leaves after seeing the queries. This is the leaf-level
  limit B = number of leaves.
* Lemma 5 gives ε_q(e) ≈ C(q,e)·α^{q−e}. The loss is e·b + log₂ C(q,e) bits out of q·b, where b = log₂(1/α).
* So the adversary gains the e/q fraction of the query bits, plus log₂ C(q,e) bits for choosing which
  queries.
* A Merkle event, however, equivocates a whole block. For block density 1/B comparable to α (b ≈ 4–6 bits,
  so α ≈ 1/16–1/64), the block loss is ≈ q·log₂(1 + 2^b/B) + log₂ B. Measured values (`wb_bound.py eps`) for
  the first equivocated block:

| q, b | B = 64 | 256 | 1024 |
|---|---:|---:|---:|
| 50, 5.36 | 41.8 bits | 18.7 | 12.6 |
| 60, 4.47 | 31.7 | 15.2 | 11.3 |
| 46, 5.83 (final round, 12k) | 48.1 | 21.3 | 13.4 |

  Each event costs the adversary about log₂(N/(10e²t³)) ≈ n − 198 bits of probability. So the tolerance
  pays once n − 198 exceeds the per-block loss. This is the whole mechanism.
* **This is why the cap must be larger than q.** At B = 64 ≈ q, one block costs 30–48 bits and the method
  barely helps. The "free cap at level log q" of L4-B §2.5 is too coarse.
* Blocks of 2⁸–2¹⁰ need either a large cap or (better) **untruncated 48-B digests for the top c levels**.
  `cap_cost.py`: wide top levels cost ≈ 1.0 KB per tree at c = 8 and ≈ 2.6–3.0 KB per tree at c = 10, for
  q = 40–69. A sent cap is always more expensive.

**[H-rob]: resolved in HROB.md.** It is false for WHIR as built (§2 there). It is proven [T] in its shift form for WHIR-Y (Theorem R), where the query-move bound is N(m)·(1−δ)^q instead of Lemma 5. The original statement follows.

**[H-rob] (open): WHIR is block-robust.** Lemma 5's hypothesis must hold for WHIR's shift-query step, and
the non-query moves (sumcheck/folding randomness, OOD samples, combination randomness) must have small
ε_rob(m). Two variants:
* **H-rob(strong).** A does not depend on T, with density α = 2^{−b} at the round's proven radius. The other
  moves' ε_rob ≤ 2^{−300}.
* **H-rob(shift), the conservative variant.** The modification T moves the list-decoding picture by ≤ m/B in
  relative distance.
  * Blocks are unions of folding cosets, so fold_c(f^T) = fold_c(f)^T. The proximity gap applied at radius
    δ − m/B then covers the fold steps.
  * The query step then has A with density ≤ α + m/B. This is computed as `--shift`.
  * It needs the round radii to keep WHIR's proven (Johnson-regime) rbr analysis valid on
    [δ − (K+1)/B, δ].

Neither variant is proven. WHIR's own rbr theorem is a prerequisite that the current 42-B plan also has.

## 6. Concrete minimal digest width (c)

Settings:
* t = 2⁶⁴, failure ≤ 2⁻¹²⁸, ℓ = 2¹⁷ verifier hash points.
* Per-round rbr target 268 bits, or 236 bits plus z = 32 PoW.
* α = 2^{−target/q}. The best K is chosen per row.
* Depth (20–31) and path count (≈ 5,000) enter only through ℓ, which is negligible.

Minimal n in bits; the byte width (n/8 rounded up) is in parentheses.

| shape (queries per round) | zero tolerance (K = 0) | B = 2⁸, strong | B = 2⁸, shift | B = 2¹⁰, strong | B = 2¹⁰, shift | B = 2¹², shift |
|---|---:|---:|---:|---:|---:|---:|
| 4 × 40 | 324 (41) | 217 (28) | 230 (29) | 207 (26) | 211 (27) | 206 (26) |
| 4 × 50 | 324 (41) | 209 (27) | 218 (28) | 204 (26) | 207 (26) | 204 (26) |
| 4 × 60 | 324 (41) | 206 (26) | 212 (27) | 203 (26) | 205 (26) | 203 (26) |
| final 12k today: 69/69/55/46 | 324 (41) | 212 (27) | 221 (28) | 205 (26) | 208 (26) | 205 (26) |
| final 12k levers: 61/61/49/41, z = 32 | 324 (41) | 210 (27) | 218 (28) | 205 (26) | 207 (26) | 204 (26) |

**Net final-layer saving against 42 B** at 3 KB per digest byte, minus the wide-top bytes over the four
WHIR trees (`net_saving.py`), for the final 12k shape:

| c (B = 2^c) | strong: D, net | shift: D, net |
|---|---|---|
| 7 | 28 B, 40.4 KB | 30 B, 34.6 KB |
| 8 | 27 B, 40.8 KB | 28 B, 38.0 KB |
| 9 | 26 B, 39.9 KB | 27 B, 37.3 KB |
| 10 | 26 B, 35.5 KB | 26 B, 35.5 KB |
| 12 | 26 B, 25.7 KB | 26 B, 25.7 KB |

The optimum is c = 8–9: **27–28 B, net ≈ 37–41 KB**. The levers shape gives the same numbers within
1 KB. Against 48 B the gross saving is 18 KB larger.

Calibration:
* The zero-tolerance row gives n ≥ 324, from 10·t³/2ⁿ ≤ 2⁻¹²⁸.
* CMS19's constants give n ≥ 192 + log₂ 24 + 128 ≈ 325. Both round to **41 B**.
* The 42-B rule (t³/2ⁿ ≤ 2⁻¹⁴⁴) carries about 12 bits of unused margin.

## 7. Verdict (d)

1. **Proven now, under U-2 and on the same dependencies as today's 42-B plan** (WHIR rbr; one-call XOF
   challenges):
   * n = 324 bits suffices; byte-aligned this is **41 B** (328 bits, failure ≤ 2^{−132.7} from the Merkle
     term).
   * Sources: CMS19 Thm 8.6 with its explicit constants, and Theorem 4 with K = 0.
   * Saving against 42 B: **≈ 3 KB.**
   * 40 B (320 bits) is *not* provable this way: 10t³/2³²⁰ = 2^{−124.7}.
2. **Proven in this note [T], conditional on H-rob:**
   * Theorem 4 plus Lemma 5 give **26–28 B** (n = 205–221) with blocks of 2⁸–2¹⁰ leaves and wide top levels.
   * Net **≈ 35–41 KB** under the final layer.
   * This is the CY21b mechanism carried to the QROM and to multi-round BCS with state restoration.
3. **Still conjectured or open:**
   * (i) **H-rob for WHIR** (§5). This is the one real mathematical gap. The query step is done abstractly;
     the fold, OOD and sumcheck steps and the exact form of the query-step agreement set are not.
   * (ii) Independent review, and ideally Lean formalization, of Lemmas 1–2, Corollary 3 and Theorem 4. The
     proofs are complete as written but new.
   * (iii) The uncapped CY21a-style route (≈ 36 B), which needs quantum reverse soundness. It is not derived
     here and is dominated by (2).
4. **Spec impact, if (3)(i)–(ii) close.** U-7 would change as follows. Only the proof technique changes; no
   new assumption class is added.
   * Merkle node inputs carry (round, oracle index, level, index).
   * The verifier deduplicates repeated leaf openings, or rejects inconsistent repeats (§2).
   * **The WHIR transcript absorbs each round's query answers before the combination challenge γ.** This
     is the WHIR-Y change of HROB.md §3. Without it, the protocol is attackable at any n < 256
     (HROB.md §2).
   * Narrow digests of n ≥ 221 bits (28 B) below level c = 8, and full 384-bit digests above.
   * The FS chain state σ stays at 384 bits.
   * Per the standing rule, this needs a user decision before adoption.
5. **Recommendation.**
   * Amend U-7 to **41 B** now (proven, −3 KB).
   * Open a WHIR task for **H-rob(shift)**: a block-robust rbr theorem with the radius-shift argument of §5.
     It would unlock 28 B (−38 KB).
   * Put Theorem 4 up for review or formalization in parallel. It is self-contained: compressed oracle, one
     potential function, Frobenius bounds.

## 8. Caveats

* The FS challenge is modelled as one random-oracle output per round ([H-M]). With counter-mode expansion
  over several SHA-384 calls, the "last call" transition needs a per-group rbr argument. This applies
  equally to today's analysis.
* The truncated-SHA-384 narrow, wide and FS oracles are modelled as independent random oracles through
  domain separation. This is standard, and as in CMS19 and CY.
* Theorem 4 bounds *soundness*. Knowledge soundness and extraction for recursion are not addressed. CMS19
  §8.5.2 handles extraction in the zero-tolerance case only.
* All numbers use a fixed per-round target (268 bits, or 236 + 32 PoW). They do not re-optimise WHIR
  parameters for the shifted radius required by H-rob(shift). That may cost a few extra queries, which this
  note does not model.
