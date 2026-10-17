# Adversarial review of ANALYSIS.md (reviewer agent, 2026-10-17)

I found no fatal flaw in Lemmas 1, 2, Corollary 3, Lemma 5 or the core of Theorem 4. There are several fixable gaps. Two headline claims are overstated: that CMS19 Thm 8.6 proves 41 B directly, and that 26 B is backed by a credible hypothesis (it needs H-rob(strong)).

I checked the proof steps against the fetched sources: CFHL21 Lemma 4.1, Cor 4.2, Lemma 4.3 with Fig. 1 and eq. (8); CMS19 Defs 8.3/8.4, Thm 8.6, Lemma 4.9, Lemma 5.13 and §8.5.1/§8.6. I also grepped CY21a and CY21b for the quoted claims. I reran the numbers through the `calc/wb_bound.py` and `calc/cap_cost.py` functions using drivers in the scratchpad, with `python3 -I`. No repo files were modified; I did not run the scripts' main blocks, because `wb_bound.py` main writes `wb_bound.json`.

## Answers to your checks

1. **Frobenius / operator-norm through cO: valid.** For a fixed x, both projectors are diagonal and cO_{xŷ} ⊗ I keeps the rest of the database fixed. So the operator is block-diagonal over (x, ŷ, rest of database), and its norm is the largest block norm. Lemma 1's entries match CFHL Fig. 1: the ⊥ row and column entries have size 1/√M, γ_{⊥,⊥} = 0, and off-diagonal entries are ≤ 3/M. Cases (a), (b), (c) and the "Chg" consequence all check out. Taking the maximum over point types (narrow / wide / FS) is also legitimate.
2. **Does κ move only by the claimed amounts? Yes.** At narrow points κ moves by at most ±1, including:
   * inversions, which turn a default block into chosen content and cost one unit;
   * a lexicographic re-route when r is already an output at that position (case (ii));
   * un-recording (going from a value back to ⊥), which Lemma 1(b) charges.

   Two small proof cases are missing but trivial: block b already collided (F unchanged), and b leaving the collided set (impossible, since the new value can only add reached nodes). Wide points allow any jump, at negligible cost. FS points are monotone.
3. **Lemma 2's recursion: correct.** It needs only the triangle inequality and ‖Π_{=i}ψ‖ ≤ a_s(i), so non-commutation with cO doesn't matter. The induction and the binomial identity C(s,m) + C(s,m−1) = C(s+1,m) check out.
4. **Claim W: holds, given fixes 3 and 4 below.**
5. **Claim F: correct.** ε_rob puts ∃T inside the probability, so the adversary choosing T after the challenge is covered. Robustness of the prefix through a prover move follows from CMS19 Def 8.3 item 2. Uniqueness of the new transcript needs fix 2 below.
6. **Fact A with ℓ points: fine.** The points must be pairwise distinct, and with mixed output sizes the error term is Σ 1/M_i ≤ ℓ/N_min (Lemma 4.1's proof gives this). It's worth stating that once.
7. **Numbers: all reproduce.** Every §6 cell matches. So do the net-saving table, the Corollary 3 table, the per-block-loss table (within 0.1) and the K=0 bounds (n = 320/324/328 give −124.7/−128.7/−132.7). ε̂ for the final shape at B=256 runs −268, −246.7, −228.7, …
8. **41 B from CMS19: the arithmetic is right, the citation isn't** (item 10 below).

## Issues

| # | Sev. | Location | Problem | Fix |
|---|---|---|---|---|
| 1 | fixable (wrong as written) | §4, robust level F, l.246–247: "Prefixes with no oracle have F = +∞" | A prefix with no oracle has τ_T = τ for every T, so the formula gives F = −1 if state(τ) = 1. With the stated rule, κ misses a lucky challenge at an oracle-free verifier move. Claim F step 4 (F(τ) ≥ L, so F(τ′) ≥ L) then fails at the next round. | Drop the rule and use the formula: +∞ only when doomed. |
| 2 | fixable | wide-bad def l.235–237 and Claim F step 3, l.290–292 | "Unique chain prefix" needs: no FS output equals σ₀. Otherwise σ₀ can be reached at two depths and one FS point creates two transcripts. The bad-σ set guards new entries, but D₋ₓ is arbitrary in the static analysis. | Add "σ₀ ∈ Out_fs" to wide-bad (or put the round index in the FS input). If wide-bad means collisions across wide positions, Claim W′'s Chg must use outputs over the whole wide region (still ≤ t). |
| 3 | fixable | positions p = (i, ℓ, j), l.110; Claim W step 5, l.258–259 | If a round commits several trees (e.g. batched polynomials), they share positions. One excess entry at p can then put blocks of two trees into Coll, breaking \|Coll\| ≤ e(D). | Positions = (round, oracle index, level, index), and say so in the U-7 amendment. |
| 4 | fixable (spec) | Claim W steps 3–5 | If the verifier opens the same leaf twice (repeated i.i.d. query, or separate paths), a collided node lets the two openings disagree. Then no single block string, and no single τ_T, explains the accepted run, so "accepting implies state(τ_T) = 1" fails. | Require the verifier to deduplicate leaf indices or reject inconsistent repeats. Add this to the spec impact in §7. |
| 5 | cosmetic/fixable | Claim F, l.287 and l.293 | Lemma 1(a) bounds 10·Pr_r[κ_r ≥ j] without conditioning on κ_⊥ = i, but step 4 assumes κ_⊥ = i. The case κ_⊥ < i is covered by Lemma 1(c) plus Γ being non-increasing in d, but it isn't argued. | Add the two lines. |
| 6 | cosmetic | Corollary 3 step 3, l.202 | With κ = min(k, e), κ_r ∈ {κ_⊥, κ_⊥+1}, so a jump of 2 can't happen and G_{i,i+2} = 0. The (3t/N)^j terms are harmless but unnecessary. | Note G₂ = 0 there. |
| 7 | cosmetic | §0 l.28, "Hard floor ≈ 203 bits, set by 3·log t + log(10e²) − 2 log K + 128/(K+1)" | That expression decreases forever in K. With ε̂ set to 2^−1000, the script gives n_min = 201/196/191/187 at Kmax = 12/20/40/80. The floor comes from ε̂(K) growing (H-rob), not from the formula. main_table also has n = 202 entries. | Reword: the floor depends on H-rob. |
| 8 | cosmetic | §0 "n ≈ 205–221"; §5 "≈ 2.6–3.0 KB per tree at c=10" | The tables contain 203/204 (e.g. 4×60, B = 2¹⁰). cap_cost gives 2.33 KB at q=40, c=10. | Fix ranges to 203–221 and 2.3–3.0 KB. |
| 9 | fixable (affects headline) | §5 H-rob(strong), l.356–357; §6 "strong" columns | "A independent of T with density α at the proven radius" is very likely false. Modifying m blocks can bring f within reach of any codeword at distance ≤ δ (+ m/B), so A must cover the union of their agreement sets. That needs at least the shift and, beyond unique decoding, a list-size factor. Even H-rob(shift) as computed (density α + m/B) leaves out that factor. | Treat the strong columns as not credible. Headline the shift column: 28 B at c=8, 27 B at c=9, 26 B at c≥10; net ≈ 35–38 KB. Add a log₂\|L\| term to ε_rob(m≥1). I expect that to cost about 1–3 bits of n. |
| 10 | fixable (overclaim) | §0 l.26, §6 l.402, §7(1): "41 B proven by CMS19 Thm 8.6 constants" | CMS19's constants are explicit: ω*_D ≤ 6(t²ε + 4t³/2^λ), lifting with factor 6, Lemma 4.9 with constant 1. They give λ ≥ 324.6, so 41 B is numerically right. But Thm 8.6 is for CMS19's own construction: one oracle h: {0,1}^{2λ} → {0,1}^λ, so FS state, roots and the verifier's randomness m_j = h(σ_{j−1}, "j") are each λ bits. WHIR query rounds need far more than 328 bits of randomness per round. CMS19's hash chain also differs from (σ, c) = H(σ, msg), and §8.6 says other chains need a stronger rbr notion. Thm 8.6 does not apply verbatim. | Say "CMS19 §8.5.1 proof, adapted to [H-M] long challenges and mixed output widths". The fully written route is Theorem 4 with K=0, which is itself [T] and [H-M]-dependent. |
| 11 | cosmetic | §1.2, CY21b quote | Actual text: "we leave it for future work to adapt these technique to our construction". | Quote verbatim. |
| 12 | caution | Lemma 5 / H-rob scope | T may include blocks of earlier oracles chosen after later challenges. In WHIR, a block of f_{i−1} modified after the query step changes the constraint values for f_i, so "A depends only on τ" is a strong demand. Multi-tree query steps (same index in several trees) aren't modelled. | Make both explicit parts of H-rob. |

## Verdicts

* **Lemma 1:** correct.
* **Lemma 2:** correct.
* **Corollary 3:** correct and conservative; the numbers reproduce.
* **Theorem 4:** I found no break. The potential argument handles inversions, re-routing and un-recording properly, and the static compressed-oracle view removes time-ordering worries. It needs fixes 1–4, which are definitional or spec requirements and don't change any bound, plus fix 5 written out. After those I'd rate it plausible but still unreviewed. The spots most worth formalizing are the extraction (lexicographic tie-break, default strings) and the case analysis in Claim M.
* **Lemma 5:** correct as an abstract statement. Applying it to WHIR is H-rob, which is open, and the strong variant is doubtful (item 9).
* **26–28 B:** conditional on H-rob(shift) at best, so realistically 27–28 B at c=8–9. "26 B" leans on H-rob(strong) or c ≥ 10.
* **41 B:** the arithmetic is correct. It is proven by Theorem 4 (K=0) or by an adaptation of CMS19's proof, under [H-M], not by CMS19 Thm 8.6 as stated. Fix the citation before quoting it under U-2.
