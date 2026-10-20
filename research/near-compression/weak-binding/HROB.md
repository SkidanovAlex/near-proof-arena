# H-rob for WHIR: block-robust round-by-round soundness

Date 2026-10-17. Lane WB (`lane/pq-weak-binding`). This note picks up from ANALYSIS.md, which leaves H-rob open
in §5, and from REVIEW-1.md (items 9 and 12). It is research and proof only. The one calculator added is
`calc/hrob.py`; its output is in `calc/hrob_table.txt`.

Tags, as in ANALYSIS.md:
* **[P]** proven in the cited source.
* **[T]** proven in this note. The proof is complete as written, but it has not been reviewed.
* **[H]** hypothesis.
* **[I]** calculation.

Sources:
* WHIR, ePrint 2024/1586: Construction 5.1, Theorem 5.2 and its proof, Thm 4.3 (Johnson bound).
* BCGM, ePrint 2025/2051: Def. 3.14 (MCA) and Thm 9.2 / Def. 9.1, which is MCA up to
  1 − (1 + 1/2M)√ρ with error (M + ½)⁷·d·n² / (3ρ^{3/2}·|F|).
* The OpenVM stark-backend v2.0.1 verifier, `crates/stark-backend/src/verifier/whir.rs`, at commit
  d667af5 in the local cargo checkout.

## 0. Verdict

| question | answer |
|---|---|
| Does H-rob (strong or shift) hold for WHIR **as specified (WHIR Construction 5.1) and as implemented in OpenVM v2.0.1**? | **No, and no state function can rescue it.** §2 gives a concrete QROM attack on the BCS-compiled protocol with weakly binding narrow digests. It succeeds with probability ≈ t²/2ⁿ, so it breaks the 2⁻¹²⁸ target for every n < 256 (≈ 32 B). Where it fails: the **combination step**. The shift-query answers y_{i,j} enter one field equation, with coefficients γ_i^{j+1}, and γ_i is sampled **without absorbing the y_{i,j}**. One equivocated leaf of the previous oracle, at one queried coset, chosen after γ_i, solves that equation. So for WHIR's own state function ε_rob(1) ≥ 1 − 1/\|F\| at that move (Prop. 2.2). OpenVM also folds the final round's point checks into the same γ combination, so the final round is affected too. |
| Sound replacement | **WHIR-Y: absorb each round's query answers y_{i,1..t} into the Fiat–Shamir transcript before sampling γ_i** (§3). It adds **0 proof bytes**. In the compiled proof the y's are recomputed from the openings the proof already carries. The verifier absorbs about 239 × 48 B ≈ 11.5 KB more, which is roughly 90 extra SHA-384 compressions out of about 10k. The protocol needs a one-line change in prover and verifier (`observe_ext(yi)` before `sample_ext()` for γ). |
| H-rob(shift) for WHIR-Y? | **Proven [T]** as Theorem R (§4), with explicit ε_rob(m) for every verifier move. The radius shift lands where ANALYSIS predicted: the fold, OOD and combination moves need list decoding and MCA at radius δ_i + m/B_i, uniformly over all modifications, so **no union bound over T appears in them**. Only the query moves pay a union over T: a factor N(m) = Σ_{j≤m} C(B, j), plus, in variant L, a Johnson list-size factor (REVIEW-1 item 9). To keep MCA valid the round radius must drop to δ_i = J_M(ρ_i) − K/B_i, and that costs extra queries. |
| Minimal digest width under the proven statement (today's final-12k shape: M = 8, 268 bits, no PoW) | **26 B (n = 208)** with block level c = 11, robustness cap K = 7 and queries 70/70/57/48 instead of 69/69/55/46. **Net saving 39.4 KB** of WHIR opening bytes against 42-B digests, computed exactly (351,870 → 312,428 B; failure bound 2^{−131.4} at n = 208). Other points: 28 B at c = 10 (37.5 KB) and 30 B at c = 9 (34.3 KB). |
| Other shapes (same theorem) | Contract multiplicity M = 3: 27 B at c = 11, net 39.1 KB. Levers shape (236 bits + 32 PoW): 26 B at c = 12, net 34.8 KB. |
| What binds | **Not** the robust WHIR errors. Over the whole search ε̂(m) stays ≤ 2^{−268+≈10m} (it costs about c bits per block), and n_min equals the value at ε̂ ≡ 0. The digest width is set by Theorem 4's collision chain for the chosen K (K = 7 ⇒ n = 208). K, in turn, is capped by the query cost of the radius shift K/B_i, which is worst at the rate-2⁻¹² round, where √ρ = 1/64. |
| Residual assumptions (§6) | (1) Theorem 4 and this note are unreviewed [T]. (2) [H-M], one-call challenges, as in today's plan. (3) The **interface hypothesis [H-outer]**: the PIOP before WHIR (GKR / zerocheck / stacking) is rbr-sound in "list-state" form with list radius δ_0 + K/B_0. Lemma 4.7 makes this automatic for any PIOP whose state reads the committed oracles only through that list; it has to be checked against OpenVM's actual reduction. (4) Implementation conformance: OpenVM's `binary_k_fold` is WHIR's Fold (pointwise invertible even/odd split), and query indices are i.i.d. uniform. (5) The ANALYSIS spec items: position = (round, oracle, level, index), deduplicated openings, wide top levels, and wide FS chain. |

**One-line answer: H-rob fails for WHIR as built, and is proven with one modification (WHIR-Y). Under the
proven statement the minimal digest is 26 B at c = 11, which saves 39.4 KB against 42 B.** This is
conditional on review of Theorem 4 and this note, and on [H-outer].

## 1. Setting and notation

**Oracles and blocks.**
* Use OpenVM's round indexing. Round i (0 ≤ i < M) works on oracle f_i : L_i → F:
  * k_i sumcheck rounds fold f_i;
  * then the prover commits f_{i+1}, or sends the final polynomial p := f_M if i = M − 1;
  * OOD sampling follows (not in the final round);
  * then t_i shift queries on f_i;
  * finally the combination challenge γ_i.
* m_i is the variable count, ρ_i = 2^{m_i}/|L_i| the rate, and L_i^{(s)} the image of L_i under x ↦ x^{2^s}.
* The leaves of f_i's Merkle tree are the fibres of x ↦ x^{2^{k_i}}.
* The **blocks** of f_i are B_i = 2^{c_i} equal-size unions of leaves (the level-c_i subtrees).
* f_0 is virtual: f_0 = Σ_c μ^c F_c over the stacked column oracles F_c, which may come from several trees.
  * All those trees share the index set, the depth and the block partition.
  * An "index block" b of f_0 is modified if T contains block b of a tree whose μ-coefficient vector is
    non-zero.
* For a block set T, let U_j(T) ⊆ L_j be the union of the modified blocks of oracle j, and
  μ_j(T) := |U_j(T)|/|L_j| ≤ |T|/B_j.
* U_j^{(s)}(T) is its image in L_j^{(s)}. It has the same relative density, because blocks are unions of
  fibres.

**Modified transcripts.**
* τ_T^v is τ with the oracle strings on U(T) replaced by values v.
* Non-oracle messages (ĥ, y's, p, the claims) are unchanged.
* Everything the verifier derives from oracles is recomputed from τ_T^v.
* ANALYSIS's "τ_T" ranges over all v.

**Robust doom.**
* H(τ, C, m) := ∀ T ⊇ C, |T| ≤ m, ∀ v: S(τ_T^v) = 0.
* The block-robust error of a verifier move is
  ε_rob(m) := sup over (τ, C) with H(τ, C, m) of Pr_c[∃ T ⊇ C, |T| ≤ m, ∃ v : S(τ_T^v ‖ c) = 1].
  This is ANALYSIS §2 with the quantifier over contents written out.
* ∃T and ∃v sit **inside** the probability. That models the adversary choosing which blocks to
  equivocate, and their contents, after seeing c (REVIEW-1 item 12).

**Lists.**
* Λ(C, f, r) is the set of codewords at relative distance ≤ r.
* Λ_T(C, f, r) := {u ∈ C : |{x ∉ U(T) : u(x) ≠ f(x)}| ≤ r|L|}.
* ℓ_j(r) is the Johnson bound for rate ρ_j: 1/(2ε√ρ_j) at r = 1 − √ρ_j − ε [P, WHIR Thm 4.3].
  * It holds for the folded codes RS^{(j,s)} (same rate) and for interleaved codes [P, WHIR Thm 4.4].
* J_M(ρ) := 1 − (1 + 1/2M)√ρ.
* err⋆_d(r) is BCGM's MCA error for a degree-d univariate generator at radius r ≤ J_{M'}(ρ), with
  M' ≥ 3 [P, BCGM Thm 9.2].

**Lemma 1.1 (lists of modified words) [T].** ⋃_v Λ(C, f^{T,v}, r) = Λ_T(C, f, r) ⊆ Λ(C, f, r + μ(T)).

*Proof.* Both inclusions are immediate. Take u ∈ Λ_T and set v := u on U(T); then u ∈ Λ(C, f^{T,v}, r). ∎

**Lemma 1.2 (fold commutes with block modification) [T].** WHIR's Fold has three properties:
* Fold(f, α)(y) depends only on f restricted to the fibre over y;
* it is linear in those values;
* it maps constant fibres to the same constant: Fold(f,α)(x²) = (f(x)+f(−x))/2 + α(f(x)−f(−x))/(2x),
  iterated.

Then, for s ≤ k_j and α ∈ F^s:
* (i) Fold(f^{T,v}, α) = Fold(f, α) outside U_j^{(s)}(T).
* (ii) For every w on U_j^{(s)}(T) there is a v with Fold(f^{T,v}, α) = w on U_j^{(s)}(T).
* (ii) also holds for f_0 = Σ μ^c F_c, with U_0 the set of effectively modified index blocks.

*Proof.*
* (i) Blocks are unions of fibres.
* (ii) On each fibre the fold is a linear functional whose coefficients sum to 1, so it is non-zero and
  hence surjective. Choose the fibre values independently per fibre.
* For f_0, a modified block of tree c with a non-zero coefficient vector moves f_0 on that block through
  a non-zero linear map. ∎

## 2. Where H-rob fails: the combination step

OpenVM's verifier, `whir.rs` lines 165–254, does the following in each round:
1. It samples query indices.
2. It recomputes y_i = binary_k_fold(opened values) from the Merkle-verified openings.
3. It then calls `transcript.sample_ext()` for γ **without observing any y_i**.
4. It adds claim += γ·y₀ + Σ γ^{j+1} y_j.
5. In the final round it adds the same γ-combination instead of checking final_poly(z_j) = y_j pointwise.

WHIR Construction 5.1 has the same order, with z_{i,j} and γ_i in one verifier message.

**Proposition 2.1 (attack) [T].**
* Setting: the BCS compilation of the protocol above with n-bit narrow Merkle outputs, and any false
  evaluation claim.
* Claim: there is a quantum adversary with O(t) oracle queries that makes the verifier accept with
  probability ≥ c₀·min(1, t²/2ⁿ) − O(1/|F|), where c₀ is an absolute constant.

*Proof.*
1. **Honest setup with one offset.** Commit honest codewords of some f̂. The claim σ₀ is false. In the
   first sumcheck round send ĥ = ĥ^{hon} + e₀/2, a constant shift, so that Σ_{b∈{0,1}} ĥ(b) = σ₀. Keep
   adding the running offset e_s/2 in each later round. The sumcheck checks pass, and after round 0 the
   claimed σ_{0,k} differs from the honest value by e := e_{k₀} ≠ 0.
2. **Honest middle.** Send the honest f₁ and an honest OOD answer.
3. **Read the challenges.** Receive the queries z_{0,j} and γ₀. The honest answers give
   σ_{1,0} − σ_{1,0}^{hon} = e.
4. **The only change.** The adversary needs one opened coset of f₀, at query j*, whose fold equals
   y_{j*} − e/γ₀^{j*+1}. Then σ_{1,0} = σ_{1,0}^{hon}, and every later message is honest and accepted.
5. **Finding that opening.** Such openings are tuples of row values satisfying one affine equation, a
   set of size ≫ 2ⁿ. The adversary needs one whose leaf digest equals the committed digest at that leaf
   position.
   * Each tuple has an independent uniform n-bit digest.
   * Grover/BBHT search with t queries therefore finds one with probability Θ(min(1, t²/2ⁿ)) [P, BBHT98;
     Zalka].
   * The search runs after γ₀ is known, which the protocol allows.
   * Probability 1/|F| covers γ₀ = 0. ∎

At t = 2⁶⁴, 2⁻¹²⁸ needs n ≥ 256 − log c₀.

**Consequences.**
* For the protocol as built, no digest narrower than ≈ 32 B is sound.
* The proven 41 B (ANALYSIS §7.1) stands.
* No state function satisfies H-rob with ε̂(K) small enough to give n < 256. Theorem 4 would otherwise
  contradict Prop. 2.1. Without position indexing there are more targets, and the attack only gets
  easier.

**Proposition 2.2 (WHIR's own state function) [T].**
* Setting: WHIR's Theorem 5.2 state function, at the shift/combination move.
* Claim: there is a prefix τ that is robustly doomed at level 1 (and higher) such that
  Pr_{z,γ}[∃ T, |T| = 1, ∃ v : State(τ_T^v ‖ (z, γ)) = 1] ≥ 1 − 1/|F|.

*Proof.*
1. Use the prefix of Prop. 2.1's adversary.
2. **Doomed at level 1.** For any one modified block, g₀^{T,v} is within 1/B < δ₀ of the honest
   codeword c. It is farther than 1 − ρ − 1/B > δ₀ from every other codeword, so its list is {c}. c fails
   the constraint by the offset e. Hence State = 0 for all T with |T| = 1.
3. **Revived after the challenge.** After (z, γ), take T = {the block of f₀ containing z_{0,j*}}, with v
   solving the equation as in Prop. 2.1. Then the honest f₁ lies in CCRS^{(1,0)}. ∎

The failure is exactly REVIEW-1's item 12. In Lemma 5's language: one queried leaf in leaves(T) is
enough, not "every queried leaf in A ∪ leaves(T)".

## 3. WHIR-Y and its state function

**Protocol change (WHIR-Y).**
* In round i, after the query challenge z_{i,1..t_i} and before γ_i, the prover sends
  y_{i,j} := Fold(f_i, α_i)(z_{i,j}) for every j, as non-oracle messages absorbed into the FS chain.
* The decision phase adds the point checks y_{i,j} = Fold(f_i, α_i)(z_{i,j}), read from f_i's openings.
* All sumcheck and final checks use the sent y's.
* In the compiled proof the y's are not transmitted. The verifier recomputes them from the openings and
  absorbs them, so this is a bijection between accepting compressed and uncompressed proofs.
* In the final round, (z, y, γ) is handled the same way, with p in place of f_{i+1}. Equivalently, the
  final round can check p(z_j) = y_j pointwise.

**Notation.**
* σ_{0,0} := Σ_c μ^c v_c (the stacking claims). σ_{i,s} := ĥ_{i,s}(α_{i,s}).
* σ_{i+1,0} := σ_{i,k_i} + γ_i y_{i+1,0} + Σ_j γ_i^{j+1} y_{i,j}. Every σ depends only on non-oracle
  messages and challenges.
* ŵ, CCRS^{(i,s)} = CRS[F, L_i^{(s)}, m_i − s, ŵ_{i,s}, σ_{i,s}] and RS^{(i,s)} are as in WHIR.
* g_i := Fold(f_i, α_i) on L_i^{(k_i)}, and f_{i,s} := Fold(f_i, α_{i,1..s}).
* For u ∈ RS^{(i+1,0)}, u(pow z) means û evaluated at pow(z). Its restriction to L_i^{(k_i)} is a codeword
  of RS^{(i,k_i)}, because m_{i+1} = m_i − k_i.

**Validity.** Val(τ) := SC(τ) ∧ Y(τ).
* SC: every sumcheck check derivable from τ holds. In WHIR-Y these checks involve no oracle values, so
  **SC(τ_T^v) = SC(τ)**.
* Y: every point check y_{i',j} = g_{i'}(z_{i',j}) present in τ holds.
* **Fact V.** At any prefix inside round i, before y_{i,·} are sent, Y involves only f_0..f_{i−1}.

**State function S^Y.** Fix radii δ_i, and OOD radii r_i^{ood} ∈ {δ_i (variant L), δ_i + K/B_i (variant U)}.
On a prefix ending with a prover message, S(τ‖a) := S(τ). The states after each verifier move:

| state | after | S = 1 iff |
|---|---|---|
| [Ent_i] | γ_{i−1} (or μ when i = 0) | Val ∧ Λ(CCRS^{(i,0)}, f_i, δ_i) ≠ ∅ |
| [Fold_{i,s}] | α_{i,s} | Val ∧ Λ(CCRS^{(i,s)}, f_{i,s}, δ_i) ≠ ∅ |
| [OOD_{i+1}] | z_{i+1,0} | (a) ∃ distinct u, u′ ∈ Λ(RS^{(i+1,0)}, f_{i+1}, r^{ood}_{i+1}) with û(pow z_{i+1,0}) = û′(pow z_{i+1,0}); or (b) [Fold_{i,k_i}] |
| [Qry_i] | z_{i,1..t} | Val ∧ ∃ u ∈ Λ(RS^{(i+1,0)}, f_{i+1}, δ_{i+1}) with (Q1) u\|_{L_i^{(k)}} ∈ CCRS^{(i,k_i)}, (Q2) û(pow z_{i+1,0}) = y_{i+1,0}, (Q3) ∀j: û(pow z_{i,j}) = g_i(z_{i,j}). In the final round u = p, without (Q2). |
| [Ent_{i+1}] | γ_i | Val ∧ Λ(CCRS^{(i+1,0)}, f_{i+1}, δ_{i+1}) ≠ ∅. In the final round: Val ∧ p ∈ CCRS^{(M,0)} |

**Checking the state-function axioms.**
* *Full transcripts.* Accepting means Val holds (all sumcheck and point checks pass) and the final
  constraint holds, i.e. state = 1. This is the property Claim W of Theorem 4 needs, on the extracted
  τ_T.
* *Prover moves* preserve doom by definition. Robust doom of τ‖a, including blocks of a new oracle a, is
  robust doom of τ. This is Claim F step 4.
* *The initial prefix* is §4.7.

## 4. Theorem R: block-robust rbr of WHIR-Y [T]

**Conditions.** For every round i, with 0 ≤ K and multiplicities M'_i ≥ 3:
* (F) δ_i + K/B_i ≤ J_{M'_i}(ρ_i).
* (O) r^{ood}_i + K/B_i < 1 − √ρ_i.

(F) implies (O) for variant L. Write r_i(m) := δ_i + m/B_i.

**Theorem R [T].** Assume (F), (O) and the interface hypothesis of §4.7. For every 0 ≤ m ≤ K, the
block-robust errors of WHIR-Y's verifier moves satisfy the following bounds. Here d ≤ 3 is the
sumcheck degree bound, t_i is the query count, and z is the round's PoW bits, which multiply the query
bounds by 2^{−z}.

| move | ε_rob(m) ≤ |
|---|---|
| fold α_{i,s} | err⋆_1(r_i(m)) + ℓ_i(r_i(m))·d/\|F\| |
| OOD z_{i+1,0} | C(ℓ_{i+1}(r^{ood}_{i+1} + m/B_{i+1}), 2)·2^{m_{i+1}}/\|F\| |
| queries z_{i,1..t} | Lfac·N_i(m)·(1 − δ_i)^{t_i}, where N_i(m) = Σ_{j≤m} C(B_i, j). Lfac = 1 if m = 0, in variant U, or in the final round, and Lfac = ℓ_{i+1}(r_{i+1}(m)) otherwise. The quantity N_i(m)·(1 − δ_i)^{t_i} may be replaced by Lemma 5 of ANALYSIS.md with α = 1 − δ_i. |
| combination γ_i | ℓ_{i+1}(r_{i+1}(m))·(t_i + 1)/\|F\| (final round: (t + 1)/\|F\|) |
| batching μ, outer PIOP | §4.7 |

At m = 0 these are WHIR's Theorem 5.2 errors, plus the trivially-zero error of the new prover message.

The proofs below take the moves one at a time. Each starts from H(τ, C, m) for the prefix τ before the
move. If SC(τ) fails, every τ_T^v‖c is invalid and the state stays 0. So each proof assumes SC(τ).

### 4.1 Fold move α_{i,s} (sumcheck/folding randomness)

The prefix ends with ĥ_{i,s}. Its state is [Fold_{i,s−1}], or [Ent_i] when s = 1. Let γ := r_i(m).

1. **The MCA event.** Write f_{i,s−1} as the pair (u₀, u₁) of its even and odd parts on L_i^{(s)}, so that
   Fold(f_{i,s−1}, α) = u₀ + α·u₁. The pair is an invertible pointwise transform of the 2-fibres. Let
   E_mca be the event that some S ⊆ L_i^{(s)} with |S| ≥ (1−γ)n has (u₀ + αu₁)|_S ∈ C|_S while u₀|_S or
   u₁|_S ∉ C|_S. Here C = RS^{(i,s)} and n = |L_i^{(s)}|. By (F), Pr[E_mca] ≤ err⋆_1(γ) [P, BCGM Thm 9.2
   with generator (1, α)].
2. **A witness gives a codeword c.** Suppose ¬E_mca, and that some (T, v) and w have
   Val(τ_T^v) ∧ w ∈ Λ(CCRS^{(i,s)}, Fold(f^{T,v}_{i,s−1}, α), δ_i). Let U := U_i^{(s)}(T) and
   S := {y ∉ U : w(y) = Fold(f_{i,s−1}, α)(y)}. By Lemma 1.2(i), outside U the modified fold equals the
   unmodified one.
   * So |L^{(s)} ∖ (S ∪ U)| ≤ δ_i n and |S| ≥ (1 − δ_i − m/B_i)n = (1 − γ)n.
   * By ¬E_mca there are codewords c₀, c₁ with c_j|_S = u_j|_S.
   * c₀ + αc₁ agrees with w on S, and |S| > ρn, so c₀ + αc₁ = w.
   * Let c ∈ RS^{(i,s−1)} be the codeword with even and odd parts (c₀, c₁). Then Fold(c, α) = w, and c
     agrees with f_{i,s−1} on every fibre over S.
   * So c ∈ Z₀ := Λ_b(RS^{(i,s−1)}, f_{i,s−1}, γ), a set fixed by τ with |Z₀| ≤ ℓ_i(γ).
3. **Robust doom forbids c.** Let v″ equal v on every oracle except f_i. On f_i's T-blocks, choose v″
   (Lemma 1.2(ii), applied to the first s−1 folds) so that f^{T,v″}_{i,s−1} = c on U^{(s−1)}.
   * Then f^{T,v″}_{i,s−1} disagrees with c only on fibres over L^{(s)} ∖ (S ∪ U), so
     c ∈ Λ(RS^{(i,s−1)}, f^{T,v″}_{i,s−1}, δ_i).
   * By Fact V, Val(τ_T^{v″}) = Val(τ_T^v) holds.
   * H(τ, C, m) at (T, v″) gives c ∉ CCRS^{(i,s−1)}.
4. **The sumcheck polynomial separates.** With p̂_c as in WHIR's Claim 5.3, step 3 gives
   Σ_{b∈{0,1}} p̂_c(b) ≠ σ_{i,s−1} = Σ_b ĥ_{i,s}(b), the last equality by SC(τ). So p̂_c ≢ ĥ_{i,s}.
   Meanwhile w = Fold(c, α) ∈ CCRS^{(i,s)} says p̂_c(α) = ĥ_{i,s}(α).
5. **Union over a fixed set.** The event is contained in E_mca ∪ {∃ c ∈ Z₁ : p̂_c(α) = ĥ_{i,s}(α)}, where
   Z₁ := {c ∈ Z₀ : p̂_c ≢ ĥ_{i,s}} is fixed before α. By Schwartz–Zippel this has probability
   ≤ err⋆_1(γ) + ℓ_i(γ)·d/|F|. ∎

**No union over T.** MCA quantifies over all agreement sets S, and the list Z₀ is taken at the shifted
radius once. So the adversary's choice of T after seeing α costs only the radius shift m/B_i. This is
step 2 of the task.

### 4.2 OOD move z_{i+1,0}

The prefix ends with the oracle f_{i+1}, so its state is [Fold_{i,k_i}] of the part before it.
1. H gives that (b) is false for every (T, v), and z_{i+1,0} changes neither Val nor any list.
2. So a flip needs (a) for some f^{T,v}_{i+1}: two distinct u, u′ ∈ Λ_T(f_{i+1}, r^{ood}). By Lemma 1.1
   both lie in Λ(f_{i+1}, r^{ood} + m/B_{i+1}), a fixed set whose size is finite by (O).
3. Two distinct multilinear û, û′ give distinct univariate polynomials û(pow X), û′(pow X) of degree
   < 2^{m_{i+1}}. A union bound over pairs gives the stated bound. ∎

### 4.3 Query move z_{i,1..t} (shift queries)

The prefix ends with y_{i+1,0}, so its state is [OOD_{i+1}]. H gives, for every (T, v), that (a) fails
for f^{T,v}_{i+1} and [Fold_{i,k}](τ_T^v) = 0.

1. **Candidates.** Let Y := {u ∈ Λ(RS^{(i+1,0)}, f_{i+1}, r_{i+1}(m)) : (Q1) ∧ (Q2)}. Y is fixed before
   the queries. By Lemma 1.1, every u that witnesses [Qry_i](τ_T^v ‖ z) = 1 lies in Y.
   * **Variant U:** |Y| ≤ 1. Since m ≤ K, Y ⊆ Λ(f_{i+1}, r^{ood}_{i+1}). H at (T, v) = (C, the original
     contents) says no two members of that list agree at pow z_{i+1,0}, and (Q2) pins û(pow z_{i+1,0}) to
     y_{i+1,0}.
   * **Variant L:** |Y| ≤ ℓ_{i+1}(r_{i+1}(m)), and |Y| ≤ 1 when m = 0 (then T = C = ∅ and r^{ood} = δ).
   * **Final round:** Y ⊆ {p}.
2. **Agreement sets.** For u ∈ Y let A_u := {z ∈ L_i^{(k)} : û(pow z) = g_i(z)}, using the unmodified g_i.
3. **Claim.** If (T, v) and u ∈ Λ(f^{T,v}_{i+1}, δ_{i+1}) witness the flip, then every z_j lies in
   A_u ∪ U_i^{(k)}(T), and dens(A_u ∪ U_i^{(k)}(T)) < 1 − δ_i.
   * The first part is (Q3) together with Lemma 1.2(i).
   * For the density, let v′ equal v except on f_i's T-blocks. There choose v′ so that g_i^{T,v′} = û∘pow
     on U_i^{(k)}(T), by Lemma 1.2(ii); for i = 0 this is the batched version.
   * By Fact V (the y_{i,·} are not yet in the transcript), Val(τ_T^{v′}) = Val(τ_T^v) holds.
   * H at (T, v′): (b) fails, so Λ(CCRS^{(i,k)}, g_i^{T,v′}, δ_i) = ∅.
   * û∘pow on L_i^{(k)} lies in CCRS^{(i,k)} by (Q1), so its distance from g_i^{T,v′} exceeds δ_i.
   * Their disagreement set is exactly L_i^{(k)} ∖ (A_u ∪ U_i^{(k)}(T)), which proves the claim.
4. **Union.** U_i^{(k)}(T) depends only on T's effective blocks of f_i (index blocks for f_0). So there
   are at most N_i(m) distinct such sets of ≤ m blocks. The z_j are i.i.d. uniform (OpenVM's
   `sample_bits`). Hence
   Pr ≤ Σ_{u∈Y} Σ_{T′} dens(A_u ∪ U(T′))^{t} ≤ |Y|·N_i(m)·(1 − δ_i)^{t_i}.
5. **Alternative.** Every contributing u has dens(A_u) < 1 − δ_i, so ANALYSIS Lemma 5 with α = 1 − δ_i
   also bounds the inner probability. ∎

On the task's questions:
* **The union over T appears only here.** It is paid once per query move, as N(m) ≈ B^m/m!: about c
  bits per block.
* It is **cheaper than the "strong" Lemma 5 numbers** (18.7 bits per block at B = 256). The robust
  hypothesis bounds A ∪ U(T) for every T, not just A, and the radius shift has been moved into δ_i
  through §4.1.
* **Multi-tree query steps** (the initial round opens the same index in every stacked tree) are covered.
  Equivocating any tree's block at an index only modifies f_0 on that index block. Union bounds count
  index blocks, so N_0(m) does not grow with the number of trees.

### 4.4 Combination move γ_i

The prefix ends with y_{i,·}, so its state is [Qry_i]. Every value of the prefix is fixed before γ_i.
1. **Candidates.** Let W := ⋃ Λ(RS^{(i+1,0)}, f^{T,v}_{i+1}, δ_{i+1}) over the valid (T, v); validity now
   includes Y_i: y_{i,j} = g_i^{T,v}(z_{i,j}). By Lemma 1.1, W ⊆ Λ(f_{i+1}, r_{i+1}(m)), and W is fixed
   before γ_i.
2. **Each candidate fails a fixed condition.** For u ∈ W, coming from (T, v), H says u fails (Q1), (Q2)
   or (Q3)(T, v). Under Y_i, (Q3)(T, v) is equivalent to (Q3′): û(pow z_{i,j}) = y_{i,j} for all j. So u
   fails one of (Q1), (Q2), (Q3′), and **none of these depends on (T, v)**.
3. **A non-zero polynomial in γ.** Since Σ_b û(b)·eq(pow z, b) = û(pow z), u ∈ CCRS^{(i+1,0)} holds iff
   P_u(γ_i) = 0, where
   P_u(γ) := [Σ_b ŵ_{i,k}(û(b), b) − σ_{i,k}] + γ·[û(pow z_{i+1,0}) − y_{i+1,0}] + Σ_j γ^{j+1}·[û(pow z_{i,j}) − y_{i,j}].
   P_u is a non-zero polynomial of degree ≤ t_i + 1.
4. **Union.** A union bound over W gives the stated bound. ∎

**This is where WHIR-Y is used.** In unmodified WHIR, (Q3) would read g_i^{T,v}(z_{i,j}). Its value is
chosen after γ_i, so the conditions are not fixed and Prop. 2.2 applies.

### 4.5 Final round

* The final query move is §4.3 with Y ⊆ {p}. p is a prover message, so it is not modifiable.
* The final combination is §4.4 with W ⊆ {p}.
* The final full-transcript state is the decision. ∎

### 4.6 Proof of Theorem R

1. Each verifier move of WHIR-Y is one of §4.1–4.5, or §4.7 for μ and the outer PIOP.
2. Each bound there holds for every (τ, C) with H(τ, C, m).
3. m ≤ K keeps every radius used within (F) and (O): r_i(m), r^{ood} + m/B, and r_{i+1}(m) in the list
   bounds.
4. ε_rob(m) is the supremum over moves. Theorem 4 uses ε̂(m) = max_{m′≤m} ε_rob(m′) only for m ≤ K
   (Claim F step 5 gives m ≤ K + 1 − (j − i) ≤ K). ∎

### 4.7 Interface: batching μ and the PIOP before WHIR

**Lemma 4.7 (list states) [T].**
* Setting: the committed column oracles are F = (F_1..F_W), with joint (interleaved) lists
  Λ^{W}(F, r). Suppose a verifier move's state has the form S(τ) = Val′(τ) ∧ ∃ c ∈ Λ^{W}(F, δ_0) with
  P(c, τ). Here Val′ and P read only non-oracle messages and challenges.
* Let ε_P := sup over (c, τ) with P(c, τ) = 0 of Pr_ch[P(c, τ‖ch) = 1].
* Claim: ε_rob(m) ≤ ℓ^{W}_0(δ_0 + m/B_0)·ε_P.

*Proof.* Lemma 1.1 for interleaved words puts every witness c in the fixed set
Λ^{W}(F, δ_0 + m/B_0). If c ∈ Λ_T, then setting v := c on U(T) and applying H gives P(c, τ) = 0. Take a
union bound over that set. ∎

**Lemma 4.8 (batching μ) [T].**
* Setting: the state before μ is S_pre := Val ∧ ∃ (c_1..c_W) ∈ Λ^{W}(F, δ_0) satisfying every stacking
  claim Σ_b ŵ_0(ĉ_c(b), b) = v_c, where ŵ_0 = Z·(weight) is linear in Z. The state after μ is [Ent_0].
* Claim: ε_rob(m) ≤ err⋆_{W−1}(δ_0 + m/B_0) + ℓ^{W}_0(δ_0 + m/B_0)·(W − 1)/|F|.

*Proof.* This is the proof of §4.1 with the generator (1, μ, …, μ^{W−1}), which is BCGM Thm 9.2 with
d = W − 1.
1. MCA turns a witness w into a tuple (c_c) jointly agreeing with F off U(T), with Σ μ^c c_c = w.
2. Setting v″ := (c_c) on the modified blocks and applying H shows some claim fails.
3. Then Σ_c μ^c (Σ_b ŵ_0(ĉ_c(b), b) − v_c) is a non-zero polynomial of degree ≤ W − 1 in μ that vanishes
   iff w meets the batched constraint. ∎

**[H-outer] (interface).**
* Statement: the PIOP before WHIR (GKR, zerocheck and the stacking reduction in stark-backend v2) has a
  state function of the form in Lemma 4.7, with list radius δ_0 + K/B_0, ending in S_pre.
* What then follows: its robust errors are its ordinary per-u errors times ℓ^{W}_0(δ_0 + K/B_0). Since
  |F| ≈ 2^{371}, that factor is negligible. The initial prefix is doomed for every first message when
  x ∉ L, as in WHIR §7.
* Status: this is the standard "list-decoding compiler" shape, and Lemma 4.7 then makes robustness
  automatic. It is still a hypothesis only because this note has not re-derived OpenVM's outer protocol.

## 5. Numbers (`calc/hrob.py`, output `calc/hrob_table.txt`)

**Model.**
* Shape: final-12k, from `levers_model.py`, with b = 8, k₁ = 1, k = 3, h = 2¹⁹:
  * rates 2^{−8, −8, −10, −12};
  * |L_j| = 2^{27..24};
  * depths 26/23/22/21;
  * leaf bytes 1,760 / 384 / 384 / 384.
* Radius: δ_j = J_M(ρ_j) − K/B_j (variant U: also ≤ 1 − √ρ − 2K/B − √ρ/64).
* Queries: q_j = ⌈target / −log₂(1 − δ_j)⌉. The search also allowed extra queries; none helped.
* ε_rob(m) is the Theorem R maximum; the fold MCA error uses the least M′ ≤ 64.
* Theorem 4 is evaluated with t = 2⁶⁴, ℓ = 2¹⁷ and failure ≤ 2⁻¹²⁸.
* Bytes are computed exactly: leaves plus expected multiproof siblings, at D bytes on levels ≥ c and
  48 B on levels < c.
* The baseline is today's shape with 42-B digests, which reproduces the 3,932-digest count.
* Optimised over c (uniform, plus mixed per tree) and over K ≤ 20.

**Final-12k today (M = 8, 268 bits)**, baseline 351,870 B. Results for variant L; variant U is never
better here.

| c (B = 2^c) | K* | queries | n_min | D | net saving vs 42 B |
|---|---:|---|---:|---:|---:|
| 6 | 0 | 69/69/55/46 | 324 | 41 B | 3.8 KB |
| 8 | 2 | 72/72/59/51 | 237 | 30 B | 27.2 KB |
| 9 | 2 | 70/70/57/48 | 237 | 30 B | 34.3 KB |
| 10 | 4 | 70/70/57/48 | 219 | 28 B | 37.5 KB |
| **11** | **7** | **70/70/57/48** | **208** | **26 B** | **39.4 KB** |
| 12 | 5 | 69/69/56/47 | 214 | 27 B | 36.0 KB |
| 13 | 7 | 69/69/55/46 | 208 | 26 B | 35.4 KB |
| 14 | 7 | 69/69/55/46 | 208 | 26 B | 30.2 KB |

**Contract M = 3 (268 bits)**, baseline 361,720 B: **27 B at c = 11 (K = 5), net 39.1 KB**; 26 B at c = 12,
net 38.0 KB.

**Levers (236 bits + 32 PoW, M = 8)**, baseline 312,403 B: **26 B at c = 12 (K = 7), net 34.8 KB**; 27 B at
c = 10, net 34.5 KB.

**Reading the table.**
* Across all rows, n_min equals the value obtained with ε̂ ≡ 2⁻¹⁰⁰⁰ (checked at c = 8, 10, 11). The
  robust WHIR errors never bind. For example, at c = 11, K = 7, ε̂(m) = −268.8, −258.6, −249.1, …, −203.1
  for m = 0..7.
* n is set by Theorem 4's narrow-collision chain: K = 2, 4, 5, 7, 8 give n = 237, 219, 214, 208, 206.
* K is capped by the radius shift K/B_j against √ρ_j/(2M):
  * at c = 8, K = 7 would cost 80/80/68/62 queries;
  * at c = 11 it costs +1/+1/+2/+2.
* 26 B (n ≤ 208) is the floor: 25 B would need n ≤ 200, below the chain floor at any K ≤ 20.
* Against ANALYSIS §6:
  * the shift columns there (28 B at c = 8, 27 B at c = 9) were too optimistic at small c, because they
    ignored the extra queries;
  * the optimum moves to c = 11;
  * the net result (≈ 39 KB) is in the same range as ANALYSIS's 35–41 KB, now computed with exact byte
    counts (≈ 3.9 KB per digest byte, not 3).

## 6. Residual assumptions and caveats

1. **Review [T].** Theorem 4 (ANALYSIS, with the REVIEW-1 fixes 1–5 applied) and Theorem R here are
   complete as written but unreviewed. The steps most worth a second reader:
   * the choice of v″/v′ (Lemma 1.2(ii)) and Fact V, which together let the robust hypothesis be applied
     at a re-chosen (T, v);
   * the claim in §4.3 that the density bound holds for every contributing T′.
2. **[H-M]** One-call challenges. This is the same as today's plan.
3. **[H-outer]**, §4.7.
4. **Implementation conformance** (not mathematics):
   * OpenVM's `binary_k_fold` must be WHIR's Fold, with the three properties of Lemma 1.2 and the
     even/odd form used in §4.1;
   * query indices must be i.i.d. uniform. With-replacement sampling is used, and dedup only helps.
5. **Spec changes required** (U-7 amendment, user decision):
   * (a) **WHIR-Y**: absorb y_{i,·} before γ_i in every round, including the final round.
   * (b) Node positions (round, oracle, level, index).
   * (c) Deduplicated or consistent repeated openings.
   * (d) 48-B digests above block level c = 11, and narrow 26-B digests below.
   * (e) The FS chain stays at 384 bits.

   Without (a), the attack of §2 applies at every n < 256.
6. **Scope.**
   * Soundness only. Knowledge soundness and extraction for recursion are not covered, as in ANALYSIS
     §8.
   * The robust analysis covers WHIR-Y plus the batching step. The outer PIOP is covered only through
     [H-outer].
7. **15·2^N domains** (lane x15-domains). Nothing here uses smoothness beyond these four facts:
   * fibres of x ↦ x^{2^k} have size 2^k;
   * blocks are unions of fibres;
   * BCGM Thm 9.2 holds for any evaluation domain;
   * the Johnson bound holds for any RS code.

   So Theorem R carries over verbatim to cosets of order c·2^K. The numbers change only through the rates
   and depths of such a shape.
8. **Possible improvements, not taken.**
   * A radius that varies with robustness level (δ − m/B at level m) would remove the extra queries. It
     breaks Claim M (iii) of Theorem 4, which needs doom at level F − 1 to follow from level F at a fixed
     radius.
   * Using a larger MCA multiplicity M′ than the base M would offset the shift. It helps the 42-B
     baseline equally, so it is not a weak-binding saving.
