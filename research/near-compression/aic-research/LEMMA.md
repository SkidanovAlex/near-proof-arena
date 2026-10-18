# The A-IC obstruction, and what any replacement for A-IC must assume

Lane `lane/pq-aic-research`, 2026-10-18. Companion to `REPORT.md`. Notation and numbering of
`../final-soundness/PROOF.md` (cited as PROOF §x / Thm 6.4 / Lemma 7.1 / Assumption 7.3).

Tags (as in PROOF.md): **[T]** proven here, complete as written, not yet reviewed;
**[S]** argued at protocol level, every step stated but one or more steps not written out to
the level of [T] — each such step is marked **(unproven step)**; **[P]** proven in a cited
published source; **[A]** assumption.

## 0. Results

| # | statement | tag |
|---|---|---|
| Thm O | In **every** oracle model in which native verification uses a random function H and adversaries are bounded only in their H-queries, the depth-d ≥ 1 recursive system is **insecure** (success probability ≈ 1, ≤ 2⁴⁵ H-queries), as soon as the base verifier, run with the in-circuit hash, accepts one proof of one false statement. | [T] |
| Lemma E.1 | That hypothesis holds unconditionally when the circuit's hash rows are unconstrained (the "relativized"/oracle-gate model). | [T] at protocol level |
| Lemma E.2 | Abstract "lucky move" lemma: for a uniformly random in-circuit function F, one prover message turns a false sumcheck-type claim into a true one, except with probability ≤ 2⁻¹²⁰⁰⁰. | [T] |
| Lemma E.3 | Hence, for a uniformly random F, the hypothesis of Thm O holds except with probability ≤ 2⁻¹¹⁹⁹⁰. | [S] |
| Cor O.1 | Any proof of the U-6 statement (≤ 2⁶⁴ quantum queries, no time bound) for the recursive claim implies that V₀^{SHA-384} is **perfectly sound**: no false base statement has any accepting proof. | [T] |
| Cor O.2 | The break in PROOF Thm 7.4 is exactly step 2, bullet 2 (the A-IC application), and it cannot be repaired inside any such model. Every valid proof must use (i) a time bound on in-circuit hash computation, (ii) an H-dependent certified relation (native re-check: non-succinct; or an algebraic oracle: AROM), or (iii) an identification (A-IC). | [T] |
| Lemma P | ("peel") With the final layer's FS domain idealised and every in-circuit domain concrete, depth-d soundness reduces, with additive loss = Thm 6.4's bound, to **standard-model** soundness of the depth-(d−1) system with concrete SHA-384, against an adversary whose running time is the original one plus the cost of simulating the compressed oracle. | [T] |
| Cor P.1 | With a naive simulation (time Θ(t²)) Lemma P gives nothing at t = 2⁶⁴: the needed inner assumption is false at time 2¹²⁸ (generic Grover grinding). Whether a simulation in quasi-linear time Õ(t) exists is gate G-P1. | [T] given the cited simulation cost |

Net: a proven bound without A-IC (or without some time-bounded computational assumption on
SHA-384) is **impossible for this architecture in any oracle model**, not merely unknown.

---

## 1. Models

**Definition 1.1 (certified relation).** For i ≥ 1, the layer-i AIR NV_i contains SHA rows that
constrain message/digest pairs. Let C ⊆ M × {0,1}³⁸⁴ be the set of pairs (m, y) that a row
sequence of the SHA AIR can certify, with the framing of PROOF §1.3. Two cases:
* (a) **concrete:** C = graph(F) for the concrete function F computed by the SHA-512-compression
  AIR (truncated per PROOF §1.3). This is the system as built.
* (b) **unconstrained:** the hash rows are free columns ("oracle gates"), C = M × {0,1}³⁸⁴.
  This is the "relativized" circuit of BCG24 Def 3.5/§3.4 and Arnon–Yogev 2025/329 Defs 4.1–4.2,
  when the argument does not check the gates.

For a deterministic verifier V that makes hash calls, write V^C(x, π) = 1 iff V accepts when
every hash call on input m is answered by some y with (m, y) ∈ C, consistently (equal inputs,
equal answers). For C = graph(F) this is V^F.

**Remark 1.2 (C is independent of H — forced).** In any oracle model the scheme (vk_i, its AIR,
its constants) is fixed before H is sampled, and an AIR's satisfying set is defined by fixed
polynomial identities over BabyBear. So C does not depend on H. The only ways for the certified
relation to depend on H are: (1) the native verifier itself queries H on each certified pair —
CGSY24 §6.3/Thm 6.5 "weak relativized NARK", proof size + O(q·λ), not succinct; (2) the oracle
carries an algebraic structure the argument can use — the AROM (CCGOS23 Def 4.1). Neither is
the system as built.

**Definition 1.3 (model M(C)).** H is a uniformly random function on the domain-separated sets of
PROOF Lemma 1.1 (quantum-accessible). The final verifier V_d uses H. For 1 ≤ i ≤ d, the layer-i
relation R_{vk_i} certifies hash pairs in C, so NV-faithful (F1) reads: T ∈ R_{vk_i}(x_i) ⇒
V_{i−1}^C(vk_{i−1}, x_{i−1}, dec_i(T)) = 1 (for C = graph(F) this is exactly PROOF Lemma 7.1,
which is stated for the concrete SHA-384). The adversary is quantum, makes ≤ t queries to H, and
is **unbounded in running time** — the convention of PROOF Thm 6.4 and of the Main Theorem.

**Definition 1.4 (H-ex(C)).** There are a base statement x₀ whose chunk-validation claim is false
(Lemma 7.2's predicate fails for every witness) and a proof π₀ with V₀^C(vk₀, x₀, π₀) = 1.

**Definition 1.5 (C-completeness).** For every i ≥ 1 and every (x_{i−1}, π_{i−1}) with
V_{i−1}^C(π_{i−1}) = 1, the honest layer-i prover run with hash C (C = graph(F)), on the honest
NV_i witness, outputs π_i with V_i^C(π_i) = 1. This is completeness of SWIRL instantiated with F.
It fails only if some PoW move has no witness, or a sampler exceeds the cap J (PROOF Lemma 6.3).
For SHA-384 it is what the running system exhibits; for case (b) it is trivial (answers are
free); for uniformly random F it fails with probability ≤ 2¹⁰·e^{−2³²} (Lemma E.3 step 5).

---

## 2. Theorem O

**Theorem O [T].** Fix d ≥ 1 and C with H-ex(C) and C-completeness. In M(C) there is an adversary
A that makes at most Q_hon ≤ 2⁴⁵ queries to H such that

  Pr_H[ V_d^H accepts (x_d, π_d) ∧ the chunk statement named by x_d is false ] ≥ 1 − 2⁻¹⁰⁰⁰.

*Proof.*
1. **Inner layers, no H-queries.** A hard-codes (x₀, π₀) from H-ex(C). It needs no H-query to
   find them: they exist independently of H (C is independent of H, Remark 1.2), and A is
   unbounded in time (or takes them as non-uniform advice). For i = 1, …, d−1, A runs the honest
   layer-i prover with hash C (case (a): computing F; case (b): any consistent answers) on the
   honest NV_i witness that encodes π_{i−1}. By NV-faithful's converse direction (the honest NV_i
   witness exists whenever V_{i−1}^C accepts — this is NV completeness, which the circuit lane
   proves together with Lemma 7.1) and C-completeness, V_i^C(π_i) = 1, with x_i linked to x_{i−1}
   by (F3). None of this touches H.
2. **Final layer.** A runs the honest layer-d prover **with H** on the honest NV_d witness for
   π_{d−1} (valid: π_{d−1} is V_{d−1}^C-accepting, which is exactly what R_{vk_d} certifies in
   M(C)). Its H-queries are its commitment hashing (≤ 2³⁰ for a domain of 2^{log h + b} = 2²⁷
   leaves plus folds and the W columns' leaf hashing) and its PoW grinding (≤ 8 query moves,
   capped at 2⁴² attempts each). So Q_hon ≤ 2⁴⁵ ≪ t = 2⁶⁴.
3. **Acceptance.** SWIRL with H is perfectly complete except for the PoW and sampler caps. With
   z = 32 and a cap of 2⁴² attempts per move, a move fails with probability (1 − 2⁻³²)^{2⁴²} ≤
   e^{−2¹⁰}; the sampler-cap failure is ≤ (1/16)^{12·2²⁰} per move (PROOF Lemma 6.3). Union over
   ≤ 2¹⁰ moves: failure ≤ 2⁻¹⁰⁰⁰.
4. **Falsity.** By (F3), the base-statement digest in x_d equals x₀'s, which is false. ∎

**Remark 2.1 (consistency with PROOF.md).** Thm O does not contradict the Main Theorem, which
assumes A-IC. It shows that, read inside the model in which Thm 6.4 is proven, **A-IC is false**
for the adversary of Thm O: the pairs Q_d(T_d) are C-pairs that A never queried (case (a): they
are F-values, and F ≠ H; case (b): they are arbitrary). So A-IC can only be read as a statement
about time-bounded, real-world adversaries — outside every oracle model. This agrees with the
derivation from BCG24's §2.4 flip technique (BCG24 itself only proves the relation-level
impossibility, Thms 4.1/5.1/6.1; see REPORT §1).

---

## 3. Existence of accepting proofs of false statements

### Lemma E.1 (unconstrained gates) [T at protocol level]
In case (b), H-ex(C) holds for every false base statement x₀.

*Proof.* In case (b) every hash answer in V₀'s computation is prover-chosen. Then:
* every Merkle authentication check passes by choosing the node outputs top-down to equal the
  required values; the PoW check passes by choosing the PoW block with z leading zeros;
* every Fiat–Shamir challenge is a prover-chosen value;
* hence the prover may commit to nothing and choose every opened value after the challenges.

Fix any trace T′ of the right shape with correct program columns. Run the honest prover on T′
and, at every verifier move, choose the challenge to be a root of the difference between the
claimed and the true round polynomial whenever the current claim is false (a false claim at a
sumcheck round with message degree D ≥ 1 has a cheating message whose difference polynomial has
a root in K∖{0, 1}; see the construction in Lemma E.2). After that move the claim is true, and
from then on the honest prover's messages pass. All WHIR checks pass because the opened values
are those of a genuine codeword (T′'s encoding), or are chosen freely. ∎

### Lemma E.2 (lucky move against a random function) [T]
Let K = F_{p¹²}, |K| = 2^{370.88}, char K ≠ 2. Consider one round of an FS-compiled sumcheck
under T\*: the state σ is fixed; the prover sends s ∈ K[X] of degree ≤ D (D ≥ 2), required to
satisfy s(0) + s(1) = c′; the challenge is r = Samp(G(Abs(σ, s))), where Abs and G are the
restrictions of a uniformly random F to the disjoint absorb and squeeze domains, encodings are
injective (PROOF Lemma 1.1), and Samp maps uniform blocks to a uniform element of K except with
probability ε_cap ≤ (1/16)^{12·2²⁰} (PROOF Lemma 6.3). Let s\* (degree ≤ D) be the true round
polynomial, with s\*(0) + s\*(1) = c ≠ c′. Then

  Pr_F[ ∄ s : s(0)+s(1) = c′ ∧ s(r(s)) = s\*(r(s)) ] ≤ 2⁻¹²⁰⁰⁰.

*Proof.*
1. **Candidates.** Put δ = c′ − c ≠ 0. For a ≠ b in K with N(a,b) := ab + (1−a)(1−b) ≠ 0, let
   Δ_{a,b}(X) = δ·(X−a)(X−b)/N(a,b) and s_{a,b} = s\* + Δ_{a,b}. Then deg s_{a,b} ≤ D,
   s_{a,b}(0) + s_{a,b}(1) = c + δ·N(a,b)/N(a,b) = c′, and s_{a,b}(a) = s\*(a), s_{a,b}(b) = s\*(b).
   Distinct unordered pairs {a,b} give distinct s_{a,b} (the root sets differ). The number of
   admissible pairs is ≥ (|K|² − 3|K|)/2 > 2⁷⁴⁰. Take any M = 2³⁸⁴ of them.
2. **Absorb outputs.** The κ_{a,b} := Abs(σ, s_{a,b}) are M independent uniform 384-bit strings
   (distinct inputs). Let N_κ be the number of distinct values. E[N_κ] = 2³⁸⁴(1 − (1 − 2⁻³⁸⁴)^M)
   ≥ 0.632·2³⁸⁴. N_κ is 1-Lipschitz in each κ, so by McDiarmid, Pr[N_κ < 2³⁸³] ≤
   exp(−2(0.132·2³⁸⁴)²/2³⁸⁴) = exp(−0.035·2³⁸⁴) < 2^{−2³⁷⁹}.
3. **Challenges.** Condition on the absorb values. G is independent of Abs (disjoint domains),
   so the challenges r_κ at distinct κ are independent and, outside the cap event, uniform on K.
   For each distinct κ pick one candidate {a,b} with κ_{a,b} = κ. It wins iff r_κ ∈ {a, b}:
   probability 2/|K|. So Pr[no win | N_κ ≥ 2³⁸³] ≤ (1 − 2/|K|)^{2³⁸³} + 2³⁸⁴·ε_cap
   ≤ exp(−2^{384−370.88}) + 2⁻⁵⁰⁰⁰⁰⁰⁰ ≤ 2⁻¹²⁸⁰⁰ (log₂e·2^{13.12} ≈ 12 840).
4. Total ≤ 2^{−2³⁷⁹} + 2⁻¹²⁸⁰⁰ ≤ 2⁻¹²⁰⁰⁰. ∎

The same argument applies to any verifier move whose check is "a nonzero polynomial of degree
≥ 1 in the challenge vanishes" and whose preceding prover message ranges over a family with
≥ 2³⁸⁴ members with distinct roots — e.g. the GKR line reduction (claim (1−μ)a′ + μb′ vs the
true (1−μ)a + μb, with (a′, b′) ranging over the solutions of the root relation).

### Lemma E.3 (random F satisfies H-ex) [S]
For F uniformly random (independent of H), H-ex(graph F) and graph(F)-completeness hold except
with probability ≤ 2⁻¹¹⁹⁹⁰.

*Argument.*
1. Take a false base statement x₀ and any trace T′ of the right shapes, with correct program
   columns, whose public values name x₀. T′ ∉ R_{vk₀}(x₀).
2. The cheating prover commits honestly to T′'s encoding (a genuine interleaved codeword), so
   every WHIR claim about it that is *true* is proven by the honest WHIR prover.
3. **(unproven step)** Every reason T′ ∉ R surfaces as a *false* claim in some sumcheck-type
   move of the PIOP (zerocheck for constraint violations, LogUp-GKR for unbalanced buses, the
   root relation for the GKR output), and each such move's message space contains a two-root
   family as in Lemma E.2. This needs the message shapes of PROOF §3: plain rounds of degree
   ≥ 2; Gruen rounds s = eq_pre·eq₁(ξ, X)·t(X) with t of degree 2 and one linear constraint, so
   that t′ − t = c·(X−a)(X−b) with c fixed by the constraint whenever that coefficient is nonzero.
   This is a routine but unwritten case check over every sub-protocol.
4. Apply Lemma E.2 at the first false claim of each sub-protocol (≤ 2⁶ applications): after the
   lucky round the claim is true, and the honest prover continues. Union bound ≤ 2⁶·2⁻¹²⁰⁰⁰.
5. PoW witnesses exist for each move except with probability (1 − 2⁻³²)^{2⁶⁴} per move;
   sampler caps as in Theorem O step 3. ∎

**Status of H-ex for the concrete SHA-384.** It is a finite statement about one function and
cannot be proven or refuted with known techniques. Its negation — that the FS/Merkle-compiled
base verifier with concrete SHA-384 is *perfectly* sound for every false statement — would be a
statistically sound succinct non-interactive proof with a fixed hash, which fails for all but a
2⁻¹¹⁹⁹⁰ fraction of functions (Lemma E.3) and which no one believes for SHA-384.

---

## 4. Corollaries

**Corollary O.1 [T].** Suppose a proof establishes: "for every quantum adversary making ≤ 2⁶⁴
queries to SHA-384-as-random-oracle (no time bound), Pr[V_d accepts ∧ chunk statement false] ≤
2⁻¹²⁸", for some d ≥ 1, in any model satisfying Definition 1.3. Then ¬H-ex(graph SHA-384): V₀ with
concrete SHA-384 is perfectly sound.

*Proof.* Contrapositive of Theorem O (with C-completeness, which the running system exhibits;
if it failed, π₁ would not exist, but then also no honest recursion would run). ∎

So the contract U-2 + U-6, as worded (query-bounded only), **cannot be met by any proof** for the
recursive claim; it can only be met (a) for the non-recursive base proof (PROOF Cor 6.5), or
(b) under an assumption that ties in-circuit computation to the oracle or bounds the
adversary's time.

**Corollary O.2 [T] (the precise obstruction).** In PROOF Thm 7.4, steps 1, 2 (bullet 1), 3 and 4
hold in M(graph F). Step 2 bullet 2 — "by A-IC, every hash in Q_i(T_i) is D-consistent" — is the
only step that fails, and by Theorem O no argument confined to M(C) can replace it, for any C
(Remark 1.2 makes C independent of H in every oracle model). A replacement must leave M(C) in one
of three ways:
* (i) **bound the adversary's time** on in-circuit hash computation (standard-model assumption on
  SHA-384) — the best such reduction is Lemma P;
* (ii) **make the certified relation H-dependent**: either the native verifier re-queries every
  certified pair (CGSY24 Thm 6.5; proof grows by every in-circuit hash input of every layer, i.e.
  by at least the size of π₀ itself, so it is dominated by sending π₀) or the oracle is algebraic
  (AROM, CCGOS23 Thm 9.4: classical only, asymptotic, an uninstantiable random-extension
  assumption, SHA-384 has no low-degree arithmetization);
* (iii) **identify** in-circuit evaluations with oracle queries (A-IC, or CGSY24 §2.3's conjecture
  "attacks on the real scheme are no more effective than on the idealised one").

---

## 5. Lemma P (peel one layer into the standard model)

**Setting (model M_mix).** Layer d's native prover and verifier use FS/Merkle hash domain P_fin,
modelled as a QRO H. Every hash computed inside any circuit (layers 1..d verify layers 0..d−1)
uses domain P_in ≠ P_fin, evaluated concretely: F := SHA-384(P_in-framed ·). This needs P_fin to
be a final-layer-only prefix (REPORT §5, change H-1); in the code today the prefix is shared, so
M_mix does not describe the code yet. The adversary A is quantum with ≤ t H-queries and running
time τ_A (F counted as ordinary gates).

**Assumption S_{d−1}(τ, ε_S) [A, standard model].** No quantum algorithm of time ≤ τ outputs
(x_{d−1}, π_{d−1}) with V_{d−1}^F(π_{d−1}) = 1 and the base statement named by x_{d−1} false, with
probability > ε_S.

**Lemma P [T].** Assume NV-faithful(d) (Lemma 7.1 with SHA-384 = F) and T\* for layer d. For every
A as above there is B (no oracle) with τ_B ≤ τ_A + Sim(t) + Ext such that

  Pr[A wins in M_mix] ≤ ( √Pr[B breaks S_{d−1}] + 2⁻¹⁶⁰ )² + (t′G)²,

with t′, G as in PROOF Thm 6.4 for the one-element family {vk_d}. Here Sim(t) is the cost of
simulating Zhandry's compressed oracle for t queries and measuring D, and Ext = poly(n) is the
cost of reading π_d's transcript from D and list-decoding T_d (PROOF S-25, Guruswami–Sudan).

*Proof.*
1. B runs A with H replaced by the compressed oracle on the P_fin domain. This is a perfect
   simulation [P: Zha19]. A's F-computations are ordinary computation, unaffected.
2. B measures D and reads A's output π_d.
3. By PROOF Thm 6.4 step 7 (Fact A) applied to the event W = "V_d^H accepts and the base statement
   is false": √Pr_real[W] ≤ √Pr_D[π_d is D-consistent, accepting, statement false] + √(ℓ_V/2³³⁶),
   with √(ℓ_V/2³³⁶) ≤ 2⁻¹⁶⁰.
4. By Thm 6.4 steps 2–6 (one IOP, family {vk_d}), Pr[κ(D) = 1] ≤ (t′G)². If κ(D) = 0 and π_d is
   D-consistent and accepting, then by step 8 the round-0 list Λ₀ contains c with
   T_d := unstack(c) ∈ R_{vk_d}(x_d), and B finds it by list decoding.
5. B outputs π_{d−1} := dec_d(T_d), x_{d−1} := pv_d(T_d). By (F1) with F, V_{d−1}^F accepts; by
   (F3) the base statement is x_d's, which is false on the event W.
6. So Pr[B breaks S_{d−1}] ≥ Pr_D[D-consistent accepting false] − (t′G)², and rearranging gives
   the claim. ∎

**Corollary P.1 (concrete accounting) [T, given the simulation cost].** With t = 2⁶⁴, (t′G)² and
2⁻¹⁶⁰ are as in PROOF §9 (total 2⁻¹³⁵·²). The inner assumption is needed at time
τ = τ_A + Sim(2⁶⁴).
* A straightforward compressed-oracle implementation keeps a database of ≤ t entries and touches
  all of them per query: Sim(t) = Θ(t²·n) ≈ 2¹³⁸ gates. At time 2¹³⁸ the inner layer is broken by
  generic quantum grinding with success ≈ τ²·ε_rbr = 2²⁷⁶·2⁻²⁶⁸·⁵ > 1, and the 336-bit node
  digests admit BHT collisions at 2¹¹². So **S_{d−1}(2¹³⁸, 2⁻¹²⁸) is false**, and Lemma P yields
  nothing at the contract level.
* If Sim(t) = Õ(t)·poly(n) (gate **G-P1**: not established here; known efficient simulations are
  only stated as poly(t, n) per query), τ ≈ 2⁶⁴⁺ᶜ and S_{d−1} is not contradicted by any generic
  attack (τ²ε ≈ 2^{128+2c−268.5}).
* Even then, S_{d−1} is an adaptive-soundness assumption for a SNARG for NP with a fixed hash.
  It is not falsifiable in Naor's sense, and Gentry–Wichs (ePrint 2010/610, Thm 5.1) rules out
  black-box reductions of it to any falsifiable assumption. It is the depth-(d−1) system's own
  security. So Lemma P *relocates* A-IC (to a standard-model statement about the inner system)
  rather than removing it.

---

## 6. Status

| item | tag | open step |
|---|---|---|
| Thm O | [T] | uses NV completeness (circuit lane) and C-completeness (exhibited by the running system) |
| Lemma E.1 | [T] protocol level | — |
| Lemma E.2 | [T] | — |
| Lemma E.3 | [S] | step 3: case check of message families over all PIOP sub-protocols |
| Cor O.1, O.2 | [T] | — |
| Lemma P | [T] | requires P_fin ≠ P_in (change H-1, not in code) |
| Cor P.1 | [T] | G-P1: quasi-linear compressed-oracle simulation |

## References
BCG24 = Barbara–Chiesa–Guan, ePrint 2024/728 (TCC 2025), Defs 3.5, 3.13, 3.14; Thms 4.1, 5.1, 6.1;
§2.4. CGSY24 = Chiesa–Guan–Samocha–Yogev, ePrint 2023/1646 (TCC 2024), Def 3.6, Thm 5.1,
Remark 5.2, §2.3, §6.3, Thm 6.5. CCGOS23 = Chen–Chiesa–Gur–O'Connor–Spooner, ePrint 2023/587
(Eurocrypt 2023), Def 4.1, Thm 8.1, Thm 9.4. Arnon–Yogev, ePrint 2025/329, Defs 4.1–4.2, Thm 5.6.
GW11 = Gentry–Wichs, ePrint 2010/610, Thm 5.1. Zha19 = Zhandry, ePrint 2018/276. PROOF.md
references for the rest.
