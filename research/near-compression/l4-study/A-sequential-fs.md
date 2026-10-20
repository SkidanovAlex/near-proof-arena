# L4 / Hypothesis A: sequential-work Fiat–Shamir for WHIR query sampling

Date: 2026-10-17. Design analysis only. No repository was modified.
Tags: [P] proven in the cited source, [O] open, [I] my inference or heuristic.

Scratch artefacts (all in `.../scratchpad/l4/`):
- `model/` holds read-only copies of `final_layer_model.py` and `levers_model.py`.
- `repro.py` reproduces the corrected fixed point from the log: 444,481 / 527,161 B today and 355,883 / 416,893 B with all levers, at c_sha 12k / 24k.
- `chain_grid.py` and `chain_grid.out` hold the chain-lever grid.
- `chain2.c` is the sequential SHA-384 benchmark.
- `papers/` holds BLZ21 (arXiv 2006.10972), CFHL21 (arXiv 2010.11658 = ePrint 2020/1305), arXiv 2509.09896, and the abstract of ePrint 2026/2326. The archive PDF of 2026/2326 failed, so only the landing page was read.

## 0. Verdict up front

**KILL as a proof-size lever. Keep one note: it can replace grinding to save prover work.**

- **Size gain is small.** If the open lemmas hold, the best net gain over the "all levers" point (which already includes grinding z = 32) is about 10 KB (−3 %) at a verifier cost of 0.4–1.3 s. It is about 29 KB (−8 %) only with a sequential-grinding variant that also needs 2^36 parallel hashes per round.
- **It does not reach 300 KB.** The best point is 327 KB at c_sha 12k, and 380–400 KB at 24k.
- **The core quantum lemma is unproven**, and the obvious compressed-oracle argument gives no gain at all (§1.3).
- **Cheap verification is impossible here.** PoSW proofs and spot checks give no unique output, so they hand the adversary free resampling (§2.2).
- **The verifier must recompute R·T compressions.** That multiplies native verify time by about 10–500×, and it rules out in-circuit or on-chain verification of the final proof.

## 1. The QROM claim, made precise

### 1.1 Construction

For each WHIR query phase i (R ≈ 4–5 phases in the final layer):

- Take the transcript prefix τ_i.
- Set y_0 = H("start", τ_i) and y_j = H("step", j, y_{j−1}) for j = 1..T.
- Derive the query positions from y_T. The step index j and the domain tags stop chains from sliding into or merging with each other.
- The verifier recomputes the chain.

This must be done per phase. Each phase's queries are sampled after the next commitment, so an adversary resamples phase i cheaply by changing that commitment. One chain cannot be shared across phases [I].

### 1.2 Claim to prove (L1, "slow-oracle search")

Setup:

- H is a random oracle with n = 384-bit outputs.
- G(x) is the end y_T of the chain defined above.
- R(x, y) is a relation with Pr_y[R(x, y)] ≤ ε for every x. This models "queries derived from y are all bad for prover state x".

Claim: any quantum algorithm making t queries to H, at any depth or width, outputs x with R(x, G(x)) with probability

  p ≤ C·(t/T)²·ε + O(t²·T / 2^n).

The second term covers collisions and chain-merging. This would give a gain of 2·log2 T bits per query phase.

The FS-level statement (L2) adapts the CMS19 / DFMS measure-and-reprogram bound to the case where the challenge oracle is a chain end. It would read:

  p_FS ≤ Σ_{query phases} C·(t/T)²·ε_i + Σ_{other rounds} C·t²·ε_j + O(t³/2^n).

### 1.3 What the literature actually proves

- **[P] Depth lower bounds only.**
  - BLZ21 Thm 1.2 (also Unruh 2015, sequential QROM) covers an adversary that makes q queries in each of N−1 parallel rounds. It computes H^N(x) for a random x with probability at most N/2^λ + 2^−(λ−N)... + 48λN⁴q²T/2^{λ/2}.
  - BLZ21 Thm 1.3 / Lemma 4.11 extend this to arbitrary H-sequences.
  - CFHL21 §2 bounds the probability of finding a (q+1)-chain with q k-parallel query rounds by O(q³k³T/|Y|).
  - Both papers then prove the Cohen–Pietrzak FS-PoSW post-quantum secure. BLZ Thm 1.4 gives ≤ 16q²(1−α)^{⌊λ/n⌋} + 32q³(n+2)λ2^−λ + q³2^−λ for an adversary limited to (1−α)N rounds.
  - These are statements about *rounds* (sequential depth). They bound neither total queries nor a search over chain outputs.
- **[P] Grover-type bounds.** Grover optimality and parallel Grover optimality (Zalka; Zhandry; CFHL21 §2) give p = O(k q²/|Y|) for q rounds of k parallel queries. With the depth result, this is consistent with the heuristic optimal attack: p parallel Grover instances of depth d have success ≈ p·(d/T)²·ε ≤ (t/T)²·ε when t = p·d. That is evidence for L1, not a proof [I].
- **[O] Nothing found proves L1, or even the weaker t²ε/T.** The searches covered iterated hashing in the QROM, key stretching, PBKDF2, slow-hash Fiat–Shamir and PoW-FS. The closest results are:
  - Ambainis' variable-time search lower bound Ω(√Σt_i²). It is bounded-error and worst-case, in a structured-input model, not average-case in the QROM at success 2^−128.
  - Reichardt / Lee et al. adversary-bound composition. It applies to Boolean functions with independent inner inputs and bounded error, not to the small-success regime needed here.
  - Bünz–Chen–Guan, ePrint 2026/2326. It is classical ROM: grinding needs a "non-amortizing" PoW, and a single PoW cannot be both strong and non-amortizing when the verifier is much cheaper than the prover.
- **[I] Why the obvious proof fails.** CFHL's transition-capacity framework bounds progress by a maximum over databases D. A database that already holds a (T−1)-chain lets one query complete the bad event with probability ε. So capacity is about √ε per query and the bound collapses to t²ε, with no gain.
  - Counting partial chains instead (at most s/T complete chains after s queries) gives about t³ε/T. That is worse than t²ε whenever t > T.
  - A real proof needs a progress measure that tracks chain length coherently, combining the BLZ/CFHL chain hybrid with Grover's bound in the *total-query* model. That is new research.
- **[I] Grinding and chaining substitute for each other; they do not add.**
  - Grinding z bits costs a quantum attacker about 2^{z/2} per candidate.
  - Doing both as independent checks gives per-candidate cost ≈ T + 2^{z/2} under nested amplitude amplification, so the gain is ≈ 2·log2 max(T, 2^{z/2}).
  - If the PoW comes after the chain, the attacker fixes one chain and grinds nonces, so the chain buys nothing.
  - Gains only multiply in a "sequential grinding" form: find a nonce such that H^T(τ, nonce) has z zero bits, then derive the queries from that output. Honest work is 2^z·T (parallel), latency T, verifier T, and the conjectured gain is z + 2·log2 T. The bound p ≤ (t/T)²·2^−z·ε is also [O].
- **[O] L2 (FS transfer).** Measure-and-reprogram must reprogram the last chain step while the adversary's queries are spread over the chain. No existing CMS19 / DFMS / DFM20 variant gives (t/T)².

So the requested "(t/T)²·ε" bound is **not proven** for the combined game. What is proven is that fewer than T sequential rounds cannot produce the chain output at all.

## 2. The verifier problem

### 2.1 Full recomputation: the only sound option found

- Verifier cost is R·T compressions. Each chain step is one SHA-384 compression, since a 48-B digest plus index fits one 128-B block.
- Measured on this host (AMD Ryzen 9 9950X3D, OpenSSL, no SHA-512 instructions):
  - **95.6 ns per step** using raw `SHA512_Transform` in a dependent chain;
  - 305 ns per step using the one-shot `SHA384()` API.
- So 0.1 µs per compression is a realistic optimised CPU latency. GPUs are slower per thread, about 1 µs or more [I].
- The current final verify is about 10k compressions, roughly 1–3 ms. Chains add:

| T per phase | gain g = 2·log2 T | added compressions (R = 4) | added verify time @ 0.1–0.3 µs |
|---:|---:|---:|---:|
| 2^16 | 32 | 262k | 26–79 ms |
| 2^18 | 36 | 1.05M | 0.10–0.31 s |
| 2^20 | 40 | 4.2M | 0.42–1.26 s |
| 2^22 | 44 | 16.8M | 1.7–5.0 s |
| 2^24 | 48 | 67M | 6.7–20 s |

The final proof can no longer be checked cheaply inside another circuit (T·c_sha cells per phase) or on chain: millions of SHA-384 calls under a gas limit [I].

### 2.2 PoSW (Cohen–Pietrzak, MMV) and spot checks: broken here, not just expensive

- **What PoSW soundness says.** It guarantees that the prover did about (1−α)N sequential work [P, BLZ/CFHL]. It does **not** make the output unique.
- **The attack.** Fake one label (or one checkpoint segment). The root, and so the query positions, change at a cost of about log T hashes. The PoSW check misses this with probability about 1 − O(t_ch·log T / T).
- **The consequence.** The adversary regains nearly free resampling, and the protection disappears. Spot-checking recomputation of c′ out of c segments fails the same way, with detection only c′/c per fake [I].
- **The bytes are prohibitive anyway.**
  - With the BLZ bound at q = 2^64 and α = 1/2, (1−α)^{t_ch} ≤ 2^−260 needs t_ch ≈ 260 challenges.
  - Each opening is about (log2 T + 1) labels × 48 B, which is about 1 KB at T = 2^20.
  - That totals ≈ 200–260 KB after top-level dedup. This is larger than the entire WHIR authentication data (142 KB) and 10–25× the bytes it could save.
- This fits the BCG26 classical impossibility: cheap verification conflicts with the strong-and-non-amortizing property this use needs [I].

### 2.3 Proving the chain inside a proof

- **Circular.** The chain-checking sub-proof has its own final query phase, which needs either another chain or the full 268-bit target. The regress ends in an unprotected query phase whose Merkle bytes are comparable to the savings [I].
- **Too expensive in circuit.** In-circuit cost is T·c_sha, about 2^16 × 12k ≈ 2^29.5 cells per phase, above the whole final circuit (2^26.8).
- The same cost rules out using chains in the penultimate layer to shrink the final circuit.

## 3. Net bytes (calibrated model, final layer only, m = 8, 300 columns)

- The penultimate layer is unchanged; the chain applies only to the natively verified final layer, with final target = base − g.
- "Levers" means: penultimate grinding z = 32 (target 236), base constant pinned at 258, and 42-B digests.
- In the levers columns, g = 32 equals the z = 32 grinding already in the "all levers" point. The incremental value of chaining is the difference from that row.

| g (T) | today 12k | levers 12k | today 24k | levers 24k | added verify (R = 4–5) |
|---:|---:|---:|---:|---:|---:|
| 0 | 444,481 | 392,815 | 527,161 | 463,695 | — |
| 32 (2^16) | 402,513 | **355,883** (= z = 32) | 474,465 | 416,893 | 26–98 ms |
| 36 (2^18) | 396,705 | 350,659 | 466,481 | 411,447 | 0.10–0.39 s |
| 40 (2^20) | 391,745 | 345,435 | 460,473 | 403,345 | 0.42–1.6 s |
| 44 (2^22) | 385,825 | 341,141 | 451,481 | 398,787 | 1.7–6.3 s |
| 48 (2^24) | 381,057 | 335,875 | 446,433 | 393,299 | 6.7–25 s |
| 56 (seq-grind z = 16, T = 2^20) | 370,833 | **327,235** | 432,393 | 381,569 | 0.5–1.6 s, plus 2^36 parallel hashes per phase |
| 64 (seq-grind z = 24, T = 2^20) | 357,169 | 314,905 | 421,337 | 367,895 | same, plus 2^44 per phase (not real-time) |

- **Marginal value.** About 1.1–1.3 KB per security bit; each doubling of T saves about 2.6 KB and doubles verifier time.
- **Why it is small.** Queries scale linearly with the target, and 226 → 218 is only −3.5 %.
- **Within budget.** At a verifier budget of ≤ ~1 s (T ≈ 2^20), the chain saves **~10 KB over grinding z = 32** at 12k, and ~13 KB at 24k.
- **The 300 KB gap remains.** No point under 300 KB appears at any feasible T.

## 4. Prover latency

- Per phase, latency is T sequential compressions: 2^20 takes 0.1 s on a tuned CPU (0.3 s with naive code); 2^24 takes 1.6–5 s.
- The 4–5 phases are sequential, giving 0.4–1.5 s at T = 2^20, which is acceptable.
- **This is where chaining is genuinely better than grinding.** Equal quantum bits g cost the honest prover 2^{g/2} sequential hashes instead of 2^g parallel ones. For g = 40: 2^20 hashes (0.1 s) versus 2^40 (≈ 150 GPU-s per phase at ~7 GH/s per GPU).
- But grinding up to z ≈ 32–36 is already cheap on a few H200s, and those bits are where most of the size benefit sits.

## 5. Open lemmas (what would have to be proven to use any of this)

1. **L1 slow-oracle search [O].** For an index-separated chain G = H^T and any relation R with per-x density ε, a t-query QROM adversary has Pr[R(x, G(x))] ≤ C·(t/T)²·ε + O(t²T/2^n), with explicit C. No proof exists even for the weaker t²ε/T, and the compressed-oracle capacity method gives no gain (§1.3).
2. **L2 FS/BCS transfer [O].** A CMS19 / DFMS-style measure-and-reprogram where some challenge oracles are chain ends, giving loss Σ C·(t/T_i)²·ε_i, composed with WHIR's rbr knowledge soundness. It inherits the still-open WHIR / QROM items already in the log.
3. **L3 sequential grinding [O].** p ≤ C·(t/T)²·2^−z·ε when the queries come from a chain output that must also carry z zero bits.
4. **L4 non-stacking [I].** Independent grinding and chaining add only as max(T, 2^{z/2}). A proof would just confirm that chaining is not an extra lever on top of z = 32 grinding.
5. **Impossibility direction [O/I].** Whether any hash-only, uniquely-determined slow function with verifier ≪ T exists. This is plausibly impossible, by analogy with the BCG26 classical result, and it is what would be needed to avoid the verifier blow-up.

## 6. Recommendation

- **Drop Hypothesis A as a size lever for L4.** It needs open quantum lemmas for ≤ 3–8 % (10–29 KB), at a 100–500× verifier slowdown that also blocks recursive or on-chain verification.
- **Record one point:** if L1/L2 are ever proven, a short chain (T = 2^16, +26–79 ms verify) could replace z = 32 grinding to save prover GPU work. That is a prover-cost trade, not a size win.

## Sources

- Blocki–Lee–Zhou, *On the Security of Proofs of Sequential Work in a Post-Quantum World*, ITC 2021 — https://arxiv.org/pdf/2006.10972
- Chung–Fehr–Huang–Liao, *On the Compressed-Oracle Technique, and Post-Quantum Security of Proofs of Sequential Work*, Eurocrypt 2021 — https://arxiv.org/pdf/2010.11658 / https://eprint.iacr.org/2020/1305
- Bünz–Chen–Guan, *It Takes Two: Proofs of Work for Fiat–Shamir*, ePrint 2026/2326 (abstract only) — https://eprint.iacr.org/2026/2326
- *Improved Quantum Lifting by Coherent Measure-and-Reprogram*, arXiv 2509.09896 (skimmed for k-search lifting; not directly applicable) — https://arxiv.org/pdf/2509.09896
- Model and log: `/data/illia/nearproof-wt/pq-native-hermetic/research/near-compression/native/{final_layer_model,levers_model}.py`, `docs/logs/pq-final-layer-model-2026-10-17.md`
