# L4 / Hypothesis B — can hash-only authentication beat optimal Merkle multiproofs?

Date 2026-10-17. Research note only. No repository was modified. Tags: **[P]** proven in the cited
source; **[O]** open, needs a new proof; **[I]** my own inference or calculation, not peer-reviewed.

Scripts are in `scratchpad/l4/calc/` (`lb.py`, `lb2.py`, `lb3.py`, `misc.py`, `digest.py`). They import
copies of `final_layer_model.py` and `levers_model.py` from `scratchpad/l4/model/`. The baselines
reproduce the log's corrected fixed point: 444,481 / 527,161 / 570,313 B at c_sha = 12k / 24k / 32k
("today", m = 8, 268 bits, 48 B). At 12k the final layer's shape is b=8, k1=1, k=3, h=2^19,
q = [69, 69, 55, 46], Merkle depths [26, 23, 22, 21], and auth = 188,736 B = 3,932 multiproof digests.

## Bottom line

* **The digest *count* is essentially optimal. The digest *width* is where the slack is.**
  - No general ROM/QROM lower bound forces about q·log(N/q) digests per batch opening.
  - Inside the Merkle-tree model, though, the uniform-query optimal multiproof is within about
    9–18 % of a lower bound that holds for *any* query distribution (§1.3). That bound is a
    relaxation, and the real gap is smaller.
  - Every structural trick tested (correlated queries, shared trees, caps, arity, leaf size, grinding
    for favourable positions) is KILLED: at best break-even, usually worse.
* **PROMISING, but needs new proofs:** a weak-binding analysis of the Chiesa–Yogev type ("tight
  Micali" or the capped "subquadratic SNARG" analysis) carried to the QROM and to multi-round BCS.
  It would replace the "full collision resistance at ε" requirement (n ≥ log(t³/ε) ≈ 320 → 42–48 B
  digests) with n ≈ 3·log t + O(log log) ≈ 200–210 bits (≈ 26 B, capped tree) or ≈ 283–288 bits
  (≈ 36 B, uncapped).
  - Modelled final layer at c_sha = 12k: 444 → **338–348 KB** (26–28 B, no other lever).
  - With the existing levers (z = 32 grinding, m = 8, k1 free): **276–290 KB**. That is under 300 KB
    and hash-only, using a 4-ary penultimate tree, which 26 B digests make one SHA-512-family
    compression per node.
  - At c_sha = 24k: 319–340 KB.
  - Status: none of it is proven in the QROM or for IOPs. It is a concrete research target (§3).

## 1. Lower bounds: is ~q·log(N/q) digests optimal?

### 1.1 What is proven

* **[P] Folklore** (Haitner–Nukrai–Yogev, ePrint 2022/178, App. B): any ROM-SNARG has length
  Ω(log(t/ε)).
* **[P] Haitner–Nukrai–Yogev, CRYPTO 2022 (ePrint 2022/178), Thm 1.1 / 5.1.**
  - Statement: assuming rETH, every (t, ε)-*salted-sound* ROM-SNARG with a *deterministic
    non-adaptive* verifier has length Ω(log t · log(t/ε) / log q_P).
  - Thm 1.3 / 6.3 gives the same bound for ROM subvector commitments: α + β(log(t/ε)) ∈
    Ω(log t · log(t/ε) / log n), i.e. about log t / log n bits per opened element.
  - It matches Chiesa–Yogev's construction up to log n factors.
  - Applicability to us: weak.
    - It is classical ROM only.
    - Fiat–Shamir query derivation counts as non-adaptive in their sense (footnote 4).
    - Scale: log t · log(t/ε) ≈ 64 · 192 bits ≈ 1.5 KB, about 100× below our ≈ 190 KB of paths.
    - It **does not** prove that paths of length log N are necessary. The authors list a direct
      (unconditional, wider-class) SVC lower bound as an open problem. **[O]**
* **[P] Tamassia–Triandopoulos, ICALP 2005** ("Computational bounds on hierarchical data
  processing"). In the hierarchical-data-processing (hash-DAG) model, membership proofs for
  hash-based authenticated dictionaries cost Ω(log n), even with O(n^{1−ε}) authentication
  information. This is the only path-length lower bound found. It covers single membership in a
  restricted structural model, not batch openings in the ROM. Papamanthou–Tamassia–Triandopoulos
  ("optimal verification of operations on dynamic sets") go beyond hashing (accumulators), so they
  do not apply.
* **[P] Chiesa–Yogev, Barriers (TCC 2020)**, as cited by HNY22. A ROM-SNARG's verifier must make
  enough queries, and every ROM-SNARG "contains" an IOP with related parameters. Query count is
  therefore bounded by IOP soundness: q ≥ λ / (bits per query). That matches our WHIR schedule and
  says nothing about the commitment's size.
* **[P] Chiesa–Yogev, CRYPTO 2021 (ePrint 2021/281):** a ROM-SNARG of size Õ(log(t/ε) · log t), up
  from Micali's Õ(log²(t/ε)).
  - The saving comes from the **digest width** (λ ≈ 2 log t + log β + 3), not from path count. Paths
    keep their log(l/2^{i*}) length.
  - Their Table 1 at (t, ε) = (2^64, 2^-128): Micali 346 KB vs theirs 188 KB (1.84×).
  - They explicitly leave QROM adaptation open ("we leave it for future work to adapt [CMS19]").
* **[P] Chiesa–Yogev, TCC 2021 (ePrint 2021/188), "Tight security bounds for Micali's SNARGs".**
  - Soundness: t·ε_PCP + C·t/2^λ with C ≤ 12·l·log|Σ|, provided λ ≥ 2 log t + 6.
  - So collisions need not be negligible at the ε level, only rare (t²/2^λ ≤ 2^-6). Requires
    per-node domain separation.
  - Nearly matching lower bound: C ≥ l log|Σ| / q².
* **[P] CMS19 (Chiesa–Manohar–Spooner, TCC 2019, ePrint 2019/834).** BCS in the QROM has error
  O(t²·ε_rbr + t³/2^λ). This is the source of the current n ≥ 320 → 336–384-bit rule. No tight
  QROM analysis of Merkle/BCS was found (search of 2023–2026 ePrint: 2023/1256 gives the QROM
  rbr→FS transfer, 2024/724 gives UC Merkle bounds, both classical-style binding).

### 1.2 Does the bound apply to our setting?

Our setting: adaptive FS-derived positions, 2^20–2^26 leaves, q ≈ 46–150 per round. The answer is
"only in a restricted model".

* In the bare ROM nothing rules out sub-log(N/q) openings.
* No known hash-only construction achieves them. CY21 still pays log(l/q) digests per query.
* "Constant-size proofs from hashes" do not exist. HNY22 rules them out conditionally:
  Ω(log t·log(t/ε)) is superlinear in λ.
* Micali's CS proofs are O(λ² log n). No hash-only "proof-carrying hash" scheme with
  constant-size openings was found.
* Verdict on the literature: **no route to fewer digests. CY21/CY-tight are a route to narrower
  digests.**

### 1.3 New: Merkle-model lower bound for any query distribution [I]

The question: for a fixed public leaf layout, can a non-uniform (clustered) query distribution
reach the same round soundness with fewer multiproof digests?

**Argument.**
* Write u_ℓ for the number of level-ℓ subtrees the query set touches. Exactly,
  digests = 2 + Σ_{ℓ=1}^{d−1} u_ℓ − u_d.
* Attack: the adversary commits a word that agrees with a cheating codeword on a set S of density
  α = 2^{-b}. In the list-decoding regime b = −log₂((1+1/2m)√ρ). The adversary may choose S
  aligned to subtrees: a "heavy" class of B level-ℓ subtrees with internal agreement a_h, and the
  rest with agreement a_l, averaging α.
* Every such S is realisable: corrupt a codeword off S with junk.
* Against this attack family the best defender splits the q distinct leaves equally across groups
  (Jensen, since the per-group log-miss is convex in group size). That yields a minimum u_ℓ per
  level for miss ≤ 2^-268.
* Summing the per-level minima gives a lower bound (LB) on expected digests for **any**
  distribution.
* The bound only grows as the attack family grows:
  - pure full-subtree attacks gave a gap of ≈ 250 digests per round;
  - mixed full + uniform attacks gave ≈ 200;
  - two-class heavy/light attacks gave ≈ 118.

| shape | uniform multiproof | LB (2-class attacks) | max headroom |
|---|---:|---:|---:|
| final, c_sha 12k (q 69/69/55/46, d 26/23/22/21) | 3,932 | 3,463 | 469 digests = 22.5 KB (11.9 %) |
| final, c_sha 24k (5 rounds) | 5,627 | 4,886 | 741 digests = 35.6 KB (13.2 %) |
| child gas-failure5 | 3,499 | 2,880 | 619 digests = 29.7 KB (17.7 %) |

**Reading the table.**
* The headroom sits entirely in the top ≈ log q + b levels.
* It is an upper bound on what any clustering trick could save. The true optimum is closer to
  uniform, because richer attacks (multi-class, cross-level) tighten the LB further.
* Realising even part of it needs a new WHIR soundness theorem for non-uniform queries. WHIR's
  analysis assumes uniform shift queries.
* An informal check: a natural clustered design (8 level-6 subtrees × 9 queries) loses ≈ 170 bits
  of soundness to a "concentrate agreement in 8 subtrees" attack (miss ≈ 2^-98 instead of
  ≈ 2^-268).
* **Conclusion:** within Merkle commitments, optimal multiproofs over uniform queries are
  near-optimal. **KILL** clustering.

## 2. Constructions that might beat it — verdicts

Baseline: final layer at c_sha = 12k (444,481 B; auth 188,736 B).

| # | idea | result | verdict |
|---|---|---|---|
| 2.1 | **Correlated or structured positions within a round** (blocks, intervals, expander walks) | The adversary aligns agreement with the correlation structure. A block of g queries gives about the soundness of one query. Upper bound on any gain: ≤ 22.5 KB (§1.3), unrealisable without a new soundness proof. | **KILL** |
| 2.2 | **Positions reused across WHIR rounds** (round i+1 queries derived from round i) | WHIR samples round-i shift queries *after* f_{i+1} is committed and *before* f_{i+2} is committed. Deterministic reuse reveals round-(i+1) positions before f_{i+2} is committed, so the prover cheats on known positions. Marginally fresh but correlated queries leave the trees separate, so no path is shared. | **KILL** (unsound / 0 B) |
| 2.3 | **One tree for several rounds' oracles** | f_{i+1} depends on round-i folding randomness, which comes after f_i's root, so oracles from different rounds cannot share a tree. Even a hypothetical merged tree saves only the per-tree root: ≤ 4 digests ≈ 192 B, because each round's queries stay in its own subtree. Same-round oracles (stacked columns) are already one tree in SWIRL. | **KILL** |
| 2.4 | **FRI-style "consistent queries" across layers** | The per-layer path is still paid in each layer's own tree. WHIR's decreasing q_i already beats the constant q of FRI. The useful part, the 2^k coset in one leaf, is already in the model. | **KILL** (already in) |
| 2.5 | **Tree caps** on top of an optimal multiproof | The best cap level is 0 for all four rounds (change +0.00 digests). The multiproof already shares the top levels. A cap at level ≈ log q is *free*, and it is the enabler for weak binding (§3). | **KILL** as a size lever |
| 2.6 | **Arity** | Expected multiproof digests: round 1 (q=69, d=26) 1,312 binary vs 1,950 4-ary; q=55 844 vs 1,252; q=46 672 vs 1,521 8-ary. Binary minimises (a−1)/log₂a. (4-ary helps *in-circuit* cost; see §3.) | **KILL** for proof bytes |
| 2.7 | **Larger leaves vs depth** | One Ext12 value (48 B) costs the same as one digest. Moving a level into the leaf adds 2^k values to save one digest. Already optimised jointly with k in the model. First-round width/k1 is the separate lever already listed. | **KILL** (already optimal) |
| 2.8 | **Grinding for a small multiproof** (accept FS positions only if multiproof ≤ T) | Soundness falls by z = log(1/Pr[P]) bits, so ≈ z/b extra queries are needed. Simulation (20k samples): multiproof std ≈ 10.6 digests (q=69, d=26) and ≈ 8.6 (q=46, d=21). At z = 2/4/8, saving 13.5/21.8/34.6 digests vs cost ≈ 6.5 digests per bit (path plus 8 Ext12 leaf values per extra query). Net ≥ 0 everywhere, best ≈ break-even. | **KILL** |
| 2.9 | **Sampling without replacement** | q²/(2M) ≈ 0.01 duplicate queries per round at M ≥ 2^17. Negligible. | **KILL** |
| 2.10 | **Ron-Zewi–Rothblum** (local proofs near witness length; proving as fast as computing) | Shrinks IOP oracle length or prover time, not argument size or path length. | **N/A** |
| 2.11 | **Constant-size hash-only proofs, proof-carrying hash, Micali** | None exist. HNY22 conditionally rules out o(log t·log(t/ε)). Micali is O(λ² log n). | **KILL** |
| 2.12 | **Accumulation in place of openings** | Covered in the log (iter. 4): the decider still opens WHIR. Recursing the openings into an inner proof is the same fixed point. | **KILL** |

## 3. The PROMISING lever: weak binding → narrower digests

### Mechanism (classical, proven [P])

**CY tight Micali (2021/188):**
* With per-node domain separation (position index in each node hash), soundness is
  t·ε + 12·l·log|Σ|·t/2^λ, for λ ≥ 2 log t + 6.
* Collisions are survivable. Only inversions of the root or nodes cost the ε-level term, and only
  linearly in t.

**CY subquadratic (2021/281):**
* Chop the tree at a cap of ≈ q nodes (free with multiproofs, §2.5), domain-separate every node,
  and use a "permuted robust" PCP.
* Each collision doubles the adversary's candidate strings, and each inversion frees one cap block.
* Both are paid for by robust soundness.
* The digest then drops to λ = 2 log t + log β + 3 ≈ 139 bits at t = 2^64 (classical).
* Their Table 1 at (2^64, 2^-128): 346 → 188 KB.

### Our transfer (all [I]/[O])

* Quantum collision and "inversion of a prior input" events: the analogue of t² is t³ (BHT/Zhandry
  collision bound; inversions of the t prior-trace targets are collision-like).
* Plausible requirement for the capped version: n ≈ 3·64 + log β + c ≈ **200–210 bits → 26 B**,
  or 28 B with margin. Here β is the robustness ratio: freeing a cap block frees ≤ L ≈ 2–3 queries,
  so the cost per inversion is ≈ L·b + log(cap) ≈ 20 bits.
* Uncapped version (tight-Micali analogue): root/node inversion with Grover over M ≈ 2^27 targets,
  t²·M/2^n ≤ ε → n ≳ 283 → **36 B**.
* WHIR is an easy case for the "permutation" step: its shift queries are already uniform, so cap
  blocks receive ≈ 1 query each (max load ≈ 3 at 2^{i*} ≈ q, ≈ 2 at 4q).
* WHIR's per-query fold checks are independent repetitions. That is exactly the "repeated PCP"
  structure CY prove robust (Lemma 2.3) **[I]**.

### Quantified with the calibrated model

`digest.py`: fixed point re-solved per configuration, final layer with digest D.
"pen 4-ary" means the penultimate tree is 4-ary. This is valid only if the penultimate digest is
≤ 26 B, so that 4·26 + 17 B padding + 7 B index fits one 128-B SHA-512 block. It halves in-circuit
path compressions and so shrinks the final circuit (2^26.8 → 2^26.3 cells at 12k).

| c_sha | config | 48 B | 42 B | 36 B | 32 B | 28 B | 26 B |
|---:|---|---:|---:|---:|---:|---:|---:|
| 12k | today (268, m=8) | 444,481 | 417,983 | 388,157 | 368,273 | 348,389 | 338,447 |
| 12k | today + pen 4-ary | — | — | — | — | — | **320,751** |
| 12k | levers (z=32, pen 236 / fin 226) | 376,145 | 355,883 | 332,457 | 315,321 | **298,185** | **289,617** |
| 12k | levers + pen 4-ary | — | — | — | — | — | **276,217** |
| 24k | today | 527,161 | 493,351 | 459,541 | 437,001 | 414,461 | 403,191 |
| 24k | levers + pen 4-ary | — | — | — | — | — | 319,149 |
| 32k | today | 570,313 | 536,503 | 502,693 | 478,465 | 452,533 | 439,567 |
| 32k | levers + pen 4-ary | — | — | — | — | — | 341,613 |

(The 26 B column of the "today" and "levers" rows uses a binary penultimate tree, so it is
conservative.)

**Best achievable hash-only final layer under Hypothesis B:**
* ≈ **276–290 KB** at c_sha 12k with 26 B digests plus the existing levers;
* ≈ 320–340 KB at 24–32k;
* ≈ 338 KB at 12k with *no* other lever.

### Open lemmas — all must close before this is usable under U-2 "proven bounds only"

* **L1 [O]** QROM version of the CY scoring lemma. Bound the probability that a t-query quantum
  adversary's (compressed-oracle) trace contains k domain-separated collisions or prior-input
  inversions by (c·t³/2^n)^k. Partial tools: Liu–Zhandry multi-collision bounds;
  Hamoudi–Magniez multiple-collision-pair bounds; CMS19 compressed-oracle Merkle analysis. The
  classical "query trace" argument does not transfer verbatim.
* **L2 [O]** Extend CY21's cap-soundness game from PCPs/Micali to multi-round BCS: one capped tree
  per round, FS transcript chaining, state restoration (t² Grover factor), plus OOD and sumcheck
  messages, which are unaffected by tree attacks.
* **L3 [O/I]** Block-wise ("permuted") robust round-by-round soundness for WHIR's shift-query step.
  Claim: ε_i(d) ≤ C(2^{i*}, d) · α^{q_i − L·d}, with L the max cap-block load. This looks
  elementary given uniform queries, but it must be combined with the MCA/list-decoding round error
  (Bordage–Chiesa–Guan–Manzur Thm 9.2) and WHIR's own soundness theorem, which is itself still open
  per the log.
* **L4 [O]** Transcript and FS hash: collisions in the sponge state at n ≈ 208 bits are also
  "1-bit forks". Either cover them in the same game or keep the transcript state at full 384 bits
  (no proof-size cost; roots stay in transcript).
* **Spec impact:** this amends U-7 (digest ≥ 336–384 bits). User decision: it is a *proof-technique*
  change, not a new assumption class. Same SHA-384, truncated output, per-node position
  domain-separation, capped trees.

### Quick ranking of the remaining work

1. L1 + L2 in the QROM: a research paper's worth of work. It is the only hash-only path to < 300 KB
   found here.
2. A cheaper interim step: the uncapped tight-Micali analogue at 36 B (≈ 388 KB today at 12k, 332 KB
   with levers) needs L1-style inversion accounting but no robustness lemma.
