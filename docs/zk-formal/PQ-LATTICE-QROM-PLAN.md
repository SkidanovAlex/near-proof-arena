# QROM knowledge soundness for an Akita-type lattice final wrap: scope, attack plan, go/no-go (track L2, milestone 1)

Date: 2026-10-17. Lane `lane/pq-lattice-qrom`. This is a research plan, not a proof. Nothing here is a
security certificate.

Inputs:
* `docs/zk-formal/PQ-LATTICE-WRAP-STUDY.md` (option L2);
* `research/near-compression/lattice-study/{A,B,C}.md`;
* V3-D3A-STUDY §D (U-2, U-6, U-7, U-8) and §11.2;
* `docs/logs/pq-final-layer-model-2026-10-17.md`.

Papers read for this milestone (pdftotext copies in the session scratchpad):
* Akita, ePrint 2026/1983: §§3.1–3.8, 4.2–4.5, 5.5, 8.2, 9.5, 10, 12, 13, App. C, D.3, E, H;
* CMS19 2019/834; DFM20 2020/282; BGTZ23 2023/1256; AFK22 2021/1377; AFKR 2023/1945;
* LMS22 2022/889; CMNW 2024/281;
* Rotem–Tessaro 2024/1724;
* Chiesa–Dall'Agnol–Di–Guan–Spooner 2025/947 (arXiv 2411.05360);
* DFMS22 commit-and-open (arXiv 2202.13730);
* Majenz–Sharma, Fischlin in the QROM (arXiv 2602.17307, abstract only).

**Tags:**
* **[P]** proven in the literature (theorem cited);
* **[O]** open (stated open in the literature, or no result found by our search);
* **[I]** our inference or estimate, unverified.

---

## 0. Verdict in one paragraph

**No proof route available today yields a contract-compliant bound** (≤ 2⁻¹²⁸ against 2⁶⁴ quantum SHA-384
queries, proven) for an Akita-type wrap. The obstruction is structural, not a matter of constants:

* Akita's commitments are **compressing Ajtai images**: a 128-byte commitment covers 2³⁰ coefficients
  (§4.5) [P].
* So the committed witness is not determined by the transcript or the RO database. The only meaningful
  property is **knowledge** soundness, because the "language" of short openings is essentially everything.
* Knowledge must come from **rewinding**, i.e., coordinate-wise forks of the fold challenges.
* The QROM tools with explicit losses either:
  * need a straight-line, database-readable witness (CMS19 and its lifting lemma, the Unruh/Pass transforms);
  * or lose exponentially in the number of Fiat–Shamir rounds (DFM20).

  Akita plus a sumcheck front end has **≈ 400–700 challenge rounds** [I].

Quantum-rewinding results (LMS22, CMNW) are interactive only, and have two limits:
* they need **MLWE** (for collapsing) in addition to MSIS;
* they give only **1/poly extraction slack** with poly(1/slack) runtime, which is unusable at 2⁻¹²⁸ [P/I].

**Most promising route [I]:** a *hybrid lifting theorem*, built from three pieces:
* (i) CMS19-style compressed-oracle bounds (t²·ε) for every **statistical** round (the sumcheck, batching and
  ring-reduction challenges), relative to an idealised extractable commitment;
* (ii) a new **QROM tree-extraction lemma** for the few (≈ 4–8) **computational** fold rounds, with losses
  *additive* across folds and expected-time (not 1/poly) extraction;
* (iii) a collapsing argument for Ajtai maps under MLWE.

Piece (ii) is the open core [O].

**Size if it works:** with an explicit-constant t² theorem and ≈ 192–228-bit MSIS, the wrap estimate is
**≈ 180–230 KB** (§3.6). That fits < 300 KB.

**Go/no-go:** go only if (ii) closes with:
* polynomial and additive round losses;
* extraction overhead ≤ 2⁴⁰·T_A;
* assumptions within {MSIS, MLWE} at ≤ 224 quantum core-SVP bits.

Otherwise the lattice wrap can only be adopted under option L1 (a relaxed contract for the last layer).

---

## 1. The exact protocol under study

### 1.1 Stack

`Π_wrap = FS^H[ PIOP ∘ Akita ]`, where:

* **Statement** (wrap study §1): "I know a penultimate SWIRL proof π that the fixed SWIRL verifier accepts."
  This is ≈ 9–12k SHA-384 (SHA-512-compression) evaluations plus ≈ 6×10⁴ Ext12 multiply-equivalents, i.e.
  **≈ 2²⁷–2³⁰ base-field witness elements** [I].
* **Front end (PIOP):** a Lattice-Jolt-style sumcheck PIOP over a **uniform** circuit:
  * Spartan-style R1CS/CCS sumchecks;
  * lookup or GKR sumchecks for SHA-512 word operations and BabyBear-Ext12 emulation (B §2);
  * claim reductions to one batched multilinear opening.

  Jolt's RISC-V-specific Twist/Shout machinery is replaced by our fixed circuit. The PIOP's oracle is the
  committed witness polynomial(s).
* **PCS:** Akita (Dao, Bodaghi, Khajehpour, Vitto, …, Thaler; ePrint 2026/1983), opened in one heterogeneous
  batch exactly as in Jolt (Akita App. E.2–E.3).
* **FS hash:** SHA-384 (U-7), modelled as a QRO. Akita ships SHAKE-based XOF streams. Re-instantiating them with
  SHA-384 in counter mode is an engineering change. Because this is the **final** layer, the FS hash is
  never arithmetised: only native SHA-384 cost is paid [I].

### 1.2 Akita parameters as published [P]

| item | value | source |
|---|---|---|
| ring | R_q = Z_q[X]/(X^d+1), d a power of two, q ≡ 2s+1 (mod 4s) (minimal split s = 2: q ≡ 5 mod 8) | §3.1 |
| moduli (implementation) | p32 = 2³²−99, p64 = 2⁶⁴−59, p128 = 2¹²⁸−2³²+22537 | §13.1, App. I |
| opening / challenge field E | F_{q^k}, k a power of two dividing d/s; k = 4, 2, 1 for p32/p64/p128, so **\|E\| ≈ 2¹²⁸** | App. H |
| fold challenge family | sparse ±a shells; certified operator-norm filters: d = 64 shell (31 × ±1, 11 × ±2), **log₂\|C_acc\| ≥ 128.06**; d = 128 shell (31 × ±1), **≥ 128.56** | §3.2, App. D.3 Table 12 |
| challenge invertibility | every nonzero difference with ‖c̄‖∞ ≤ 2c_max < q^{1/s}/√s is a unit (LS18) | §3.1–3.2 |
| MSIS target | every instance ≥ 128-bit **quantum** ADPS16 core-SVP (0.265β, LGSA); family-wide union λ_fam > 125; compression maps 147–153 bits | App. C |
| FS claim | **classical ROM only**; "QROM security is outside the scope … future work" | §1.1, §10, §10.2, §14 |
| shipped FS target | "128-bit classical-ROM transcript target" | App. H Table 14 |
| measured size | 61.3–67.3 KB opening (p32, N = 2²²–2³⁰), 68–72 KB for p64/p128; Jolt proofs 85.9–98.1 KB | Tables 8, 10 |

**Observation [I].** Corollary 10.34 caps the provable FS strength at log₂\|E\| − log₂ c − log₂(Q_max+1) for any
error term c/\|E\|. With \|E\| ≈ 2¹²⁸ and fold denominators ≈ 2¹²⁸, Theorem 10.33 therefore cannot certify
2⁻¹²⁸ for any Q_max ≥ 1. The shipped "128-bit" target must rest on transcript grinding (Prop. 10.3, which the
theorem explicitly does not credit) and/or a small Q_max. We did not find the production Q_max in the paper;
check the artifact. Under our contract the published parameters are short even **classically** (C §Q1).

### 1.3 Round ledger of one Akita fold (Fig. 5) and its per-round errors (eq. 218–223) [P]

Notation:
* µ′ = extended-witness variable count at the level;
* d_s = range-tree stage degrees;
* m_s = frontier sizes;
* W_{j,g} = fold-challenge coordinates (claims × blocks);
* n_j = relation rows.

Every field challenge is uniform in E or a power of E.

| # | stage (Fig. 5) | challenge space | interactive (knowledge) error charged | extraction structure | soundness type |
|---|---|---|---|---|---|
| 0 | tensor reduction (evaluation-trace folds, k > 1): row/claim batching, then m rounds of degree-2 sumcheck | E^κ (nested), E per round | ε_tensor,h (eq. 220); grouped claims (N_clm−1)/\|E\| (eq. 221) | nested tree 2^κ, then 3 per round | statistical given committed partials |
| 1 | bind partial evaluations (D image or compressed H payload) | none | none | — | binding of D, F, H: **computational (MSIS, ℓ∞ bound b−1 or 1)** |
| 2 | root public batching ζ_batch (root only) | E | (Λ−1)/\|E\| (eq. 222) | Λ-ary | statistical |
| 2′ | **fold challenge tuple** (c_{g,c,i}) with response grinding nonce | C_acc^W (sparse ring elements, \|C_acc\| ≈ 2¹²⁸) | **W_{j,g}/\|C_acc\|** (CWSS, eq. 217) | flat coordinate-wise, k = 2 per coordinate, factor 1+W | **computational**: two siblings give a weak opening via cross-multiplication, or a short kernel vector of A (MSIS) |
| 3 | bind successor witness (B-commitment, compression) | none | none | — | binding of B, F, H: **computational** |
| 4 | optional squared-norm claims | none | — | — | — |
| 5a | ring-reduction α | E | ξ_ring/\|E\| | ξ-ary | statistical given commitments |
| 5b | relation-row batching τ₁ | E^{⌈log n⌉} | ⌈log n_j⌉/\|E\| | nested binary tree 2^{⌈log n⌉} | statistical |
| 5c | range anchor τ₀ (+ binary-support anchor) | E^{µ′} | µ′/\|E\| (+ β µ′/\|E\|) | nested binary tree 2^{µ′} | statistical |
| 5d | range-tree sumcheck stages s = 1..S (degree d_s+1 ∈ {3, 5}) and frontiers | E per round | Σ µ′(d_s+1)/\|E\| + Σ (m_s−1)/\|E\| (eq. 216) | (d_s+2)-ary per round | statistical |
| 5e | relation/range batching, binary batching, norm-claim binding | E | (1 + β + ν_j)/\|E\| | — | statistical |
| 5f | fused relation sumcheck (degree 3, µ′ rounds) | E per round | 3µ′/\|E\| | 4-ary per round | statistical |
| 6 | setup-product sumcheck (offloaded edges, degree 2) | E per round | 2 log N_setup/\|E\| (eq. 219) | 3-ary per round | statistical; setup binding is computational |
| T | terminal: tensor prefix, clear partials, fold tuple, reveal z | C_acc^{B_term}, E | ε_term (eq. 211) | flat k = 2 | computational (A_term binding) |

What the published theorems give [P]:
* **Interactive bound:** ε_int(sch) = Σ_j ε_j^sch + ε_tensor + ε_grp + ε_term + ε_batch (eq. 223). The
  extractor needs the full mixed transcript tree, of size Tree(sch) = Π_r b_r (eq. 225), which includes
  nested 2^{µ′} stages. It returns an exact batch witness **or** a short kernel vector for one matrix view
  (Thm 10.31).
* **Classical ROM bound:** Pr[accept ∧ extraction fails] ≤ (Q+1)·ε_int + Δ_setup + Σ_I Adv^MSIS(B_I), with
  T_{B_I} ≲ (Q+1)·poly(Tree, T_A, …) (Thm 10.33, eq. 227–229). The proof uses Lemma 3.22, a mixed-tree
  generalisation of AFK22/FMN24 §8 with *additive* per-stage losses.
* **What the extracted witness is:** a valid algebraic decommitment, not the canonical short one (Remark 10.32).
  The evaluation relation (57) is exact over the base field K. Exact-witness extraction of the *application*
  relation is therefore a front-end design obligation (C §Q2) [P/I].

**Round count [I].** The schedule has ≈ 4–8 nonterminal folds at 2³⁰ (O(1 + log(log N / log L)), §9.4). Each
fold has ≈ 3–5 sumcheck stages of µ′ ≈ 15–30 rounds, so the PCS alone has ≈ 300–600 challenge rounds. The
PIOP adds ≈ 60–120 more (two or three 30-round sumchecks plus lookup/GKR layers).

### 1.4 Front-end rounds (generic Spartan/Jolt-style) [P for the sumcheck bound]

* **Sumcheck** over µ variables, individual degree ℓ: per-round error ℓ/\|F\|, total µℓ/\|F\|. It is
  (ℓ+1)-special sound per round (Akita Thm 3.7).
* **Batching and selectors:** (t−1)/\|F\| or s/\|F\| (Lemma E.1).
* **Lookups (Shout/GKR-style):** a product of sumchecks of small degree.

All of these are **statistical** (IP-style) given oracle access to the committed polynomial. Jolt uses the
128-bit field (\|F\| ≈ 2¹²⁸); the PIOP also needs ≥ 2²⁶¹ under a t² QROM route (§3).

---

## 2. Target theorem (to be proved; statement only)

**Model.** H = SHA-384 is a QRO H: {0,1}* → {0,1}³⁸⁴, and all domain separation goes through one oracle. FS
challenges are derived by counter-mode expansion with rejection sampling; this is Akita's "ideal coordinate
stream" (Lemma 10.2), lifted to the QROM. The setup seed is expanded by a domain-separated H_setup (Δ_setup as
in eq. 67).

A is a quantum oracle algorithm. It makes ≤ t = 2⁶⁴ queries to H, counting every response-grinding and
proof-of-work probe, and has circuit size ≤ T_A. **Contract gap [I]:** U-6 bounds only queries. An MSIS/MLWE
term needs an explicit time bound T_A, which is a **user decision** (§4).

**Theorem (target, [O]).** For every such A, there is a quantum extractor E with oracle access to A. E may
record and reprogram H (compressed oracle) and rewind A coherently. Its expected size is
T_E ≤ X_ext·T_A with X_ext explicit. There are also quantum adversaries B_I (MSIS, one per matrix view
I ∈ 𝓘(sch)) and B_LWE (MLWE, collapsing), each of size ≲ T_E, such that

```
Pr[ V^H(x, π) = 1  ∧  (x, E^A) ∉ R_wrap ]
   ≤  C · t^a · max_r ε_r                         (statistical rounds, QROM lifting)
    + F_fold(t, ε_fold)                           (computational fold rounds; additive over folds)
    + Σ_I Adv^MSIS_I(B_I) + Adv^MLWE(B_LWE)        (binding / collapsing)
    + O(t³ / 2³⁸⁴)                                (SHA-384 collisions in transcript binding)
    + Δ_setup
   ≤  2⁻¹²⁸,
```

where:
* R_wrap is the **exact** wrap relation: an accepting penultimate SWIRL proof, with exact BabyBear/SHA-384
  semantics enforced by range and bit constraints in the circuit;
* ε_r is the per-round interactive error of statistical round r (§1.3, §1.4);
* ε_fold = W/\|C_acc\| per fold coordinate group.

Targets for the explicit constants:
* a = 2 and C ≤ 6, matching CMS19's ω*_D(G_BCS, t) ≤ 6(t²ε + 4t³/2^λ) [P, CMS19 §8.5];
* F_fold(t, ε) ≤ C′·t²·Σ_folds ε_fold (additive);
* X_ext ≤ 2⁴⁰;
* the slack is a fixed term ≤ 2⁻¹³⁰, **not** an inverse polynomial.

**Composition.** R_wrap's witness π is a SWIRL proof whose own soundness is a QROM argument about the same
oracle evaluated **in-circuit**. The composition needs an oracle-relativised (AROM-like) QROM model. This gap
is shared with the hash-only design (C §Q2.3) and is out of scope here [O].

---

## 3. Proof-strategy candidates

### 3.1 (a) Round-by-round soundness plus a CMS19/BGTZ23-style transform

What exists [P]:
* **CMS19:** the BCS compilation of an IOP with *statistical* rbr soundness ε is QROM-sound with error
  6(t²ε + 4t³/2^λ). With rbr *knowledge* it is QROM-knowledge-sound with error O(t²κ + t³/2^λ), via a
  straight-line extractor that reads the IOP oracles from the compressed-oracle database. The engine is the
  lifting lemma ω* ≤ O(t²·I(P_G, t)): quantum success ≤ t² × classical per-query instability of a
  **database predicate**.
* **BGTZ23:** (k₁..k_µ)-special soundness implies rbr soundness, with ε_i = (k_i−1)/\|C_i\|. Special soundness
  does **not** imply rbr knowledge (Thm 1.3).

Where it breaks for Akita [I, the central structural point]:
1. **There is no statistical state function.** CMS19's "doomed" predicate must be a function of the RO
   database. In BCS the oracles are SHA-Merkle-committed, so their contents sit in the database. In Akita the
   witness sits behind a compressing Ajtai map: 2³⁰ coefficients → 128 B, with many short openings per
   image. Whether a partial claim is "true" depends on which opening the prover has in mind. It is not
   defined information-theoretically.
2. **Soundness without knowledge is vacuous.** Extraction outputs a witness **or an MSIS solution**
   (R_∨ := R ∪ {short kernel vectors}). The language L(R_∨) is all instances, since compressing matrices
   always have short kernel vectors. For a compressing PCS, even L(R) is essentially all (cm, r, v). So
   BGTZ23 plus CMS19 soundness says nothing; we need **knowledge**.
3. **rbr knowledge is impossible here.** rbr knowledge needs a witness readable from (x, transcript prefix,
   next message). The witness is ≫ the transcript and hidden behind Ajtai images, so no such extractor exists,
   information-theoretically.
4. **The recursion needs knowledge anyway.** R_wrap's in-circuit hash is concrete SHA-384, so accepting
   penultimate proofs for false statements exist. Only extraction (knowledge) gives end-to-end soundness.

**The bridging lemma one would want** ("computational rbr soundness"): if A turns a doomed state into a
non-doomed one with probability > t²ε, then an efficient B finds two distinct short openings of one
commitment (MSIS). Producing two openings needs a fork, i.e., rewinding. So the bridge is itself a **QROM
forking/rewinding lemma** [O]: (a) alone cannot close the gap. Two parts of (a) remain useful:
* **L-stat** (provable with current tools [I]): QROM knowledge soundness of PIOP + all intra-fold algebraic
  rounds, relative to an *idealised extractable commitment* (a hybrid in which committed vectors are
  supplied by an oracle the extractor can read). This is CMS19's lifting with per-round ε_r ≤ 2⁻²⁵⁸·⁶.
* **L-bridge** [O]: replace the idealised commitment by Ajtai plus a fold-level extractor (strategy b).

**Required per-round error (t² route) [I, from CMS19's constant 6]:** 6·t²·ε ≤ 2⁻¹²⁸ gives
ε_r ≤ 2⁻²⁵⁸·⁶ per round. This is the **max** over rounds, not a sum: CMS19 bounds a per-query instability.
* Algebraic rounds: \|E\| ≥ 2^{258.6 + log₂(degree ≤ 5)} ≈ **2²⁶¹**. Akita embeds F_{q^k} only for power-of-two
  k. Supported primes give 2²⁵⁶ (k = 8 over p32, k = 4 over p64, k = 2 over p128; **just insufficient**) or
  2⁵¹² (4× the field bytes). A custom q ≈ 2⁶⁶–2⁶⁸, q ≡ 5 (mod 8), with k = 4 gives 2²⁶⁴–2²⁷² (×2.1 the bytes
  of today's 128-bit E) [I]. Grinding could cover the few missing bits, but under a fixed query budget its
  QROM accounting needs its own proof [O].
* Fold rounds: \|C_acc\| ≥ 2^{258.6 + log₂ W}, i.e. ≈ 2²⁶⁸ for W ≈ 2⁸–2¹⁰. A d = 256 weight-64 ±1 shell has
  log₂\|C\| = 267.6 [I, computed]. Its ℓ₁ mass ω = 64, against 31–53 today, roughly doubles the response
  envelope and the A collision radius.

### 3.2 (b) DFM20 measure-and-reprogram plus quantum rewinding

[P] DFM20 reduces any n-challenge-round FS prover to an interactive prover, losing (2t+n+1)^{2n}, and O(t^{2n})
is optimal in general. Knowledge then needs a **post-quantum interactive** extractor:
* **LMS22** (lattice Bulletproofs; recursive special soundness plus last-round collapsing; **Ring-LWE**):
  * extractor size P(t, k, log 1/δ, 1/ν)·(ck)^{t−i};
  * slack ν = 1/poly;
  * knowledge error 2 log ℓ/φ(m);
  * explicitly leaves the QROM open.
* **CMNW** (2024/281) extends this to **coordinate-wise** special soundness, using BBK22 stateless simulation
  and collapsing of the SIS hash under **LWE** (LZ19, LMZ23):
  * knowledge error ℓξ/\|S\| + 1/poly(λ);
  * extractor size Σ 2n^{2i}(2ξ+2)^i, super-polynomial for log-round protocols;
  * its QROM step is literally DFM20, so only constant-round protocols are covered (CMNW App. B.6).
* **Chiesa–Dall'Agnol–Di–Guan–Spooner** (2025/947): interactive BCS with **collapse-binding** vector commitments
  is post-quantum (knowledge) sound with error κ + negl. This is a multi-round rewinding technique for
  computationally binding commitments, but in the standard model and interactive only.
* **Module collapsing:** Ajtai (M)SIS maps are collapsing under (M)LWE (LMZ23; module variant in Jackson–Miller–Wang,
  arXiv 2312.16619) [P].

Is Akita (k₁..k_µ)-special sound? Its folds are **coordinate-wise** 2-special sound (flat, factor 1+W). Its
batching stages are **nested** interpolation trees (2^{µ′}, 2^κ, 2^{⌈log n⌉} leaves). Its sumchecks are
(ℓ+1)-special per round. The structure is a mixed CWSS tree (Lemma 3.22), not plain (k₁..k_µ) special
soundness. It also holds only **computationally**: the extractor may output an MSIS solution [P: §3.8,
Lemma 10.28, Thm 10.31].

Assessment [I]:
* With n ≈ 400–700 FS rounds, DFM20's loss is ≈ 2^{130n}. **Dead**, even if folds were the only rounds that
  needed rewinding, because DFM20 counts every FS round.
* The quantum extractors give 1/poly slack, and runtime poly(1/ν)·(ck)^{rounds}. At ν ≤ 2⁻¹²⁹ the MSIS
  reduction would run in time ≥ 2^{129·deg}, which no MSIS parameter set survives (§4).
* A **concrete, expected-time** quantum extractor is needed, analogous to "guaranteed extraction" in
  Lombardi–Ma–Spooner 2021/1543 for collapsing Σ-protocols. None exists for multi-round CWSS [O].
* Using (b) only on a ≤ 2-fold variant still costs (2t+1)^{2·n_f} ≈ 2^{260} at n_f = 2. Fold challenges would
  then need ≈ 2⁻³⁹⁰, and a 2-fold Akita has a large tail.

Size impact (if it worked at n_f = 2): fold families ≈ 2⁴⁰⁰ (d = 512, ω ≈ 100), a large terminal response, and
the statistical rounds still on the t² route. ≈ 300–500 KB [I, low confidence]. **Not promising.**

### 3.3 (c) Straight-line extraction (Fischlin, Pass/Unruh, hash-committed witnesses)

* **Rotem–Tessaro 2024/1724** [P]. Multi-round Pass transform: Merkle-commit a full transcript tree of degrees
  (n₁..n_s), open one RO-selected path, repeat for λ. It is QROM knowledge-sound with no super-polynomial loss.
  Its multi-round Fischlin analogue has **no** QROM proof and needs ≤ Θ(log λ / log log λ) rounds.

  Cost for Akita: prover work and tree size Π n_i ≥ 3^{rounds} with ≈ 400+ rounds, so it is
  **infeasible** [I]. The proof would also repeat the whole ~70 KB transcript path λ/log(n) times, i.e.
  **MBs** [I].
* **Unruh / DFMS22 (succinct Unruh), Majenz–Sharma 2026 (Fischlin in the QROM)** [P]: three-move Σ-protocols only.
* **Hash-commit the witness** so that E reads it from the database. Two variants:
  * (i) Merkle-commit the 2³⁰-element witness with SHA-384 and prove consistency with the Ajtai opening by
    random spot checks. That is a hash-IOP query phase: at 2⁻²⁵⁸ per-round need, ≈ 100–250 queries × ≈ 1.4 KB
    paths ≈ **150–350 KB**, which defeats the purpose [I].
  * (ii) Hash π inside the circuit. The circuit's SHA-384 is concrete, not the oracle, so E would still need
    lattice knowledge extraction to obtain a *second* preimage. No shortcut [I].
* **Trapdoor straight-line extraction:** program the setup matrix to a trapdoored or LWE-injective one.
  Compressing Ajtai maps have no unique opening to decode, and an injective root commitment would be the size
  of the witness. Infeasible [I].

**Verdict: (c) is not viable for an Akita-sized round structure.**

### 3.4 (d) 2025–2026 literature search

Searched: ePrint/arXiv/web, "QROM" × {lattice, succinct argument, Fiat–Shamir, multi-round, folding, LaBRADOR,
Greyhound, LatticeFold, Akita}, plus quantum forking/rewinding for multi-round protocols.

| work | what it proves | gap for us |
|---|---|---|
| Akita 2026/1983 | classical-ROM KS with additive mixed-tree losses; MSIS at 128-bit quantum core-SVP | "QROM … future work"; §14: "promising progress … does not seem to fully transfer" [P] |
| CMNW 2024/281 | first PCS with KS vs quantum adversaries (interactive; LWE for collapsing); QROM via DFM20 | constant-round only; 1/poly slack; MB-size proofs [P] |
| Chiesa et al. 2025/947 | interactive BCS + collapse-binding VC is post-quantum (knowledge) sound | interactive, standard model; semi-adaptive IOPs [P] |
| Rotem–Tessaro 2024/1724 | first multi-round transform with QROM KS, no super-polynomial loss | exponential tree, so infeasible for many rounds [P] |
| AFKR JoC 2025 (2023/1945) | (Γ₁..Γ_µ)-special soundness, FS loss (Q+1)κ, classical | says quantum counterparts "do not have closely-matching" results (yet) [P/O] |
| BGTZ23, CMS19 | special soundness ⇒ QROM soundness after BCS (statistical IOPs) | no knowledge; no computational commitments [P] |
| LaBRADOR / Greyhound / LatticeFold(+) / Neo / RoK* / Hachi / RoKoko | classical ROM, heuristic FS, or no FS analysis | no QROM theorem found (C §Q1) [O] |
| DFMS 2021/280 (online extractability), DFMS22 (commit-and-open), Majenz–Sharma 2602.17307 | QROM straight-line extraction for hash-committed Σ-type protocols | Σ-protocols / commit-and-open only [P] |

**No 2025–2026 paper proves QROM (knowledge) soundness with explicit bounds for any multi-round lattice
SNARK or folding scheme** [O]. This is the same conclusion as research report C, now checked against Akita
and the 2025/947 and 2024/1724 lines.

### 3.5 Recommended strategy: hybrid lifting (a + b′) [I]

1. **L-stat (feasible).** Model the commitment as an idealised extractable oracle. The PIOP and all algebraic
   rounds of every fold form a public-coin protocol with statistical rbr knowledge soundness *relative to the
   committed vectors*. Lift with CMS19 for a 6t²·max ε_r bound. This is paper work on known tools; it is also
   exactly what the hash-only track needs (shared QROM machinery).
2. **L-fold (open core).** Replace the idealised commitment by Ajtai commitments plus the fold challenges. Prove
   a QROM **tree-extraction lemma** for coordinate-wise 2-special-sound fold rounds:
   * the extractor records the database (compressed oracle) and, per fold level, reprograms only that level's
     fold-challenge query (measure-and-reprogram with AFK-style matched-index accounting, Lemma 3.22's
     recursion, quantised);
   * it rewinds coherently using collapsing of the Ajtai maps (MLWE), with CMSZ21 state repair or
     guaranteed-extraction ideas;
   * targets: additive loss C′t²Σ_folds W/\|C_acc\|, expected size X_ext·T_A, and no 1/poly slack.
3. **L-collapse.** Collapsing of each Akita matrix view (A, B, D, F, H, shared-prefix setup) under MLWE, with
   explicit losses: an LMZ23-style hybrid over the views. Note that it **adds the MLWE assumption** next to MSIS.
4. **L-compose.** Akita's strong–weak nested invariant (Thm 10.31, Cor. 10.17) must be re-proved with
   quantum-extracted subtrees. This is where classical "two extractions under the same commitment agree,
   else collision" needs a quantum analogue: a collapse-binding consequence.

**Why this is the most promising [I].**
* It isolates the open part to ≈ 4–8 computational rounds with a clean algebraic structure: flat k = 2 per
  coordinate, commitments collapsing under MLWE.
* Everything else rides on CMS19, which is proven and has explicit constants.
* L-fold is a natural quantum generalisation of two proven results: Akita's classical Lemma 3.22 and CMNW's
  interactive CWSS extractor.

**Main risk.** The quantum literature has repeatedly found that tree-structured rewinding costs a
multiplicative factor per level (DFM20 optimality; LMS22's (ck)^t). Additivity across folds may be false in
general, or need extra structure. A negative result is possible.

### 3.6 Proof-size impact on the wrap (start: 64–72 KB PCS at 2³⁰ [M], full Jolt proofs < 100 KB [M])

Assumed breakdown [I, unmeasured; measuring it is milestone M2]:
* Akita: ≈ 50 % extension-field bytes (sumcheck messages, partial evaluations, frontier claims) and ≈ 50 %
  lattice bytes (compressed commitments, terminal response z, inner state t, digits);
* PIOP: ≈ 25–35 KB, all field elements (Jolt total minus PCS).

Scaling rules [I]:
* field bytes scale with log₂\|E\|;
* lattice bytes scale ×(1.3–1.5) for MSIS 192–228 (rank ∝ 1/log δ(β): ×1.34 at 192, ×1.52 at 228, computed
  with the core-SVP/GSA rule), plus ≈ +0.5–1 bit per response coefficient for doubled challenge mass.

| scenario | per-round need | \|E\| / \|C_acc\| | Akita | PIOP | **wrap total** |
|---|---|---|---:|---:|---:|
| S0 paper parameters (classical ROM, nominal 128) | — | 2¹²⁸ / 2¹²⁸ | 64–72 KB [M] | 25–35 KB | **≈ 90–105 KB** |
| S1 classical ROM honestly at Q = 2⁶⁴ (Akita Thm 10.33; = option L1 security) | Σε ≤ 2⁻¹⁹² | 2²⁵⁶ / ≈ 2²¹⁰ (d = 256, w ≈ 44) | ≈ 105–135 KB | ≈ 50–70 KB | **≈ 160–200 KB** |
| **S2 QROM, hypothetical t² theorem (CMS19 constant), MSIS 192–228** | max ε_r ≤ 2⁻²⁵⁹ | ≈ 2²⁶⁴–2²⁷² (custom q ≈ 2⁶⁶–2⁶⁸, k = 4) / ≈ 2²⁶⁸ (d = 256, w = 64) | ≈ 115–150 KB | ≈ 55–75 KB | **≈ 180–230 KB** |
| S2′ as S2 but only supported primes (\|E\| = 2⁵¹²) | — | 2⁵¹² | ≈ 170–200 KB | ≈ 100–140 KB | ≈ 280–340 KB |
| S3 QROM with t³ or a 2²⁰ constant | ≤ 2⁻³²³ | ≈ 2³²⁸ (q ≈ 2⁸², k = 4) / ≈ 2³³⁰ (d = 512) | ≈ 140–165 KB | ≈ 70–90 KB | **≈ 220–260 KB** |
| S4 DFM20 (2t+n+1)^{2n}, n ≈ 500 | ≈ 2⁻⁶⁵⁰⁰⁰ | — | — | — | **impossible** |
| S5 (b) on a 2-fold variant | ≈ 2⁻³⁹⁰ fold rounds | — | — | — | ≈ 300–500 KB (low confidence) |

**Reading.** < 300 KB is reachable if the QROM theorem has loss ≲ t³ per round, additive over rounds and folds,
**and** the modulus is customised so that \|E\| ≈ 2²⁶⁴–2³³⁰. Akita's theory permits this (q ≡ 5 mod 8, any
size); its implementation supports only p32/p64/p128 today.

---

## 4. MSIS / MLWE parameter sketch

**Why 128-bit core-SVP is not enough [I].** The contract asks Pr[break] ≤ 2⁻¹²⁸ for adversaries bounded by 2⁶⁴
queries. A computational term needs a time bound T and a success/time trade-off model:

| trade-off model for the MSIS term | condition | λ (quantum core-SVP, 0.265β) for T = 2⁶⁴ | with extraction overhead X_ext = 2³⁰–2⁴⁰ |
|---|---|---:|---:|
| linear (generic: Adv ≤ T/2^λ) | 2^{log T − λ} ≤ 2⁻¹²⁸ | **192** | **222–232** |
| quadratic (amplitude amplification of a sampling attack: Adv ≤ (T/2^λ)²) | — | 128 | 158–168 |
| threshold (BKZ below the required block size succeeds with ≈ 0) | heuristic | 128 | 128 |

Notes:
* The extraction overhead is real. The extractor must at least write the 2³⁰-coefficient witness, and Akita's
  Tree(sch) includes 2^{µ′} nested stages (eq. 225–228). The MSIS adversary B_I's time is
  ≈ (Q+1)·poly(Tree, T_A).
* **Recommendation [I]:**
  * baseline λ_MSIS = λ_MLWE = **192** quantum core-SVP (LGSA, matching Akita App. C conventions);
  * plan for **224–232** if the final theorem's X_ext is ≥ 2³⁰ and the user does not accept a sub-linear
    trade-off model;
  * report all instances also under the 0.2563 exponent (Akita's sensitivity check) and classical MATZOV.
* MLWE parameters are needed only for the collapsing reduction (L-collapse). They are a proof device: the
  scheme does not change, but the assumption set does (MSIS + MLWE + SHA-384-as-QRO).

**Parameter shape [I] (rough scaling, not estimator output):**

| quantity | Akita today | wrap at 192 | wrap at 228 |
|---|---|---|---|
| BKZ block size β for the target | 483 (128-bit q-coreSVP) | 725 | 860 |
| rank scaling (∝ 1/log₂δ(β)) | 1.00 | 1.34 | 1.52 |
| compression-map output (128 B today at 147 bits) | 128 B | ≈ 160–190 B | ≈ 190–220 B |
| A collision radius | 2κ̄₁β̄∞ with ω = 31–53 | ×≈1.3–2 (ω = 64) | same |
| invertibility | 2c_max < q^{1/2}/√2 | unchanged (c_max ≤ 2) | unchanged |
| modulus | p32/p64/p128 | custom q ≈ 2⁶⁶–2⁶⁸ ≡ 5 (mod 8), k = 4 | same |
| total size impact | — | lattice bytes ×≈1.35–1.6 | ×≈1.5–1.8 |

All MSIS numbers must be regenerated with the lattice-estimator and Akita's certified Rust estimator (App. C)
before any claim. Concrete MSIS hardness is **heuristic by nature** [P: C §Q3]. This is an assumption added
next to the QRO, not removable by proof.

---

## 5. Work plan, risks, go/no-go

### 5.1 Milestones

| id | deliverable | content | effort | tag |
|---|---|---|---|---|
| **M1** | this document | scope, ledger, strategies, sizing | done | — |
| **M2** | `research/near-compression/lattice-study/qrom_params.py` + Akita size breakdown | Exact round ledger for a wrap-sized Akita schedule: run Akita's planner/validator offline (light build), or transcribe its schedule output. Measured byte breakdown by component. Parameter search for S1/S2/S3 (custom modulus, d = 256 challenge shells, MSIS 192/228 via lattice-estimator). Replace every [I] size in §3.6 | 2–3 wk | engineering |
| **M3** | paper lemma **L-stat** | QROM KS of PIOP + intra-fold algebraic rounds relative to an idealised extractable commitment, with explicit 6t²·max ε_r. Includes the challenge-sampler conditional tapes (Lemma 10.2) in the QROM and grinding accounting under a fixed query budget | 1–2 mo | feasible [I] |
| **M4** | paper lemma **L-collapse** + interactive **L-fold-int** | (i) collapsing of Akita's matrix views under MLWE, with concrete loss. (ii) Interactive post-quantum KS of a fixed Akita schedule with **concrete** error (no 1/poly): generalise CMNW (CWSS + BBK22 + state repair) to Akita's mixed flat/nested trees; aim for expected-time guaranteed extraction (LMS 2021/1543 style). **Gate G1 (see 5.3)** | 2–3 mo | hard; partially open |
| **M5** | paper lemma **L-fold** (QROM) | QROM tree extraction for the fold rounds, additive across folds; compose with M3 into the §2 theorem. **Gate G2** | 2–4 mo | open core [O] |
| **M6** | composition note | wrap KS + SWIRL KS under an oracle-relativised QROM (shared with the hash-only track's M4) | shared | [O] |
| **M7** | Lean (after G2) | ArkLib-*style* framework re-proved inside ArenaCore (DESIGN F4: no Mathlib/ArkLib/VCVio in challenge packages). (a) QROM model + compressed oracle (shared with the hash-only M1). (b) Cyclotomic-ring algebra: LS18 invertibility, operator norms, Ajtai binding ⇒ MSIS reduction statement. (c) Akita classical interactive extraction (Thm 10.31) first, as a stepping stone. (d) M3 lifting. (e) M5. MSIS/MLWE hardness enter as named axioms with explicit advantage terms | 6–12 mo | — |

Order:
* M3 is useful even if the lattice route dies: it is the QROM lifting the hash-only path needs.
* M2 and M3 run in parallel.
* M4 decides feasibility before the expensive M5 and M7.

### 5.2 Risks

1. **R1 — no additive QROM tree extraction (high).** DFM20 shows O(t^{2n}) is optimal for *general*
   multi-round FS. Additivity needs protocol structure; for CWSS with computational binding it may fail or need
   new ideas. A negative result is plausible.
2. **R2 — 1/poly slack (high).** All known quantum rewinding (CMSZ21, LMS22, CMNW, 2025/947) is stated with
   1/poly or negl(λ) slack. Concrete 2⁻¹²⁸-level extraction with expected-poly time is unproven for
   multi-round protocols. Without it, MSIS parameters explode (§4).
3. **R3 — extra assumption (certain if the route works).** Collapsing needs MLWE. The wrap's security then rests
   on MSIS + MLWE + SHA-384-QRO, all heuristic-concrete. Unusual parameters (custom q, large β/q) get little
   cryptanalysis.
4. **R4 — protocol churn (medium).** Akita is weeks old and unaudited. App. F lists security bugs in prior
   artifacts. Any proof is for a frozen schedule family; later optimisations may invalidate it.
5. **R5 — oracle relativisation (shared, open).** Recursion with in-circuit SHA-384 needs an AROM-like QROM,
   for this route and for hash-only.
6. **R6 — size drift (medium).** Custom moduli move field and NTT costs; d = 256 challenge shells and MSIS 228
   could push S2 toward S2′. M2 measures this.
7. **R7 — time to result (high).** M4 + M5 is ≥ 4–7 months of specialist QROM work, with low prior probability
   of success [I: ≈ 20–35 %]. Lean (M7) adds ≥ 6 months. None of it is on the real-time engineering critical
   path, except that the final layer's format waits on it.

### 5.3 Go/no-go criterion

**GO** for a lattice final wrap under the unmodified contract only if **all** of the following hold:
* **G1 (end of M4, ≈ month 3–4):** an interactive post-quantum KS proof for a fixed Akita-type schedule with
  * knowledge error Σ W/\|C_acc\| + (explicit term ≤ 2⁻¹³⁰), **not** 1/poly;
  * expected extractor size ≤ 2⁴⁰·T_A;
  * assumptions ⊆ {MSIS, MLWE}.
* **G2 (end of M5, ≈ month 6–8):** the §2 theorem with
  * a ≤ 3 and C ≤ 2¹⁰;
  * losses additive over folds and rounds;
  * X_ext ≤ 2⁴⁰.
* **G3 (parameters):** with G2's constants, M2's script gives
  * a wrap ≤ 250 KB (≥ 15 % margin under 300 KB);
  * all MSIS/MLWE instances ≥ 192 bits (≥ 224 if the user rejects sub-linear trade-off models);
  * verifier ≤ 50 ms single-thread.

**NO-GO** (fall back to option L3 hash-only at ≈ 0.44–0.57 MB, or L1 with an explicitly relaxed last-layer
contract at ≈ 160–200 KB, scenario S1) if any of these happen:
* G1 fails: only 1/poly slack, or extraction cost ≥ (ck)^{rounds};
* G2 yields only DFM20-type (exponential in rounds) loss;
* G3's sizes exceed 300 KB;
* a published negative result.

---

## 6. Decisions needed from the user (all PROPOSALS)

1. **Time bound for computational terms.** U-6 bounds queries only. Proposal: add "and quantum circuit size
   ≤ 2⁶⁴·poly for the MSIS/MLWE terms, linear trade-off model", which gives 192-bit lattice parameters
   (224–232 with the extraction overhead).
2. **Accept MLWE** as an additional assumption, needed only as a proof device for collapsing, if the route
   proceeds.
3. **Customised modulus** (q ≈ 2⁶⁶–2⁶⁸, k = 4) rather than Akita's shipped p32/p64/p128, to avoid S2′.
4. Whether **L1** (S1: classical-ROM-proven at Q = 2⁶⁴, ≈ 160–200 KB) is an acceptable interim final layer
   while L2 research runs. It would amend U-2/U-6 for the last layer only.
