# Lattice final-wrap study for the ≤ 300 KB PQ track — 2026-10-17

Status: literature study plus model; no code, no measurement of our own.
Decision context: hash-only SWIRL/WHIR recursion bottoms out at ≈ 444–570 KB
(today's settings) / ≈ 356–449 KB (all levers) at realistic in-circuit SHA-384
cost (`docs/logs/pq-final-layer-model-2026-10-17.md`); the user chose to study a
lattice final wrap (2026-10-17). Contract unchanged: V3-D3A-STUDY §D (U-2 proven
bounds, U-6 ≤ 2⁻¹²⁸ at ≤ 2⁶⁴ quantum RO queries, U-7 SHA-384, U-8 real-time).

Evidence reports (by three research agents, sources cited inside):
`research/near-compression/lattice-study/{A-labrador-greyhound,B-modern-lattice,C-security}.md`.
Tags: [M] measured in a paper, [E] authors' estimate, [I] our inference.

## 1. The statement the wrap must prove

"I know a penultimate SWIRL proof that the fixed SWIRL verifier accepts."
With the penultimate layer shaped for cheap verification (calibrated model,
`native/levers_model.py`): **≈ 9–12k SHA-384 (SHA-512-compression)
evaluations + ≈ 6×10⁴ Ext12 multiply-equivalents** [I]. SHA-512 in binary R1CS
≈ 45–60k constraints per compression [I] → ≈ 2²⁹ constraints; in a sumcheck
front end (LaBinius/Jolt style) the hash cost is far lower per compression.

## 2. Findings

| question | answer |
|---|---|
| **Size** | Comfortably fits. LaBRADOR 49–54 KB for binary R1CS 2²⁰–2²⁵ [M]; Greyhound 46–53 KB at N = 2²⁶–2³⁰ [M]; **Akita** (ePrint 2026/1983) 64–72 KB at 2³⁰, full Lattice-Jolt proofs < 100 KB [M]. Our wrap: **≈ 80–150 KB** [I] incl. re-parameterisation. |
| **Verifier** | LaBRADOR alone is linear (≈ 9 s at 2²⁵ [M]) — unusable for a fixed large circuit. Use a sumcheck front end + lattice PCS: LaBinius+LaBRADOR on 65,536 SHA-256 compressions 731 ms [M]; **Akita 16–33 ms** single thread at 2³⁰ [M]; RoKoko 7–13 ms but on vSIS (non-standard) at 2⁻¹⁰⁰ [M]. |
| **Prover** | Akita commit ≈ 3.5 s + open ≈ 3 s at 2³⁰ on 8 threads [M]; LaBinius+LaBRADOR 4,096 SHA-256 compressions in 0.44 s on one core [M]; Greyhound 173 s single-thread at 2³⁰, > 64 GiB [M]. Our wrap ≈ 200–1,000 core-seconds [I] → seconds on a GPU/multi-core budget; no GPU numbers published (ICICLE CUDA LaBRADOR has no timings and omits security repetitions). |
| **BabyBear / Ext12** | **Not native.** BabyBear ≡ 1 mod 2²⁷ fully splits the power-of-two cyclotomics these schemes use, breaking small-challenge invertibility (Akita/LaBRADOR need q ≡ 5 mod 8). Workaround: run over the scheme's 64/128-bit field, ≈ 1.1–1.5× overhead in a sumcheck front end [I] (≈ 500 constraints per Ext12 mult in mod-2⁶⁴+1 R1CS). Native option: Φ₃₇ (degree 36, contains Ext12, non-splitting over BabyBear) per SuperNeo's any-cyclotomic design — research project. |
| **Exact extraction** | Achievable: LaBRADOR's binary-R1CS reduction recovers an exact witness (norm < q) [P]; extractor outputs "witness or MSIS solution", adding an MSIS term. Not the blocker. |
| **QROM / Fiat–Shamir** | **Blocker.** No QROM (knowledge-)soundness proof exists for LaBRADOR, Greyhound, LatticeFold(+), Neo, Akita, RoKoko. Papers are interactive/classical (LaBRADOR 2⁻¹²⁵ per level) or defer FS ("future work"). Generic multi-round QROM FS loses (2q+n+1)²ⁿ (DFM20) — useless at ≈ 25–35 rounds. CMS19's t²·ε_rbr route needs statistical rbr soundness with hash commitments; lattice arguments are computational with Ajtai commitments. Even classically, Q = 2⁶⁴ needs per-round κ ≤ 2⁻¹⁹² vs ≈ 2⁻¹²⁵ today. |
| **Hardness** | Heuristic by nature: "128-bit" = classical core-SVP (0.292β); quantum sieving (0.265β) ≈ 116 bits [I]; our contract arguably needs ≈ 192-bit MSIS when trading success probability for time [I]. Adds an assumption next to SHA-384-as-QRO, in less-studied parameter ranges. Chen 2024's quantum LWE claim was withdrawn (bug). |
| **Formalisation** | None for any lattice SNARK. Nearest: EasyCrypt Dilithium (classical; found FS-with-aborts gaps), ArkLib (Lean, IOP rbr/FS, no QROM, no lattice). |
| **Maturity** | Rapidly moving field with recent security fixes (Akita App. F lists bugs in earlier papers/code); Akita is open-source Rust, unaudited. |

## 3. Verdict

* **Engineering targets: met on paper.** An Akita-style wrap (sumcheck front end
  + Module-SIS lattice PCS over a 64/128-bit field) gives ≈ 80–150 KB, tens of ms
  verification, and seconds-scale proving at our statement size.
* **Contract: not met today.** U-2/U-6 require a proven bound at ≤ 2⁻¹²⁸ against
  2⁶⁴ quantum queries. No lattice SNARK has a QROM Fiat–Shamir proof, current
  parameters miss even the classical requirement (κ ≈ 2⁻¹²⁵ vs ≤ 2⁻¹⁹²), and
  MSIS hardness is estimator-based (~116 quantum bits at the papers' "128").
  The same open issue (in-circuit SHA-384 vs SHA-384-as-oracle) applies to any
  recursive wrap and is shared with the hash-only design.

So the lattice route trades a size problem for a security-proof problem.

## 4. Options (user decision)

| option | final size | what it costs |
|---|---:|---|
| **L1. Lattice wrap under a relaxed contract for the last layer** — classical-ROM-proven FS + estimator MSIS at ≈ 192-bit parameters, amend U-6/U-7 for that layer | ≈ 80–150 KB | weaker, explicitly heuristic guarantee on the layer that every validator checks; new assumption class |
| **L2. Lattice wrap + research to prove QROM soundness** for sumcheck + lattice-PCS (Akita-type): rbr knowledge soundness of the IOP part, a QROM BCS-style transform for computationally binding (Ajtai) commitments, larger challenge sets (≥ 2⁻¹⁹²–2⁻²⁵⁶ per round) | ≈ 100–160 KB [I] (bigger challenges) | open research (months, uncertain); then Lean formalisation |
| **L3. Hash-only, accept 0.45–0.57 MB** (U-9 target band) | ≈ 444–570 KB | nothing new; fully within contract once the existing QROM/MCA obligations are closed |
| **L4. Hash-only research bets** (sequential-work Fiat–Shamir, shorter-than-Merkle hash openings) | unknown | research; see chat notes 2026-10-17 |

Recommendation [I]: keep L3 as the contract-compliant baseline and build the
SHA-384 recursive parent (needed by every option, since the lattice wrap sits on
top of the same SWIRL recursion). In parallel, scope **L2** concretely — the
QROM proof for an Akita-type stack is a well-defined research problem, and its
answer decides whether a < 300 KB proof can meet the contract. Use L1 only if the
user is willing to amend U-6/U-7 for the final layer.

## 5. If pursued, first steps

1. Penultimate-shape re-optimisation for lattice cost (SHA count dominates;
   trade fewer SHA for more field arithmetic, which is cheap in a sumcheck front end).
2. Akita prototype on a SHA-512-compression batch at 64-bit field: measure proof
   bytes, prove time, verify time at 10k compressions (CPU).
3. Security write-up for L2: define the rbr knowledge-soundness target per round
   at ≈ 2⁻²⁶⁰, challenge-set sizes, and the missing QROM transform theorem.

## 6. L2 milestone 1 result (2026-10-17, `lane/pq-lattice-qrom` @ `eea80395b`)

Full plan: `docs/zk-formal/PQ-LATTICE-QROM-PLAN.md` on that lane. User decision
2026-10-17: run L3 (hash-only baseline) and L2 in parallel.

**Verdict: no existing route proves the contract for an Akita-type wrap; the
obstruction is structural.**
* Akita's Ajtai commitments compress (128 B for 2³⁰ coefficients), so the witness
  is not determined by the transcript/oracle record: CMS19-style rbr knowledge
  soundness is impossible; the bridging lemma ("bad transcript ⇒ MSIS solution")
  needs two openings of one commitment, i.e. an open quantum forking lemma.
* DFM20's (2t+n+1)²ⁿ loss is fatal at ≈ 400–700 challenge rounds (Akita +
  sumcheck front end). LMS22 / CMNW quantum rewinding is interactive-only,
  needs MLWE, and extracts only up to inverse-polynomial slack. Straight-line
  extraction (Pass / Rotem–Tessaro) costs ≈ 150–350 KB. No 2025–2026 QROM
  knowledge-soundness result for any multi-round lattice SNARK/folding scheme.
  Akita's own Cor. 10.34 cannot certify 2⁻¹²⁸ classically at Q ≥ 1 with a 2¹²⁸
  challenge field.
* **Most promising: "hybrid lifting"** — CMS19 (6t²ε) for the statistically sound
  rounds (challenge field ≥ 2²⁶¹), a *new* quantum tree-extraction lemma with
  additive losses for only the 4–8 fold rounds (the open core), and MLWE
  collapsing for the commitment matrices (adds MLWE).
* Wrap size if it succeeds: **≈ 180–230 KB** (custom q ≈ 2⁶⁶, MSIS 192–228 bit);
  ≈ 280–340 KB with Akita's shipped moduli; ≈ 160–200 KB under L1 (classical ROM
  at Q = 2⁶⁴). Odds ≈ 20–35 %, ≥ 4–7 months specialist work.
* Gates: **G1** (~month 3–4) interactive PQ knowledge soundness with additive
  error ≤ 2⁻¹³⁰, extractor ≤ 2⁴⁰× adversary time, assumptions ⊆ {MSIS, MLWE};
  **G2** (~month 6–8) QROM theorem with loss ≤ C·t³ (C ≤ 2¹⁰), additive across
  folds; **G3** parameter script ≤ 250 KB. Any gate fails → L3 or L1.
* User decisions raised: a time bound for the lattice terms (U-6 bounds queries,
  not time; linear time/success ⇒ ≈ 192-bit quantum core-SVP, 222–232 with
  extractor overhead); accept MLWE; custom modulus; L1 as interim final layer.
