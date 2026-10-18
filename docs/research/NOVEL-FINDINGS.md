# Potential novel findings — register for publication review

Status: living register, started 2026-10-18. One entry per candidate finding.
Novelty is **unverified** until the entry's prior-art field cites a search; review
status is **unreviewed** until someone outside the lane that produced it has checked it.
Literature catalogue: `docs/research/literature/INDEX.md` (catalogue entries for every prior-art
citation below; unexploited items ranked in `docs/research/literature/OPPORTUNITIES.md`).
Prior-art verdicts (2026-10-18): `research/novelty/PRIOR-ART.md` (from `lane/novelty-prior-art` @ 34920925e).

## How to maintain

* Add an entry when a lane produces a result that is not a direct application of a cited
  theorem or a known engineering pattern. Keep it even if it later turns out to be known;
  mark it `known` and cite the source.
* Fields: claim (one paragraph, precise), evidence (branch @ commit, file, theorem/test),
  category, novelty, review, disclosure, closest prior art, next step.
* **Novelty:** `candidate` (no search yet) → `searched-new` (search found nothing closer than
  the cited work) / `incremental` / `known`.
* **Review:** `unreviewed` → `internal-review` (checked by an independent agent/person) →
  `external-review`.
* **Disclosure:** `none-needed` / `check` (may affect deployed systems; decide on
  coordinated disclosure **before** any publication) / `in-progress` / `done`.
* **The GitHub repository (ilblackdragon/near-proof-arena) is public.** Never commit keys,
  private challenge data, unpublished third-party vulnerability details, or names of systems a
  finding may affect — not here and not anywhere else in the repo. Keep such material outside
  the repository, under `/data/illia/nearproof-deps/restricted/`, and reference it only by that
  local path.

## Register

| id | short title | category | novelty | review | disclosure |
|---|---|---|---|---|---|
| NF-1 | Standard QROM compilation gives no grinding credit when PoW bits are not bound to the query block (proof gap, no attack) | security analysis | searched-new | unreviewed | pending user decision (proof gap only, no attack) |
| NF-2 | Multi-call challenge squeezing is outside QROM Fiat–Shamir theorems; counter-mode fix | security analysis | incremental | unreviewed | none-needed |
| NF-3 | Sub-collision-resistant Merkle digests in WHIR: block equivocation attack, WHIR-Y fix, Thm R | theory | searched-new | internal-review (partial) | none-needed |
| NF-4 | QROM straight-line knowledge soundness for families of recursive layers with truncated Merkle (Thm 6.4), conditional on A-IC | theory | incremental | unreviewed | none-needed |
| NF-5 | Query-bounded security of hash-only recursion is impossible in any oracle model (Thm O) | theory | known (folklore) | unreviewed | none-needed |
| NF-6 | WHIR over ×15 (15·2^K) cosets on BabyBear with exact rejection sampler | systems / theory application | incremental | unreviewed | none-needed |
| NF-7 | SHA-512 compression AIR on a 31-bit field: base-8 digits, polynomial carry checks, 7,353 main cells (171 × 43) | engineering | searched-new (engineering) | unreviewed | none-needed |
| NF-8 | Narrow verifier circuit + measured final-layer size laws; modelled ≈ 299 KB final layer, conditional on T\* and A-IC | engineering / measurement | searched-new (data point) | unreviewed | none-needed |
| NF-9 | Ajtai-compressing lattice SNARKs cannot have CMS19-style rbr knowledge soundness | theory (obstruction) | known | unreviewed | none-needed |
| NF-10 | Capacity-regime proximity gaps cost more bytes per security bit than Johnson at low rate | analysis | known / incremental | unreviewed | none-needed |

## Entries

### NF-1 — Standard QROM compilation gives no grinding credit when PoW bits are not bound to the query block
* **Claim.** In a Fiat–Shamir transcript where the proof-of-work check is on the output of
  absorbing the witness, s′ = H(7, σ‖w), and the query indices are squeezed from later calls
  H(5, s′), …, **the standard QROM compilation does not give the grinding credit**: applied as
  is, it bounds the query phase only by the ungrinded per-round error (ours: 2⁻¹³⁵ → 2⁻¹⁰⁵ end
  to end). **There is no attack.** In the classical ROM the chained pattern has the same bound as
  the single-output one, and for a fixed transcript prefix a QROM reduction to search
  (DFMS22 Prop. 3.5) gives a matching bound; only the composition over many prefixes with state
  restoration is unproven (PRIOR-ART.md §1.3). Binding the PoW to the block that also yields the
  indices, B_j = H(7, σ‖w‖j) with PoW on B₁'s first z bits and indices from its remaining words,
  is covered by the standard compilation at the same honest cost.
* **Evidence.** `lane/pq-final-soundness` @ ae0ae8a7b, `research/near-compression/final-soundness/{PROOF.md §5 (Lemma 5.1), GAPS.md G-2}`; fix in `lane/pq-recursion-sha384` @ 46b7e62e2 (T\*, tamper tests); verdict `research/novelty/PRIOR-ART.md` §1.
* **Closest prior art.** ethSTARK documentation (ePrint 2021/582) §3.11.3 vs §6.3 Thms 6/8;
  Herold–Khovratovich–Kudinov–Tessaro–Wagner, Aborting Random Oracles (ePrint 2026/016) Cor 3 and
  §2 "Quantum Setting"; CMS19 App. B; DFMS22 Prop. 3.5 / Thm 4.3. Catalogue: [CMS19], [DFMS22],
  [HKKTW26], [BCG26].
* **Disclosure.** Pending user decision (proof gap only, no attack). The prior-art lane found
  possible impact on deployed systems as a proof gap only; system names are kept solely in a
  restricted note outside the repository (`/data/illia/nearproof-deps/restricted/`). Do not name
  systems here or anywhere in the repo.
* **Next.** Write the composition lemma (DFMS22 extractable simulator, PRIOR-ART §1.3) or keep
  T\*; user decides on courtesy notices before publication.

### NF-2 — Multi-call challenge squeezing outside QROM FS theorems
* **Claim.** CMS19 and CDHZ-style QROM FS theorems assume each verifier challenge is one
  oracle output. Sequential-chain squeezing (σ_{j+1} = H(σ_j)) that spans several calls per
  challenge (ours: 4–7 blocks per query move) is not covered; the generic transition loses
  ≈ ε^{1/k}. Counter mode from one post-absorb key, B_j = H(κ‖j), is covered at no cost.
* **Evidence.** `GAPS.md` G-1; PROOF.md Thm 6.4 hypotheses; fix 46b7e62e2.
* **Closest prior art.** CMS19 App. B Thm B.3; Chiesa–Orrù (ePrint 2025/536; classical ideal
  permutation, QROM open §1.3); Fractal §12.2.1; Huang–Hülsing–Maram–Ritsch–Saha, Feistel Tools
  (ePrint 2026/146) Thm 19 (ZK only). Catalogue: [CMS19], [CO25], [COS20], [HHMRS26].
* **Novelty.** Incremental (PRIOR-ART.md §2). Disclosure: none-needed.
* **Next.** Keep the counter-mode fix; optionally a short note together with NF-1.

### NF-3 — Sub-collision-resistant Merkle digests in WHIR
* **Claim.** With digests below collision resistance, WHIR as built admits a block-equivocation
  attack with success ≈ t²/2ⁿ because shift-query answers are not absorbed before γ.
  Absorbing them first (WHIR-Y, 0 bytes) makes a block-robustness property provable, allowing
  26–27-byte digests (≈ 35–39 KB saving at our size) under Thm R.
* **Evidence.** `lane/pq-weak-binding` @ 70bbb8c2e: `weak-binding/{ANALYSIS.md, HROB.md, REVIEW-1.md}`, `calc/hrob_table.txt`.
* **Review.** One internal review (REVIEW-1) of ANALYSIS; Thm R itself unreviewed. Not adopted
  (U-10 uses 42 B).
* **Closest prior art.** CY21b Game 5.2 / Def. 5.3 / §1; CMS19 Thm 8.6; CDHZ (ePrint 2025/2166)
  Thm 8.3; Hamoudi–Magniez Prop. 4.3. The WHIR reference implementation has the same γ order.
  Catalogue: [CY21b], [CMS19], [CDHZ25], [HM20].
* **Novelty.** Searched-new; judged paper-worthy (PRIOR-ART.md §3).
* **Next.** Independent review of Thm 4 and Thm R.

### NF-4 — QROM straight-line KS for families of recursive layers
* **Claim.** A single database-measurement extractor gives knowledge soundness for all d layers
  at once with truncated 42-B Merkle commitments; the error does not grow with d
  (bound (2tG + 2⁻¹⁶⁰)²).
* **Condition.** The recursive statement is conditional on A-IC (adopted as A-IC(τ), U-11/U-12);
  only the per-layer extraction is assumption-free.
* **Evidence.** PROOF.md Thm 6.4 (builds on weak-binding Thm 4, K = 0).
* **Closest prior art.** CGSY24 (ePrint 2023/1646) Thm 5.1, §2.3; CDHZ Thm 10.6 / 11.3; CCGOS23
  Thm 9.4. Catalogue: [CGSY24], [CDHZ25], [CCGOS23].
* **Novelty.** Incremental (PRIOR-ART.md §4).
* **Next.** Independent review.

### NF-5 — Impossibility of query-bounded security for hash-only recursion
* **Claim.** In any oracle model bounding only queries, depth ≥ 1 hash-only recursion is insecure:
  an unbounded-time adversary hard-codes a false base proof accepted under in-circuit SHA-384
  and wraps it honestly with ≤ 2⁴⁶ oracle calls.
* **Evidence.** `lane/pq-aic-research` @ 0079ed29a, `aic-research/LEMMA.md` (Thm O; Lemma E.3
  step 3 sketched).
* **Closest prior art.** BCG24 (TCC 2025, ePrint 2024/728) Thms 4.1/5.1/6.1; CGSY24 §1.1.2.
  Catalogue: [BCG24], [CGSY24].
* **Novelty.** Known (folklore). Keep as a remark.

### NF-6 — WHIR over ×15 cosets on BabyBear
* **Claim.** p − 1 = 15·2²⁷ lets WHIR use cosets of order 15·2^K (beyond the 2²⁷ two-adic
  limit), sound via BCGM Thm 9.2 (any evaluation set); at Ext12, m = 8 misses 2⁻²⁶⁸ so m = 3;
  exact sampler rejects p − 1 then reduces mod 15·2^j.
* **Evidence.** `lane/pq-x15-domains` @ 2cf46f1a4, `x15-domains/SOUNDNESS.md`.
* **Closest prior art.** WHIR reference implementation commits 1d392aa (3-smooth NTT) and 2556d4e
  (exact non-power-of-two index sampler); BCGM Def. 3.8; BBHR18, Circle STARKs, ECFFT.
  Catalogue: [WHIR-rs], [BCGM25], [BBHR18].
* **Novelty.** Incremental: the written c·2ᴷ lemma and the BabyBear ×15 choice look unpublished.
  Worth a remark inside NF-8.

### NF-7 — SHA-512-family AIR on a 31-bit field
* **Claim.** 7,353 = 171 × 43 committed main cells per compression (43 rows, 171 main columns,
  degree 21); the 13-column table is a fixed 64 rows, counted separately. Built from base-8 digit
  words, bus residuals and polynomial carry checks; zero-valid padding.
* **Evidence.** `lane/pq-sha384-air2` @ 971c41b5b, `research/near-compression/results/pq384-sha-air2/README.md`.
* **Closest prior art / comparator.** OpenVM sha2-air SHA-512: 18,963 cells (the only open SHA-512
  AIR); best SHA-256 AIRs ≈ 7.3–7.8k cells. Catalogue: [OVM-sha2air], [P3-sha256air], [Cor26-sha].
* **Novelty.** Searched-new (engineering).

### NF-8 — Narrow verifier circuit and final-layer size laws
* **Claim.** Final-layer size is driven by opened columns; measured laws (GKR 48L² + 192L + 152 B
  with Gruen, stacking 1,984 + 48W, relations 96·cols + …). A single 69-column role-multiplexed
  verifier AIR (258 opened columns total vs 3.5–3.9k in a port of OpenVM recursion) gives a
  modelled ≈ 299 KB final layer at 2⁻¹²⁸ vs 2⁶⁴ quantum queries with proven Johnson-regime bounds.
* **Evidence.** `lane/pq-recursion-sha384` (NV), `results/pq-recursion-nv/`, log
  `docs/logs/pq-final-layer-model-2026-10-17.md` (lane/pq-native-hermetic).
* **Condition.** The ≈ 299 KB at 2⁻¹²⁸ is conditional on T\* (G-1/G-2 fixes) and on A-IC
  (U-11/U-12) for the recursive statement.
* **Comparators.** WHIR §6.3.4 (WHIR-JB 299 KiB at 128-bit classical rbr), leanMultisig (leanVM),
  soundcalc root configurations (e.g. 200 KiB classical). Catalogue: [ACFY24], [leanVM], [soundcalc],
  [zkDTVM].
* **Novelty.** Searched-new (data point).
* **Next.** Needs the measured real-settings number before any claim.

### NF-9 — Lattice SNARK QROM obstruction
* **Claim.** Ajtai commitments compress, so the witness is not determined by the oracle record;
  CMS19-style rbr knowledge soundness is impossible; bridging needs an open quantum forking lemma.
* **Evidence.** `lane/pq-lattice-qrom` @ eea80395b, `docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`.
* **Closest prior art.** Symphony (ePrint 2025/1905); LMS22; CMNW (ePrint 2024/281); Akita (ePrint
  2026/1983). Catalogue: [Symphony25], [LMS22], [CMNW24], [Akita26].
* **Novelty.** Known.

### NF-10 — Capacity vs Johnson regime cost
* **Claim.** Optimal-gap capacity-regime folding needs m ≳ 4R(2−R)/ε² (proven), so at low rate it
  costs more bytes per security bit than Johnson-regime WHIR. With a conjectured folding parameter it
  is worse for m ≳ 1/ε, and possibly better for m ≈ 0.5/ε (LXYYZ Table 5).
* **Evidence.** `docs/logs/pq-final-layer-model-2026-10-17.md` (lane/pq-native-hermetic), iteration 7.
* **Closest prior art.** LXYYZ (ePrint 2026/2133) Tables 3–5. Catalogue: [LXYYZ26].
* **Novelty.** Known / incremental.
