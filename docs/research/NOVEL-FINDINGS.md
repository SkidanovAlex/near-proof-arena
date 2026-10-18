# Potential novel findings — register for publication review

Status: living register, started 2026-10-18. One entry per candidate finding.
Novelty is **unverified** until the entry's prior-art field cites a search; review
status is **unreviewed** until someone outside the lane that produced it has checked it.
Literature catalogue: `docs/research/literature/INDEX.md`.

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
* Never put keys, private challenge data, or unpublished third-party vulnerabilities in
  detail here; link to a restricted note instead.

## Register

| id | short title | category | novelty | review | disclosure |
|---|---|---|---|---|---|
| NF-1 | Grinding credit void when PoW bits are not bound to the query block | security analysis | candidate | unreviewed | **check** |
| NF-2 | Multi-call challenge squeezing is outside QROM Fiat–Shamir theorems; counter-mode fix | security analysis | candidate | unreviewed | check |
| NF-3 | Sub-collision-resistant Merkle digests in WHIR: block equivocation attack, WHIR-Y fix, Thm R | theory | candidate | internal-review (partial) | none-needed |
| NF-4 | QROM straight-line knowledge soundness for families of recursive layers with truncated Merkle (Thm 6.4) | theory | candidate | unreviewed | none-needed |
| NF-5 | Query-bounded security of hash-only recursion is impossible in any oracle model (Thm O) | theory | candidate (likely folklore-adjacent) | unreviewed | none-needed |
| NF-6 | WHIR over ×15 (15·2^K) cosets on BabyBear with exact rejection sampler | systems / theory application | candidate (likely incremental) | unreviewed | none-needed |
| NF-7 | SHA-512 compression AIR on a 31-bit field: base-8 digits, polynomial carry checks, 7,353 cells, 43 rows | engineering | candidate | unreviewed | none-needed |
| NF-8 | Narrow verifier circuit + measured final-layer size laws; PQ 128-bit-QROM recursion ≈ 299 KB | engineering / measurement | candidate | unreviewed | none-needed |
| NF-9 | Ajtai-compressing lattice SNARKs cannot have CMS19-style rbr knowledge soundness | theory (obstruction) | candidate (likely known to specialists) | unreviewed | none-needed |
| NF-10 | Capacity-regime proximity gaps cost more bytes per security bit than Johnson at low rate | analysis | candidate | unreviewed | none-needed |

## Entries

### NF-1 — Grinding credit void when PoW bits are not bound to the query block
* **Claim.** In a Fiat–Shamir transcript where the proof-of-work check is on the output of
  absorbing the witness, s′ = H(7, σ‖w), and the query indices are squeezed from later calls
  H(5, s′), …, the z grinding bits give no provable reduction of the query-phase error in the
  QROM: the bound falls back to the ungrinded per-round error (ours: 2⁻¹³⁵ → 2⁻¹⁰⁵ end to
  end). Binding the PoW to the block that also yields the indices, B_j = H(7, σ‖w‖j) with PoW
  on B₁'s first z bits and indices from its remaining words, restores the credit at the same
  honest cost.
* **Evidence.** `lane/pq-final-soundness` @ ae0ae8a7b, `research/near-compression/final-soundness/{PROOF.md §5 (Lemma 5.1), GAPS.md G-2}`; fix in `lane/pq-recursion-sha384` @ 46b7e62e2 (T\*, tamper tests).
* **Why it may matter beyond us.** The pattern (observe witness, check leading bits, then
  sample queries from the sponge) is common in duplex-challenger STARK stacks. Whether it is
  an *attack* or only a *proof gap* there is open; we have no attack.
* **Closest prior art.** To search: QROM/ROM analyses of grinding in FS (e.g. concrete PoW-in-FS
  analyses 2023–2026), Plonky3/OpenVM/Stwo challenger code.
* **Next.** Prior-art search; try to turn the gap into a concrete attack or a proof that the
  common pattern is fine in the classical ROM; decide disclosure.

### NF-2 — Multi-call challenge squeezing outside QROM FS theorems
* **Claim.** CMS19 and CDHZ-style QROM FS theorems assume each verifier challenge is one
  oracle output. Sequential-chain squeezing (σ_{j+1} = H(σ_j)) that spans several calls per
  challenge (ours: 4–7 blocks per query move) is not covered; the generic transition loses
  ≈ ε^{1/k}. Counter mode from one post-absorb key, B_j = H(κ‖j), is covered at no cost.
* **Evidence.** `GAPS.md` G-1; PROOF.md Thm 6.4 hypotheses; fix 46b7e62e2.
* **Closest prior art.** To search: duplex-sponge FS in the QROM (e.g. analyses of SAFE / sponge
  FS, Chiesa–Orrù? 2025), "Fiat–Shamir with sponges" papers.
* **Next.** Prior-art search; it may already be addressed by recent sponge-FS QROM work.

### NF-3 — Sub-collision-resistant Merkle digests in WHIR
* **Claim.** With digests below collision resistance, WHIR as built admits a block-equivocation
  attack with success ≈ t²/2ⁿ because shift-query answers are not absorbed before γ.
  Absorbing them first (WHIR-Y, 0 bytes) makes a block-robustness property provable, allowing
  26–27-byte digests (≈ 35–39 KB saving at our size) under Thm R.
* **Evidence.** `lane/pq-weak-binding` @ 70bbb8c2e: `weak-binding/{ANALYSIS.md, HROB.md, REVIEW-1.md}`, `calc/hrob_table.txt`.
* **Review.** One internal review (REVIEW-1) of ANALYSIS; Thm R itself unreviewed. Not adopted
  (U-10 uses 42 B).
* **Next.** Prior-art search (weakly binding / "unique-decoding Merkle" / short-digest BCS work);
  independent review of Thm R.

### NF-4 — QROM straight-line KS for families of recursive layers
* **Claim.** A single database-measurement extractor gives knowledge soundness for all d layers
  at once with truncated 42-B Merkle commitments; the error does not grow with d
  (bound (2tG + 2⁻¹⁶⁰)²).
* **Evidence.** PROOF.md Thm 6.4 (builds on weak-binding Thm 4, K = 0).
* **Next.** Independent review; compare with CMS19 Thm 8.x and CDHZ.

### NF-5 — Impossibility of query-bounded security for hash-only recursion
* **Claim.** In any oracle model bounding only queries, depth ≥ 1 hash-only recursion is insecure:
  an unbounded-time adversary hard-codes a false base proof accepted under in-circuit SHA-384
  and wraps it honestly with ≤ 2⁴⁶ oracle calls.
* **Evidence.** `lane/pq-aic-research` @ 0079ed29a, `aic-research/LEMMA.md` (Thm O; Lemma E.3
  step 3 sketched).
* **Closest prior art.** Barbara–Chiesa–Guan (TCC 2025); folklore about fixed-hash FS.
* **Next.** Probably a remark, not a paper; confirm against BCG.

### NF-6 — WHIR over ×15 cosets on BabyBear
* **Claim.** p − 1 = 15·2²⁷ lets WHIR use cosets of order 15·2^K (beyond the 2²⁷ two-adic
  limit), sound via BCGM Thm 9.2 (any evaluation set); at Ext12, m = 8 misses 2⁻²⁶⁸ so m = 3;
  exact sampler rejects p − 1 then reduces mod 15·2^j.
* **Evidence.** `lane/pq-x15-domains` @ 2cf46f1a4, `x15-domains/SOUNDNESS.md`.
* **Closest prior art.** Smooth/mixed-radix FRI (BBHR18), Circle STARKs, ECFFT.
* **Next.** Likely incremental; record unless the sampler/MCA accounting is new.

### NF-7 — SHA-512-family AIR on a 31-bit field
* **Claim.** 7,353 committed cells per compression (43 rows, 171 + 13 columns, degree 21) via
  base-8 digit words, bus residuals and polynomial carry checks; zero-valid padding.
* **Evidence.** `lane/pq-sha384-air2` @ 971c41b5b, `results/pq384-sha-air2/README.md`.
* **Next.** Compare against published SHA-512/SHA-256 AIRs and chips (OpenVM, SP1, Stwo, Plonky3 examples).

### NF-8 — Narrow verifier circuit and final-layer size laws
* **Claim.** Final-layer size is driven by opened columns; measured laws (GKR 48L² + 192L + 152 B
  with Gruen, stacking 1,984 + 48W, relations 96·cols + …). A single 69-column role-multiplexed
  verifier AIR (258 opened columns total vs 3.5–3.9k in a port of OpenVM recursion) gives a
  modelled ≈ 299 KB final layer at 2⁻¹²⁸ vs 2⁶⁴ quantum queries with proven Johnson-regime bounds.
* **Evidence.** `lane/pq-recursion-sha384` (NV), `results/pq-recursion-nv/`, log
  `docs/logs/pq-final-layer-model-2026-10-17.md` (lane/pq-native-hermetic).
* **Next.** Needs the measured real-settings number before any claim.

### NF-9 — Lattice SNARK QROM obstruction
* **Claim.** Ajtai commitments compress, so the witness is not determined by the oracle record;
  CMS19-style rbr knowledge soundness is impossible; bridging needs an open quantum forking lemma.
* **Evidence.** `lane/pq-lattice-qrom` @ eea80395b, `docs/zk-formal/PQ-LATTICE-QROM-PLAN.md`.

### NF-10 — Capacity vs Johnson regime cost
* **Claim.** Optimal-gap capacity-regime folding needs m ≳ 4R/ε², so at low rate it costs more bytes
  per security bit than Johnson-regime WHIR (even with conjectured m = 1/ε: 1.14–2.2×).
* **Evidence.** `docs/logs/pq-final-layer-model-2026-10-17.md` (iteration 6).
