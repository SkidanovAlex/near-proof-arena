# PQ succinct-proof paper: audit, draft status, and pick-up point

Status: 2026-10-19. Work paused at the user's request until the **join** (Wasm proof +
state proof over shared buses) lands. Nothing here is published.

Companion draft: `docs/research/pq-proven-soundness-paper-draft.md`.

## 1. What this records

The user asked for a paper on the novel parts of the PQ final-layer work, structured like a
cryptography/ZK preprint, foregrounding the new approaches and proofs and the absence of extra
conjectures (including the proximity conjecture). A draft was written. Before publishing, an
audit against the source lanes found factual mismatches and status overclaims. The user then
asked to wait for the join, so this note records the audit, the corrected facts, and what must
be settled before the draft becomes a paper.

## 2. Verified facts (use these, not the earlier draft numbers)

### 2.1 Sizes and runs

| run | value | source | caveat |
|---|---|---|---|
| G2 gate FINAL | **293,077 B** (`gkr 32,408 / relations 24,292 / stacking 6,832 / whir 229,346`) | `lane/pq-stream-commit` `g2-gate/MANIFEST.json`, `run.log` | bound, `V_d` accepts under pinned 125,550-row program; forgery control passes |
| provisional O-2 chain FINAL | 287,477 B | `results/pq-stream-commit/README.md` §"O-2 chain" | **`bind = false`**; provisional, must be re-run |
| model, O-2 chain | 287,037 B | same README | model, not measured |
| measured b=2 final | 416,171 B, sha256 `e5e526a2…` | same README | streamed == in-memory |
| model vs measured, b=7 m=3 | 339,747 vs 339,370 (+0.11 %) | same README | |
| model vs measured, b=7 m=64 | 330,149 vs 329,478 (+0.20 %) | same README | |

G2 runtime: 46 min wall, 17.15 GB host peak, FINAL 441 s / 13.98 GB. Soundness print 268.2 bits
(logup 323.4, proximity 281.6, query 268.2).

Streaming: `853 GB` virtual codeword at the b=7, W=106 shape committed in 480 s at 14.9 GB peak;
full best-shape final at `≈ 39 GB`; b=2 streamed peak 35.5 GB vs 64.4 GB in-memory.
`106 cols × 15·2^27 points = 2.13e11` base elements (×4 B = 853 GB) — **not** `10^12`.

### 2.2 O-2 query schedules (authoritative: `calc/o2_table_bound.out`)

| layer / shape | O-2 schedule | all-J64 | r0=J64 |
|---|---|---|---|
| final b7 h20 k1=1 k4 lf7 | **[41, 38, 29, 23]** | [44, 40, 30, 24] | [44, 38, 29, 23] |
| final b8 h19 k1=1 k3 lf9 | **[38, 35, 29, 25]** | [40, 37, 30, 25] | [40, 35, 29, 25] |
| inner NV b6 h19 k1=1 k4 lf6 | **[46, 41, 31, 25]** | [48, 44, 32, 25] | [48, 41, 31, 25] |
| base app stress b6 h21 (2 commits) | O-2 **fails** at `2^-231.77` (logup α,β) → **r0=J64** | pass | pass |

**Repo inconsistency to fix:** `DKT-VERIFY.md` prints inner `[45,41,31,24]` (lines 262, 268) but
`[46,41,31,25]` (lines 416, 458); final b8 prints `[38,35,29,24]` in `MCA-UPGRADE.md` but
`[38,35,29,25]` in `o2_table_bound.out` and `DKT-VERIFY.md:458`. The `.out` files are the
computed values; the prose tables should be reconciled before citing either.

### 2.3 Certificates

- `calc/dkt_certs_o2.json`: **129** entries for the six bound shapes = 93 round/fold sub-codes
  (s ≤ k_i) + 36 round-0 batching curves.
- **All 129 pass** the authors' engine, ArkLib's `#eval!` checker, and the **Lean kernel**
  (`lean/DKTCertsO2_{0..5}.lean`; 222 theorems; axioms `propext, Classical.choice, Quot.sound`).
- Penultimate candidates (§8.7) add 44 entries → 173 total. **35/44 kernel-checked; 9/44 are
  kernel-blocked by the 24 GB cgroup cap** (`lean/DKTCertsO2_big.keys`), checked only by the
  authors' engine and `#eval!`. A kernel check would need 32–48 GB.
- The measured G2 chain uses `NEARPROOF_DKT_EXCLUDE = lean/DKTCertsO2_big.keys` and therefore puts
  **penultimate round 3 on Johnson m=64** (+1 query). Every other round is first-order.

### 2.4 Transcript and SHA AIR

- `T*` is implemented in the backend, native SHA config, recursion SHA config, and NV circuit
  (`nv/transcript2.rs`, `nv/builder.rs`). It costs **0 base-proof bytes**, but NV grows **70 → 73
  columns** and **52 → 55 interactions/row** (rotated stays 36); ≈144 B for the extra openings.
  SHA compression count is unchanged.
- G-11 (z = 0 ⇒ zero witness) and G-10 (`c` bound into the vk pre-hash) are fixed.
- SHA AIR v2.1: 43 × 171 = **7,353** main cells/compression, degree 21, **5,921/5,921** mutations
  detected. v4: 128 × 83 (73 rotated) = **10,624** cells, degree 9 (NvAir 8 → D = 9), **6,321/6,321**
  mutations detected. `5,848` is the v4 **constraint-DAG node count**, not a mutation count.
- `2.6×` = 18,963 / 7,353 (OpenVM SHA-512 vs our v2.1) — correct.

### 2.5 E2E scope (the reason to wait for the join)

`lane/pq-e2e-slice` proves one prepared function call (`i32.const/add/drop/end`) end to end at
test size. `ctx`, `pre_state_root`, receipt, and `post_state_root` are **statement-carried stubs**
(no AIR reads them). The main finding G1 is that the NV program depends on the child proof when
the child uses PoW, so the program cannot be pinned at real settings; program binding worked only
because the test-size inner levels have no PoW.

Consequently the 293 KB / 287 KB numbers are the **recursion tail**, not a chunk-validation proof.
`docs/logs/pq-gap-analysis-2026-10-19.md` §2.1–2.3 lists what the join still needs (HOST chip and
buses, Ed25519/SHA-512 in-circuit, Wasm↔state shared-bus join, coverage theorem).

## 3. Audit findings (mismatches and overclaims found in the first draft)

| # | first draft | correct | action |
|---|---|---|---|
| 1 | "a proof for NEAR chunk validation" | recursion tail only; chunk relation not joined; e2e statement fields are stubs | rescope the paper |
| 2 | inner queries `[45,41,31,24]` | `[46,41,31,25]` per `.out` | use `.out`; reconcile repo |
| 3 | final b8 `[38,35,29,24]` | `[38,35,29,25]` per `.out` | same |
| 4 | "129 certs, all kernel-checked, every real round" | true for the six bound shapes; 9/44 penultimate certs kernel-blocked, chain excludes them and uses J64 at penultimate r3 | qualify |
| 5 | v4 mutations `5,848/5,848` | `6,321/6,321`; 5,848 is the DAG node count | fix |
| 6 | `T*` "zero proof bytes" | 0 base bytes; +3 NV columns / +3 interactions, ≈144 B | qualify |
| 7 | 287,477 B as the result | provisional and `bind = false`; bound number is 293,077 B | fix |
| 8 | "×15 saves 99 KB" | 99,072 B is the T/12k model delta; measurements show the rate effect, not that exact delta | label as model |
| 9 | prover peak 25.6–39 GB | G2 gate 17.15 GB; unbound chain 25.6 GB; streamed b2 35.5 GB | give the range with sources |
| 10 | "verifiable in seconds" | only the x15 prototype verifier (7–15 ms) is measured; no final-layer verify timing recorded here | drop |
| 11 | "all parameters from proven bounds" | DKT26 is unrefereed; DKT26→WHIR lift is paper-level (S-28) | qualify |
| 12 | 26–28 B digests "save 39 KB" | U-10 deploys 42 B; narrow setting needs position tags + dedup and is not adopted | mark optional |
| 13 | codeword "≈10^12 elements, ≈1 TB" | 2.13e11 elements, 853 GB at b=7/W=106 | fix |

## 4. What Lean actually covers (and what it does not)

Proven in Lean / ArkLib at the pinned commit, axioms checked:

- DKT26 Thm 5.12 (Johnson line MCA) + Cor 7.7 (interleaving) + Cor 7.8 (folds), with the
  `johnsonE0` constant used by the calculator; the pairwise list term of (67).
- DKT26 Prop 5.10 + Lemma 5.6 + Lemma 5.11 first-order certificates; 129/129 deployed entries.
- The ArkLib checker is decidable and re-verifies the stored integer certificates exactly.

**Not** Lean-proven here:

1. **DKT26 → WHIR lift** (S-28): RS-level MCA/list statements ⇒ WHIR round-by-round errors.
   Paper-level via WHIR Thm 5.2 as corrected by Puškin's Tartu thesis.
2. **WHIR Thm 5.2** itself (external, refereed) and its corrected form (Puškin, MSc thesis).
3. **`c·2^K` domain lemma** (x15 `SOUNDNESS.md`): hand proof of the four smoothness uses; the
   theorem lift inherits (2).
4. **`T*` grinding Lemma 5.1 and Theorem 6.4** (QROM straight-line KS for layer families): hand,
   unreviewed. Weak-binding Theorem 4 and Theorem R: hand, one internal review.
5. **Theorem O / A-IC**: hand `[T]`, unreviewed; proves A-IC is necessary in any query-only model.
6. **Tight-heights kernel** in the univariate-skip encoding (G-6): validated by code and 24 tamper
   tests, not derived line by line.

So the honest claim is: the algebraic proximity inputs and the deployed certificate instances are
Lean-checked; the protocol composition (WHIR + QROM transcript + recursion) is not.

## 5. Decisions pending

1. **Scope:** paper as "recursive final layer of the PQ stack, with the chunk join as future work"
   (accurate today), or wait for the join and write the full chunk-validation paper.
   User chose: **wait for the join.**
2. **Lean obligation for preprints.** The user's rule: a preprint we depend on should be proven
   here. Options:
   - (a) finish the 9 blocked DKT certificates (needs a >24 GB cap) and Lean the x15 domain +
     sampler + `T*` arithmetic (weeks), keeping WHIR/BCGM as cited external theorems; or
   - (b) formalise WHIR soundness + the DKT26→WHIR lift in ArkLib (months).
   Not decided. (a) is the minimum consistent with the rule; (b) is the full version.
3. **Repo reconciliation:** fix the 45/46 and 24/25 schedule discrepancies in
   `DKT-VERIFY.md` / `MCA-UPGRADE.md` before citing either.
4. **Gist:** the earlier short NF-6 note is at
   <https://gist.github.com/ilblackdragon/173ed5a72ba375ef542df00a8c04bc9c> (secret). Replace it
   only after 1–3 are settled.

## 6. Pick-up checklist

- [ ] Re-run the O-2 chain with `bind = true`; replace 287,477 with the bound number.
- [ ] Reconcile O-2 schedules (45/46, 24/25) in the two prose tables.
- [ ] Kernel-check the 9 `DKTCertsO2_big` entries at ≥32 GB, or document the exclusion permanently.
- [ ] Decide (a) vs (b) in §5.2 and, if (a), Lean the x15 domain lemma and `T*` arithmetic.
- [ ] Land the join (HOST chip/buses, sig chip, coverage theorem) per the gap analysis.
- [ ] Re-scope the paper to the joined relation; re-run the size model against the real shapes.
- [ ] Ungate the 26–28 B digest analysis only after position tags + dedup are in the circuit.
