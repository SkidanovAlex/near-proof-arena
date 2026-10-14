# D1a phase 2: from `nearAirV3D1` to the D1a admission statement — plan and status

Status: **in progress** (lane `v3-d1-phase2`, branch `lane/v3-d1-phase2`, from main `0a78f36d`),
started 2026-10-14 on the user's go-ahead. Log: `docs/logs/v3-d1-phase2-2026-10.md`.
Inputs: phase 1 (`docs/logs/v3-d1-tables-2026-10.md`, main `86fab5fd`), design
`V3-D1-DESIGN.md` §6–7, the D0a certificate (`Assembly/AdmissionV3.lean`:
`nearV3_admission_final`), the relation `NearSpecV3.RelD1a`
(`spec/lean/v3/NearSpecV3/ChunkValidationD1a.lean`) and the tier `Tier.d1a` of the signed
challenge `near-chunk-v3` (`chl_497bbbf1…`).

Ground rules (unchanged from the D0a lanes):
* the trusted spec (`spec/`), the challenges, `nearAirV3` and the D0a certificate are not edited.
  Every phase-2 module is new and lives under `zk-formal/ZkFormal/NearV3/D1/`.
* There is no `sorry`, `axiom`, `native_decide` or `implemented_by` in a committed module.
* Statements are never weakened. A phase-1 statement that turned out to be mis-stated gets a
  corrected sibling. The original is kept and the defect is recorded (see §4).
* Modules are small, there is no `decide` over real data, and no simp folds `Nat` literals
  against free variables (the lean4lean/nanoda pitfall of v3-recheck).
* The build root is `ZkFormal.NearV3.D1.Phase2`. It imports every finished phase-2 module and is
  not imported by D0a or by the verifier model.

---

## 1. Target statement

The judge's expected type for `near-chunk-v3` at a declared tier (`spec/lean/judge/ExpectedChunkV3.lean.template`) is

```
ArenaExpected.expectedType = AdmissionStatement
  (NearSpecV3.challengeParamsChunkWith .d1a (profileOf …) verifyFuel maxProofBytes maxReductionFuel)
  { publicDigest, impl := .interp verifierDigest }
```

At the frozen challenge's literals this is definitionally `challengeParamsChunk .d1a`, the same
way D0a's `params` matched `challengeParamsD0a`. So the certificate is

```
theorem nearV3D1_admission_final (art) (pub) (hpub : sha256 pub = art.publicDigest)
    (himpl : art.impl.Connection (challengeParamsChunk .d1a).verifyFuel
      (npVerifierP (challengeSpecChunk .d1a) nearAirV3D1 split prepD1b).toVerifier) :
    AdmissionStatement (challengeParamsChunk .d1a) art
```

* `challengeSpecChunk .d1a` has `Rel = RelTier .d1a = RelD1a B0` on `c.1.encode`, and
  `Domain = DomainTier .d1a` (a `RelD1a` witness of at most 64 MiB).
* Soundness for the challenge statement (`RelChunkV3`) follows from `NearSpecV3.sound_lift` /
  `rel_mono` (`relD1a_relD1`), which are already in the trusted spec. Nothing more is owed.
* `npVerifierP` reads the spec only through `claimOk S`, i.e. through `decodeClaim`. The phase-1
  model `VerifierD1Defs` uses `challengeSpecD1a`, which has the same `decodeClaim`. Item A3
  checks that the two verifiers are equal (`rfl`). If they are not, the model is restated with
  `challengeSpecChunk .d1a`.
* The proof size is bounded by `nearAirV3D1_sizeMaxAligned = 6,927,206` (kernel-checked in
  phase 1), plus the hint: transactions plus new transactions ≤ 8 MiB, refunds ≤ 1.3 MB. This
  is well below the 64 MiB cap.

## 2. Dependency graph

The D0a split is reused: per-table views → link `GoodD1` → factor theorems → admission.

```
                    V0 AirD1 ✔ ─┬─ V1 relays ✔ (kib, plf, rid)
                                ├─ V2 txV3 view ──────────┐
                                ├─ V3 akmV3 view ─────────┤
                                ├─ V4 rcptV3D1 view ──────┤
                                ├─ V5 mrkV3@20 view ──────┤
                                └─ V6 21 unchanged views ─┤ (D0a theorems, reindexed)
 P0 public bindings D1 ───────────────────────────────────┤
 P1 prep lemmas ✔ (TxVerdict, LocalNative, TxNative) ─────┤
 P2 prepD1 decomposition ─────────────────────────────────┤
                                                          ▼
                                   L1 GoodD1 / LinkD1  (views + balance ⇒ GoodD1)
                                                          │
                     F1 FactorSoundD1 (prepD1 ok ∧ GoodD1 ⇒ RelD1a B0) ──► ExtractD1StmtT
                                                          │
 R1 renders (5 new tables, rcptV3D1, mrkV3@20) ─┐         │
 R2 FactorCompleteD1 (checkD1a ⇒ ∃ GoodD1 …) ───┼──► CompleteD1StmtT + header/aligned (FitsD1)
                                                          ▼
                                   A1 nearV3D1_admission_final (+ A2 hint codec, A3 model)
```

## 3. Items, sizes, status

Sizes are Lean lines. ✔ marks a finished item, with its measured size. Every other size is an
estimate, calibrated on the D0a counterparts (`Rcpt/` 71 k, `Render/` 75 k, `Assembly/` 96 k
lines).

| id | item | depends on | est. lines | status |
|---|---|---|---|---|
| **V0** | `Extract/AirD1`: table indices of `nearAirV3D1`; `getElem?_d1_same` (indices `< 25` other than 16 and 23 are `nearAirV3`'s); `TableLocal` from `HoldsP` | — | 90 | ✔ |
| **V1** | relay views `kib_view`, `plf_view`, `rid_view` (`TableLocal → ∃ es, Wf ∧ TableTraffic`, as `BndProof`) | — | 400 | ✔ |
| **V2** | `tx_view : TxViewStmt` (`Extract/TxView`, `TxProof`, `Tx/*`, 15 modules). One entry per 16-row op: the op constants, the flag algebra (`stage = s1 + s2`, `cand`, `wr`, gates), the written values (`mo`, `nk`), the memory times (`tp + d = op`, `d < 2^14`). Under byte hypotheses on the inputs, the seven chains give integer facts: `N > kn`, `N = kn + 1`, `N < Bd`, `amt ≥ C` / `aft = amt + dep`, the overflow and stake tests, and `okP = okC`. Reuses `RcptChain.chain`/`sumL`/`convS` | V0 | 2,190 | ✔ |
| V3 | `akmV3` view (part 1 done: `Extract/Akm/Rows` gives `segInfo`, a variable-length `SegAt`): segments (`Segments.segments_of`, as `AkeyProof`). The row FSM gives a token sequence `nonce[8] tag (GKI[18])? (opt (allowance[16])? STR count STR^count)?`, and a parser-simulation lemma per token against `Wire.pU64/pU8/pOption/pU128/pBytes/pVec/pU16` (+ `pString`'s `utf8Ok` from the class / pending-continuation / E0-ED-F0-F4 flags) gives `decodeAccessKey b = some k` with `fa ↔ k.perm = fullAccess` and the nonce lanes. Plus the AKMEM / VSLOT / VPOST / AKC traffic. The tx view's tooling (`Lane`, `eval_bitsN`, `cv_b`, the `im` traffic pattern) carries over | V0 | 2.5–4 k | next |
| V4 | `rcptV3D1` view: the six changes against D0a's receipt view, which goes through `TableLocal RcptV3.table`, 153 files. (a) Copy-and-modify the affected chain: first-row `tok`, `o2`, the last-row count, MEM time `r + 1 + T0`, the 14-bit age (needs the global MEM balance, as `RcptViewV3`) and MPOS `r + M0`. (b) Investigate a trace transport. Every changed expression is affine in public offsets, but `tok` is a ranged running sum, so (b) is likely blocked. | V0, P0 | 5–12 k | |
| V5 | `mrkV3` at `maxLog 20`. The D0a chain `MerkleEmpty.focus_local` → `MerklePublic.baseTable` (`maxLog 19`) → `Candidates/MerkleLog19` (1,472 lines, "height bound generalised from 15 to 19, every no-wrap rechecked") is tied to `maxLog 19`. It needs a `MerkleLog20` port: a copy with `2^19 → 2^20`; the largest no-wrap is `4·H + 4 < P`, which holds at `H = 2^20`. Mechanical | V0 | 1.5–2 k (copy) | |
| **V6** | `Extract/ViewsD1`: the ten `Assembly.ViewsV3` views (node, walk, head, val, uniq, ups, acct, akey, bnd, size) from `HoldsP nearAirV3D1` through `getElem?_d1_same`. The SHA, ChaCha, scheduler, srcp, qv and sort views enter D0a's link through `HoldsP nearAirV3`-level lemmas (L1), not through `ViewsV3` | V0 | 150 | ✔ (see log) |
| P0 | D1 public bindings: `pubOf (preparedBytesD1 p ov)` decoded. The D0a header and the nine segments keep their offsets. The extension `M0, T0, O0, TOK0` at `E0 = 322`. The six new segments: body-prefix send (cancels positions `8 … O0−1` of the D0a body receive), `TXP`, `SIG`, `PKEY`, `PLEAF`, `PRID`. `txOverhead` in `PH_WOVH`. `pubFit`. Reuses `Public/Prepared*` | — | 3–6 k | |
| **P1** | `txVerdict : TxVerdictStmt`, `prepLocalNative : PrepLocalNativeStmt` (+ `localApply_of_applyReceipt` with the outcome), `prepTxNative : PrepTxNativeStmt` (step simulation `prepTx_step`, `prepTxs_sim`) | — | 420 | ✔ |
| P2 | `prepD1` decomposition: `prepD1 cb h = ok p` ⇒ the D0a-shaped `prepClaimD1` facts (`walkD0`, contexts, sched), the decoded tx vectors, the T1 bound, both tx roots, `newTxs` sizes, the forwarded / compute checks, the header equalities, the RS body and `p`'s fields as functions of these | P1 | 2–4 k | |
| L1 | `GoodD1 B cb k h p x` (the D1 analogue of `GoodV3`: D1 witness shape, transaction run, local receipts, the `MEM`/`AKMEM` timelines, the read keys ⊆ `txKeys`, A7ᴰ¹ against the AIR's sums) and `LinkD1`: views + bus balance ⇒ `GoodD1`. The D0a link modules apply unchanged wherever `rcptV3D1` reduces to D0a's traffic at `T0 = M0 = TOK0 = 0, O0 = 8`. The new parts are the tx/credit ops ↔ `processTxs` (with P1), the access-key memory and the leaf/rid/key relays | V*, P0, P2 | 10–20 k | |
| F1 | `FactorSoundD1`: `prepD1 cb h = ok p ∧ GoodD1 … ⇒ checkD1a B0 cb (witnessOfV3D1 k x h) = ok ()`. Needs the D1 witness codec (`decodeStateWitnessD1 ∘ encode`, `pTxD1` round trip on the hint's raw transactions) and `applyNewChunkD1` = the tx prefix (P1) + `applyReceiptsC` over local then incoming receipts. The A7ᴰ¹ measure: the relation's main pre trie covers **all** `txKeys` (keys whose values are never read are absent, not revealed), whereas the AIR walks only the read keys, so `unfoldBytesD1 ≤` the AIR's running sums needs a monotonicity lemma for the unread keys' paths (see §5, R-2) | L1, P1, P2 | 15–30 k | |
| R1 | renders: `txV3`, `akmV3`, the relays, `rcptV3D1` (D0a's `HonestRcptQ` with the offsets), `mrkV3@20`; honest bus balance of the six D1 buses and of the changed MEM / MPOS / BYTES traffic | V* | 8–15 k | |
| R2 | `FactorCompleteD1`: `checkD1a B0 cb w = ok () ⇒ ∃ k h p x, GoodD1 …`, `hintOfD1`, heights at the D1a bounds (`FitsD1`: `txV3` ≤ 2^19 at NT0 + n_loc ≤ 8,192 ops, `akmV3` ≤ 2^22 by A7, `mrkV3` ≤ 2^20), `headerOk`, roll alignment | R1, P2 | 6–12 k | |
| A1 | `nearV3D1_admission_final`: `ExtractD1StmtT` + `CompleteD1StmtT` into `ZkFormal.Prover.Np.G.admission_v2H` (as `NearAdmission.nearV3_admission`) with `nearAirV3D1_npOkPg_g2`, the size bound, `NVu`, `tables_ne_nil`, profile facts | F1, R2 | 1–2 k | |
| A2 | hint wire codec: `decodeHintD1 (HintD1.encode h) = ok h`, split/join `readBorshBytes` framing (D0a's `HintCodec` pattern) | — | 0.3–0.6 k | |
| **A3** | `ModelTier.verifierD1_tier`: `npVerifierP challengeSpecD1a … = npVerifierP (challengeSpecChunk .d1a) …` (not `rfl`: the two `claimOk` matches differ in their instances, so the proof does a case split on `WfClaim.decode`); `paramsD1a_tier` (fuel, profile, cap and reduction fuel coincide); `relTier_d1a` | — | 40 | ✔ |
| | **total remaining** | | **≈ 57–125 k** | |

Calibration and reality check: the estimates for the large items (V4, L1, F1, R1, R2) are D0a's
proportions scaled by the new surface, with the design doc's assumed 2–3× over-run already
included. The finished items came in at the low end (V0 + V1 + P1 ≈ 0.9 k lines, about 5 s of
elaboration).

## 4. Statement corrections (candidate side, `D1/PrepD1Lemmas.lean`)

* **`ExtractD1Stmt` / `CompleteD1Stmt` use the tape `preparedBytesD1 p 0`, but the verifier
  (`prepD1b` = `preparedTapeD1`) uses `preparedBytesD1 p (txOverhead h)`.** With overhead 0, the
  AIR's `w.size` check (`8 MiB − OVH − Σ x ≥ 0`) does not count the hint's transaction vectors.
  The extracted witness carries them, so the phase-1 `ExtractD1Stmt` is (very likely) false: an
  accepted overhead-0 trace can extract a witness above 8 MiB, which `RelD1` rejects.
* **Decision (coordinator, 2026-10-14): accepted.** `ExtractD1StmtT` / `CompleteD1StmtT`
  (`D1/StmtsT.lean`, on the verifier's tape `preparedBytesD1 p (txOverhead h)`, completeness
  with `headerOk`) are the canonical targets. The overhead-0 drafts were removed from
  `PrepD1Lemmas.lean`; no module or tool referenced them. The `prepD1b` docstring now states
  `txOverhead`.

## 5. Risks and open questions (no spec change proposed so far)

* **R-1 (V4 volume).** D0a's receipt view is 70 k lines, and 153 files take
  `TableLocal RcptV3.table`. The six changed expressions touch the `tok` chain, the body
  offsets, the count, the MEM time with the age no-wrap, and MPOS. If the copy-and-modify
  footprint exceeds ≈ 15 k lines, the alternative is a candidate-side AIR change: keep `tableQ`
  verbatim and move the four offsets into a 1-row "prefix" table that emits the
  pre-incremented values on new buses. That is a phase-1 design revision (new
  `nearAirV3D1`, Rust prover change), so it needs the user's go-ahead, but it is not a
  spec or challenge change.
* **R-2 (A7ᴰ¹ over unread transaction keys); likely benign, to be confirmed in F1.**
  `RelD1a`'s `unfoldBytesD1` measures the main pre trie built over **all** `txKeys` (every
  transaction's signer account and access key, read or not). The AIR walks only the keys it
  reads (phase-1 decision 7). `partialTrie` = `buildFor (mkStore values)` never fails: it
  reveals exactly the nodes that lie on some key path *and* are in the witness store, and
  leaves every other subtree as `.hash`. `processTx` reads a key only at steps 5/6, so an
  undetermined unread key is no error. For the extracted witness, whose store holds only the
  AIR-revealed nodes and values, the extra keys therefore reveal nothing new. Every store node
  is already on a read path, and a value slot is revealed only for an exact key match.
  `unfoldBytesD1` then equals the AIR's count, which is ≤ `B0`. For completeness, the honest
  witness may reveal more (nearcore records prefetched reads), so its measure is ≥ the AIR's,
  as phase 1 noted. Obligation: a `buildFor` monotonicity / "store ⊆ read paths" lemma (part
  of F1, ≈ 0.5–1.5 k lines).
* **R-3 (budget).** The D0a closure is 5,953 s single-core (after the elab-budget lane) of the
  judge's 14,400 s. The D1 closure adds the D1 modules. The modules so far take < 1.3 s each.
  The V2–V4 and R1 module families are kept < 60 s per module.

## 6. Milestone log (summary; details in the log)

| date | milestone | theorems | modules (elab, s) |
|---|---|---|---|
| 2026-10-14 | V0, V1, P1 | `tableLocalD1`, `getElem?_d1_same`, `kib_view`, `plf_view`, `rid_view`, `txVerdict`, `prepLocalNative` (+ `localApply_of_applyReceipt`), `prepTxNative` (+ `prepTx_step`, `prepTxs_sim`) | 7 modules, each ≤ 1.2 s |
| 2026-10-14 | V6, A3, V3 part 1 | `nodeViewD1` … `sizeViewD1` (10), `verifierD1_tier`, `paramsD1a_tier`, `AkmProof.segInfo` | 3 modules, each ≤ 0.6 s |
| 2026-10-14 | V2 | `tx_view : TxViewStmt` (+ `chainN/B/C/T/Q/D/S`, `zN_iff`, `msum_val`, `debit_arith`, `credit_arith`, `verdict_debit/credit`, `opWf`, `rowLane`) | 15 modules, Σ ≈ 25 s (max `Tx.OpWf` 5.1 s) |
