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
| **V3** | `akm_view : AkmViewStmt` (`Extract/AkmView`, `AkmProof`, `Akm/*`, 15 modules). Each value segment decodes (`akm_decode`: `decodeAccessKey b = some k`, nonce = the first 8 bytes, `k.perm = FullAccess ⇔ t₁`, a FullAccess value is `nonce ‖ 1`, the nonce rows are exactly offsets 0…7). Built from the borsh walk (`field`, `u32field`, `body`, `str`, `methods`, `vecMethods`, `fcPerm`, `gki`, against `Wire.pU*`/`pString`/`pVec`/`pOption`), `body_utf8` (`utf8_rows`: the class / pending-count / E0-ED-F0-F4 automaton accepts only `utf8Ok`), and exact traffic on VBYTES/AKMEM/VSLOT/BYTES/AKC | V0 | 2,656 | ✔ |
| **V4** | `RcptD1.rcptD1_view : RcptD1ViewStmt` (`D1/R/View`). The D0a receipt-view chain is copied by `scripts/rcpt_d1_copy.py` from a declaration-level taint (`scripts/RcptTaint.lean`: 428 theorems / 126 modules); 21 hand-written deltas (`scripts/rcpt_d1_overrides.lean`, `D1/R/Delta/*`). `RcptV3WfD1` / `rcptTraffic3D1` (`D1/R/ViewDefs`) carry `TOK0`, `M0`, `O0`, `T0`. Hypotheses for L1: `ExtOk pub` (extension bytes, `M0, T0 < 2^24`, `O0 < 2^30`), `ReceiptPublicRanges`, `MEM` versions ≤ 2^25 | V0 | 11.0 k generated + 1.3 k hand | ✔ (≈ 125 s serial, 131 modules) |
| **V5** | `MrkD1.mrkViewD1` (`D1/M/View`): D0a's `mrkView` for `mrkTableD1` (`maxLog 20`). Generated copies `D1/M/*` (`--profile mrk`, 47 theorems / 5 modules); the only delta is `height_le_m20` | V0 | 1.5 k | ✔ (≈ 27 s) |
| **V6** | `Extract/ViewsD1`: the ten `Assembly.ViewsV3` views (node, walk, head, val, uniq, ups, acct, akey, bnd, size) from `HoldsP nearAirV3D1` through `getElem?_d1_same`. The SHA, ChaCha, scheduler, srcp, qv and sort views enter D0a's link through `HoldsP nearAirV3`-level lemmas (L1), not through `ViewsV3` | V0 | 150 | ✔ (see log) |
| P0 | D1 public bindings: `pubOf (preparedBytesD1 p ov)` decoded. The D0a header and the nine segments keep their offsets. The extension `M0, T0, O0, TOK0` at `E0 = 322`. The six new segments: body-prefix send (cancels positions `8 … O0−1` of the D0a body receive), `TXP`, `SIG`, `PKEY`, `PLEAF`, `PRID`. `txOverhead` in `PH_WOVH`. `pubFit`. Reuses `Public/Prepared*` | — | 3–6 k | parts 1–3 ✔ (`D1/Public/Ext`, `Layout`, `Split`: header, extension → `ExtOk`, `pubCountD1_split`); the new segments' records and `PreparedBindingsD1` remain |
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
* **R-4 (V4: the re-proof is ~22 k lines; the "small prefix table" fallback does not hold; decision
  requested, 2026-10-14).**
  * *Measured.* D0a's receipt view (`Assembly.RcptViewV3`) has a closure of 1,331 modules. Of
    these, **228 modules (22,454 lines)** mention `RcptV3.table` / `tableQ` / `tableR` directly,
    and every lemma there carries `hL : TableLocal RcptV3.table …`. A D1 trace satisfies
    `TableLocal RcptD1.tableQD1` instead, so the re-proof means copying that chain (≥ 22 k
    lines, mostly verbatim, with local edits). That is over the 15 k threshold.
  * *A trace transport does not rescue it.*
    * The `tok` register is byte-decomposed (`tok₁₅ ← bitsX 31 8`, carries in `xb`), so
      starting it at `TOK0` instead of `0` cannot be shifted out.
    * The deposit age needs `r + T0 − tprev < 2¹⁴`, whereas `tableQ`'s 13-bit window cannot
      hold `r + k` for `k` up to `T0 ≈ 8,192`.
  * *The verbatim-`tableQ` fallback (coordinator decision 2) needs more than a prefix table.*
    These parts are small:
    * a "virtual" rcpt header: `PH_N = n`, `PH_BURNT = burnt − TOK0`, body
      `= u32 0 ‖ encodeReceipts(incoming refunds)`; only `rcptV3` and `mrkV3` read these;
    * an `mrkV3` remap: its count read from a new `M0 + n` field, its `MPOS` positions
      shifted by `−M0`;
    * `plfV3` sending `pos − M0`.

    The memory ordering is the obstacle. `tableQ` writes accounts at `r + 1` and its readers
    accept only `tprev ∈ [r − 2¹³ + 1, r]`. So the transactions' account writes (which come
    first) would have to happen at time ≤ 0. That needs a **memory bridge**: the transaction
    ops on their own bus `MEMT`, plus a 16-rows-per-account table that receives `acctV3`'s
    time-0 value, opens the `MEMT` chain, closes it, and re-emits the post-transaction value
    at time 0 for the receipts. It also needs **per-account uniqueness** of the bridge rows:
    two bridge chains for one account would let the prover run the account twice in
    parallel, which is unsound. That is a new table with sorting or uniqueness, Rust
    prover work and a new link argument. It is not a small prefix table.
  * **Decision requested.** Either (a) V4 by copy-and-modify on the phase-1 AIR (≈ 22–30 k
    mechanical lines, no AIR change, about 2–4 % more judge elaboration), or (b) the
    bridge redesign above (AIR + prover + conformance work, plus a bridge view and a
    uniqueness proof, ≈ 3–6 k proof lines, and V5/P0/P2 change shape). The lane recommends
    (a): it is mechanical and low-risk, and (b)'s uniqueness argument is new soundness
    surface. Until you decide, the lane works only on items that are the same under both
    choices.
* **R-3 (budget).** The D0a closure is 5,953 s single-core (after the elab-budget lane) of the
  judge's 14,400 s. The D1 closure adds the D1 modules. The modules so far take < 1.3 s each.
  The V2–V4 and R1 module families are kept < 60 s per module.

## 6. Milestone log (summary; details in the log)

| date | milestone | theorems | modules (elab, s) |
|---|---|---|---|
| 2026-10-14 | V0, V1, P1 | `tableLocalD1`, `getElem?_d1_same`, `kib_view`, `plf_view`, `rid_view`, `txVerdict`, `prepLocalNative` (+ `localApply_of_applyReceipt`), `prepTxNative` (+ `prepTx_step`, `prepTxs_sim`) | 7 modules, each ≤ 1.2 s |
| 2026-10-14 | V3 | `akm_view` (+ `akm_decode`, `body_utf8`, `utf8_rows`, `str`, `vecMethods`, `fcPerm`, `gki`) | 15 modules, Σ ≈ 22 s (max `Akm.Decode` 3.4 s) |
| 2026-10-14 | V6, A3, V3 part 1 | `nodeViewD1` … `sizeViewD1` (10), `verifierD1_tier`, `paramsD1a_tier`, `AkmProof.segInfo` | 3 modules, each ≤ 0.6 s |
| 2026-10-14 | V5, P0 (1–3) | `mrkViewD1`; `extOk_prepared`, `m0V/t0V/o0V/tok0V_prepared`, `descriptorD1_msgs`, `pubMsgsD1_split`, `pubCountD1_split` | 7 + 3 modules |
| 2026-10-14 | V4 | `rcptD1_view`, `rcptV3D1_view_nearAir` (+ `traffic_shift`, `chainByteMsgs_eq_viewG`, `tok_first`, `o2_first`, `count_last`, `age_row`, `local_K`, `memD1`) | 131 modules, ≈ 125 s serial (max `CharClass` 27 s) |
| 2026-10-14 | V2 | `tx_view : TxViewStmt` (+ `chainN/B/C/T/Q/D/S`, `zN_iff`, `msum_val`, `debit_arith`, `credit_arith`, `verdict_debit/credit`, `opWf`, `rowLane`) | 15 modules, Σ ≈ 25 s (max `Tx.OpWf` 5.1 s) |

## 7. V4: copy-and-modify plan (coordinator decision (a), 2026-10-14) — done

**As built (checkpoint 4, log milestone 5).** The declaration-level taint is 428 theorems in 126 modules, not the module-level 564. Copies keep their **original namespace** and are named `N_d1`, so that name resolution in a copy is the original's; a copy imports only modules already in its original's import closure. The hypothesis is the bundle `LocalD1` (`TableLocal rcptK ∧ ExtOk`). The rest of this section is the plan as written before the build.

**What must be copied (measured).** Inside the closure of `Assembly.RcptViewV3` (1,325 modules),
93 modules mention the receipt table directly (`TableLocal RcptV3.table`, `tableQ`, `tableR`,
`ReceiptCandidateRouting.candidateTable`). Their forward import taint is **564 modules, 45,294
lines**: 93 under `Rcpt/` and 471 under `Assembly/`.

The mapping D0a module → D1 copy (`ZkFormal.NearV3.D1.R.<suffix>`) is in
`docs/zk-formal/v3-d1-v4-map.tsv`. That list is an upper bound. Many `Assembly` modules import
a tainted module only for unrelated declarations, so the generator must taint at
**declaration** level: copy a declaration only when its type or value refers, transitively, to
a tainted constant. The expected result is well below the module-level bound. The 22,454 lines
of the 228 directly-mentioning modules are the practical lower bound.

**Generator (to build; `zk-formal/scripts/`).**
1. A Lean metaprogram (as `scripts/TypeHashes.lean`) walks the `RcptViewV3` closure. It marks
   as tainted every constant whose type or value mentions `RcptV3.table`, `tableQ`, `tableR`,
   `candidateTable` or the view statement `RcptV3ViewStmt`, and propagates the mark.
2. Source copy, per tainted declaration, using the declaration ranges (the model-split lane's
   `DeclInfo` technique):
   * each copy goes into `D1/R/<module>.lean` under the namespace `ZkFormal.NearV3.D1.R.<orig ns>`;
   * every reference to a tainted constant is rewritten to its copy;
   * untainted references stay fully qualified to the D0a original, so originals and copies
     never clash;
   * `TableLocal RcptV3.table` becomes `TableLocal RcptD1.tableQD1` (the constraints
     themselves: through a membership-transport lemma; see below).
3. Constraint membership: one lemma
   `memD1 : e ∈ RcptV3.table.constraints → e ∉ changed → e ∈ RcptD1.tableQD1.constraints`
   (`replC` is the identity off `substC`, a decidable fact). Copied proofs that use an
   unchanged constraint go through it. Only the proofs that touch one of the six changed
   expressions fail. Those are rewritten **by hand into small dedicated delta lemmas**:
   * `D1/R/Delta/Tok`: the first-row `tok = TOK0` and the token totals;
   * `Delta/Body`: `o2 = O0` and the body offsets;
   * `Delta/Count`: `r + rowE + M0 = PH_N`;
   * `Delta/Mem`: the MEM write time `r + 1 + T0`;
   * `Delta/Age14`: the 14-bit deposit age, `xb52…65`;
   * `Delta/Mpos`: the leaf position `r + M0`.

   A later refactor could then re-unify the two chains by parameterising over the offsets.
4. The view statement `RcptV3D1ViewStmt` is `RcptV3ViewStmt` with `rcptTraffic3` using the D1
   times and positions, and `RcptV3Wf` with `toks.head = TOK0`, `count + M0 = PH_N`, body
   offsets from `O0`.

**Elaboration estimate.** D0a's mean is 2.2 s per module, so the module-level upper bound of
564 copies is ≈ 1,240 s serial. The declaration-level copy is expected at ≈ 400–900 s. Judge
estimate for the D1a certificate closure:

| part | estimate (s, serial) |
|---|---|
| D0a closure (shared; elab-budget figure) | 5,953 |
| D1 phase-2 modules so far (V0–V3, P1, A3), ≈ 50 modules | ≈ 70 |
| V4 copies | ≈ 400–1,240 |
| V5 + P0 + P2 + L1 + F1 + R1 + R2 + A1/A2 (≈ 600–1,000 modules at 1–3 s) | ≈ 1,000–2,500 |
| **total** | ≈ 7,400–9,800 of the 14,400 budget (51–68 %) |

This assumes the D0a assembly roots that D1 does not use are dropped from the D1 closure.
