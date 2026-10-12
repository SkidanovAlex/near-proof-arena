# integration/v3-20261012d (2026-10-12)

Branch created from origin/lane/v3-link-rest at 3d109cf2 (soundness complete: `extractV3`, table 20 = SrcpDD).

## Merges
* **origin/lane/v3-render-sched (a40c1bbd)** — merge commit bfd7a1c8. Only textual conflict:
  `ZkFormal/V3/Integration.lean` imports (union, duplicates removed). Files edited on both sides
  (`RenderV3RcptTrieSide`, `TrieSide`, `SizeBudgetAccepted`, `RenderV3SrcpSha`, `RenderV3RcptSha`,
  Codec*) auto-merged: link-rest's table-20 changes (`A.ddTraffic`, `A.sizeBlocks`, `dd_size_sends`) and
  render-sched's conjuncts (S0F, forwarding pin after `hctx`, `ExtOf valTraffic`) are in disjoint hunks;
  everything builds unchanged — no lemma needed re-proving. render-sched did not change `nearAirV3`.
* **origin/lane/v3-render-chacha (40d4b8e1)** — merge commit 6e894916, no conflicts (Integration imports
  auto-merged). `ChachaWords.coreMidW/runMid_stW` (copies of `A9Words.coreMid/runMid_st`) kept as is.

## New
* `Render/CompleteV3Chacha.lean`: **`chachaSideV3 : ChachaSideV3`** (repackages `chacha_buses_balanced`;
  `GrantWit`/`NatRes`/forwarding premises unused), **`completeV3 : CompleteV3Stmt`**.
* `Assembly/AdmissionV3.lean`: **`nearV3_admission_final`** (art, pub, hpub, himpl ⊢
  `AdmissionStatement challengeParamsD0a art`) = `nearV3_admission_of extractV3 completeV3`;
  intermediate `nearV3_admission_of_chacha'` / `''` (from `ChachaSideV3`). Name `nearV3_admission` is
  already taken by the generic reduction in `NearAdmission.lean`, hence `_final`.
* Audit `test/AuditAdmissionV3.lean` (guarded `#check` of the final statement; axioms
  `[propext, Classical.choice, Quot.sound]` for the certificate, `completeV3`, `chachaSideV3`, `extractV3`).

## Size
`#eval sizeMaxAligned nearAirV3.toAir ({ Params.default with auxGroup := 2 })` = **6,435,489** (scratch
file; also `nearV3_sizeMaxAligned` by kernel `decide`). `v3MaxInner = 6,435,489`, `v3MaxHintBytes =
1,953,115`: 4 + 1,953,115 + 6,435,489 = 8,388,608; honest hints ≤ 1,295,025 fit.

## Verification
* Heavy modules one at a time (CodecEndInt, CodecRecInt, CodecHeader, HorizontalAuxCheck) at 16G: ok.
* `lake build ZkFormal.V3.Integration`: 4,692 jobs, ok.
* Reverse-import dependents of all modules changed vs. 3d109cf2, a40c1bbd, 40d4b8e1 (140 changed,
  2,787 dependents, 153 top-level modules): `lake build` of the 153 tops, 5,357 jobs, 0 errors (20G, no OOM).
* Audits clean: AuditExtractV3, AuditCompleteV3, AuditNearV3Admission, AuditTable20, AuditSchedBuses,
  AuditCodecVbytes, AuditMposBal, AuditRcptTrieSide, AuditUpsS0F, AuditCodecTriePin, AuditLinkCore,
  AuditA9Link, AuditA7SegMatch, AuditChachaBus, AuditAdmissionV3.
* `make pin-check` ok; no sorry/axiom/native_decide/implemented_by added; no pinned/challenge/oracle file touched.

## Remaining
The D0a certificate `nearV3_admission_final` has no open proof obligation; its only premises are the
artifact's implementation connection `himpl` (and `hpub`), as in every earlier route.
