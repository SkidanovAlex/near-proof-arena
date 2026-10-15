import ZkFormal.NearV3.D1.Public.Ranges
import ZkFormal.NearV3.D1.R.ViewDefs

/-!
# `ZkFormal.NearV3.D1.Link.Count` — the receipt count of the D1 statement (L1 delta)

Lane `v3-d1-phase2`, item L1 (a semantic delta of the generated link copies).  In D0a,
`PH_N = n` (`prepBody_count_guard`).  In D1, `PH_N = M0 + n` (`prepD1_count_bound`) and the
receipt view counts `|flatR| + M0 = PH_N` (`RcptV3WfD1.count`), so the view still has exactly
the hint's `n` incoming receipts:

* `prepD1_hn_le`: `n ≤ 5000` (the compute guard `(|locals| + n − 1)·G < gasLimit ≤ 10¹⁵`);
* **`rcpt_count_d1`**: `|flatR ls| = h.n` for the receipt view on the verifier's tape.
-/

namespace ZkFormal.NearV3.D1.Link

open NearSpec NearSpecV3 ZkFormal.V2 ZkFormal.Algebra ZkFormal.NearV3.Public ZkFormal.NearV3.D1
open ZkFormal.NearV3.D1.Public

/-- The hint's incoming-receipt count is at most 5000. -/
theorem prepD1_hn_le {cb : Bytes} {h : HintD1} {q : PrepD1} (hp : prepD1 cb h = .ok q) :
    h.n ≤ 5000 := by
  obtain ⟨w, hw, rfl⟩ := prepD1_spec hp
  have hg := prepClaimD1_gas_limit hw.claim
  have hc := hw.compute
  change w.pc.ctxB2.gasLimit ≤ _ at hg
  unfold PrepD1Run.nr at hc
  unfold maxGasLimitD0 at hg
  unfold Params.G Params.newActionReceiptExec Params.transferExec at hc
  omega

/-- The prepared header's count is `M0 + n` and below `2^32`. -/
theorem prepD1_hdr_n {cb : Bytes} {h : HintD1} {q : PrepD1} (hp : prepD1 cb h = .ok q) :
    q.base.hdr.n = q.m0 + h.n ∧ q.base.hdr.n ≤ 13192 := by
  obtain ⟨h1, h2⟩ := prepD1_count_bound hp
  exact ⟨h1, by unfold NT0 at h2; omega⟩

/-- **The receipt view has exactly the hint's `n` receipts.** -/
theorem rcpt_count_d1 {cb : Bytes} {h : HintD1} {q : PrepD1} {ov : Nat} {ls : ZkFormal.NearV3.RcptV3Vs}
    (hp : prepD1 cb h = .ok q)
    (hw : RcptD1.RcptV3WfD1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 q ov)) ls) :
    (ZkFormal.NearV3.flatR ls).length = h.n := by
  have hr := prepD1_roots hp
  have hc := hw.count (fun i _ => pubNat_pubOf_lt _ _)
  obtain ⟨hn, hb⟩ := prepD1_hdr_n hp
  have hm := (prepD1_m0_t0 hp).1
  unfold NT0 at hm
  rw [preparedD1_receipt_count q ov hr (by omega), m0V_prepared q ov hr (by omega)] at hc
  omega

end ZkFormal.NearV3.D1.Link
