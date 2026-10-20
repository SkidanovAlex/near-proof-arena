import ZkFormal.NearV3.D1.M.All
import ZkFormal.NearV3.D1.Extract.AirD1
import ZkFormal.NearV3.Assembly.LinkV3

/-!
# `ZkFormal.NearV3.D1.M.View` — **the view of `mrkV3` at height cap `2^20`** (V5)

Lane `v3-d1-phase2`, item V5.  D0a's `Assembly.mrkView` for `nearAirV3D1`'s table 23
(`mrkTableD1 = { MerkleEmpty.table with maxLog := 20 }`): the same statement (empty tree, or
the v1 Merkle view), proved by the generated copies `D1/M/Candidates/*` of D0a's chain at
`maxLog 20` (`scripts/rcpt_d1_copy.py --profile mrk`; the only delta is `height_le_m20`:
`height ≤ 2^20`; every field no-wrap of D0a's `MerkleLog19` holds at `2^20` unchanged).
-/

namespace ZkFormal.NearV3.D1.MrkD1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 ZkFormal.NearV3.Assembly

/-- **V5: `mrkV3`'s view in a `nearAirV3D1` trace.** -/
theorem mrkViewD1 {pub : List Fp} {tr : Trace Fp} (hH : HoldsP nearAirV3D1 pub tr) :
    ∃ e v, MrkWfE pub e v ∧
      TableTraffic ZkFormal.NearV3.Candidates.MerkleEmpty.table.interactions tr ZkFormal.NearV3.Assembly.T_MRK pub
        (mrkTrafficE pub e v) := by
  have hL : TableLocal tableE tr ZkFormal.NearV3.Assembly.T_MRK pub := ZkFormal.NearV3.D1.mrkD1Local hH
  have hF := ZkFormal.NearV3.Candidates.MerkleEmpty.focus_local hL ZkFormal.Near.T_MRK
  by_cases hc : ZkFormal.NearV3.Candidates.MerkleEmpty.countE.eval
      (ZkFormal.NearV3.Candidates.MerkleEmpty.focus tr ZkFormal.NearV3.Assembly.T_MRK) ZkFormal.Near.T_MRK 0 pub = 0
  · obtain ⟨hr, hz⟩ := ZkFormal.NearV3.Candidates.MerkleEmpty.empty_view_m20 hF hc
    refine ⟨true, default, ⟨fun _ _ _ => hc, hr⟩, fun b m => ?_⟩
    have h1 := hz b true m
    have h0 := hz b false m
    rw [ZkFormal.NearV3.Candidates.MerkleEmpty.focus_count] at h1 h0
    simp only [mrkTrafficE, ite_true, List.map_nil, List.count_nil]
    exact ⟨h1, h0⟩
  · obtain ⟨v, hw, ht⟩ := ZkFormal.NearV3.Candidates.MerkleEmpty.nonempty_view_m20 hF hc
    refine ⟨false, v, hw, fun b m => ?_⟩
    simpa only [ZkFormal.NearV3.Candidates.MerkleEmpty.focus_count, mrkTrafficE, Bool.false_eq_true,
      ite_false] using ht b m

end ZkFormal.NearV3.D1.MrkD1
