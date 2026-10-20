import ZkFormal.NearV3.D1.R.All
import ZkFormal.NearV3.D1.R.Delta.Traffic
import ZkFormal.NearV3.D1.Extract.AirD1
import ZkFormal.NearV3.Assembly.RcptCandidateMemoryVersion

/-!
# `ZkFormal.NearV3.D1.R.View` — **the view of `rcptV3D1`** (V4)

Lane `v3-d1-phase2`, item V4 (plan §7).  The D1 analogue of D0a's `rcptV3_view_nearAir`
(`Assembly/RcptViewV3`): from `rcptV3D1`'s local constraints, the public extension
(`ExtOk`: bytes, `M0, T0 < 2^24`, `O0 < 2^30`), the receipt header ranges and a bound
`≤ 2^25` on the versions the table reads from `MEM` (the global `MEM` balance gives it in
L1: versions are written by `acctV3` at `0`, by `txV3` at its op times and by `rcptV3D1` at
`r + 1 + T0`):

  `∃ ls, RcptV3WfD1 pub ls ∧ TableTraffic tableQD1.interactions … (rcptTraffic3D1 pub ls) ∧
     ∀ x ∈ flatR ls, x.q < 128`.

Proof: the generated copies of D0a's chain (`D1/R/Assembly/*`, hypothesis `LocalD1`) give
the D1 facts and the traffic on D0a's interactions with the body offset `O0`
(`ListChain.view_wf_d1`, `ListChain.view_traffic_d1`); `Delta/Traffic` shifts the `MEM` time
and the `MPOS` position.
-/

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RcptV3Proof RcptSkeleton

set_option maxRecDepth 16384 in
/-- Every extracted receipt has interval index `< 128` (D0a's `extracted_q_ltQ`). -/
theorem extracted_q_ltQ_d1 {tr : Trace Fp} {tt : Nat} {pub : List Fp} {y : RS}
    (h : ZkFormal.NearV3.D1.RcptD1.LocalD1 tr tt pub)
    (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) : (rcptOf tr tt y).q < 128 := by
  have F := route_receiver_d1 h lay
  have hz : 0 < y.Lv := by have hh := lay.pos; omega
  have hs : tr.cell tt (lkRow y 0) sV = 1 := by simpa using F.fld.st 0 hz
  have hf : tr.cell tt (lkRow y 0) fs = 1 := by simpa using F.fld.fs 0 hz
  have hq := repaired_first_receiver_q_d1 h h (route_height_d1 h lay 0 (by omega)) hs hf
  have he := F.consts 0 hz RcptV3.q (by simp [rconsts])
  simp only [Nat.add_zero] at he
  change cv tr tt y.s RcptV3.q < 128
  simpa only [cv, he] using hq

theorem view_q_d1 {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : ZkFormal.NearV3.D1.RcptD1.LocalD1 tr tt pub)
    {bs : List ListBlock} {e : Nat} (hc : ListChain tr tt 0 bs e) :
    ∀ x ∈ ZkFormal.NearV3.flatR (bs.map (ListBlock.view tr tt)), x.q < 128 := by
  intro x hx
  rw [flat_views] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨B, hB, hy⟩ := List.mem_flatMap.mp hy
  exact extracted_q_ltQ_d1 h ((hc.blocks B hB).layouts y hy)

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

namespace ZkFormal.NearV3.D1.RcptD1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.RcptV3 ZkFormal.V2
open ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof (ListBlock ListChain rcptOf)

/-- **The `rcptV3D1` view statement.** -/
def RcptD1ViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal tableQD1 tr t pub → ExtOk pub →
    ReceiptPublicRanges pub →
    (∀ m : List Fp, 0 < tableBusCount tableQD1.interactions tr t pub B_MEM false m →
      (m.getD 1 0).toNat ≤ 2 ^ 25) →
    ∃ ls, RcptV3WfD1 pub ls ∧ TableTraffic tableQD1.interactions tr t pub (rcptTraffic3D1 pub ls) ∧
      ∀ x ∈ flatR ls, x.q < 128

theorem recv_count_eq {tr : Trace Fp} {t : Nat} {pub : List Fp} (hx : ExtBytes pub) (b : Nat)
    (m : List Fp) :
    tableBusCount tableQD1.interactions tr t pub b false m =
      tableBusCount RcptV3.interactions tr t pub b false m := by
  have hid : fF ((t0V pub : Nat) : Fp) ((m0V pub : Nat) : Fp) b false = id := by
    funext m; unfold fF; rw [if_neg (by simp), if_neg (by simp)]; rfl
  have hrow : ∀ q, rowTraffic (RcptV3.interactions.map replI2) tr t q pub b false =
      rowTraffic RcptV3.interactions tr t q pub b false := by
    intro q
    rw [row_shift (t0E_eval hx tr t q) (m0E_eval hx tr t q) b false, hid, List.map_id]
  rw [tableQD1_interactions2, tableBusCount_eq, tableBusCount_eq]
  simp only [hrow]

/-- **V4: `rcptV3D1`'s view.** -/
theorem rcptD1_view : RcptD1ViewStmt := by
  intro tr pub t hQ hx hranges hmem
  have hL : LocalD1 tr t pub := { local_K hQ with ext := hx }
  obtain ⟨bs, e, hc⟩ := extract_lists_d1 hL
  have ht := ListChain.view_traffic_d1 hL hc
  have hprov : ∀ B ∈ bs, ∀ y ∈ B.receipts, (rcptOf tr t y).tprev ≤ 2 ^ 25 := by
    intro B hB y hy
    have hx' : rcptOf tr t y ∈ flatR (bs.map (ListBlock.view tr t)) := by
      rw [flat_views]
      exact List.mem_map.mpr ⟨y, List.mem_flatMap.mpr ⟨B, hB, hy⟩, rfl⟩
    let x := rcptOf tr t y
    let mm : Msg := [x.kslot, x.tprev, 0, x.bef.getD 0 0, x.lk.getD 0 0, x.st.getD 0 0]
    have hm : mm ∈ rcptRecvs3 (bs.map (ListBlock.view tr t)) B_MEM := memory_version_read hx'
    have hp' : 0 < tableBusCount tableQD1.interactions tr t pub B_MEM false mm.toFp := by
      rw [recv_count_eq hx.1, (ht B_MEM mm.toFp).2]
      exact List.count_pos_iff.mpr (List.mem_map.mpr ⟨mm, hm, rfl⟩)
    have hb := hmem mm.toFp hp'
    have hc' := extracted_previous_canonical hx'
    simpa [mm, x, Msg.toFp, Fp.toNat_ofNat, Nat.mod_eq_of_lt hc'] using hb
  refine ⟨_, ListChain.view_wf_d1 hL hc hranges hprov, ?_, view_q_d1 hL hc⟩
  unfold rcptTraffic3D1
  rw [traffic3G_shift]
  exact traffic_shift hx.1 ht

/-- `rcptD1_view` on `nearAirV3D1`'s table 16. -/
theorem rcptV3D1_view_nearAir {pub : List Fp} {tr : Trace Fp} (hH : HoldsP nearAirV3D1 pub tr)
    (hx : ExtOk pub) (hranges : ReceiptPublicRanges pub)
    (hmem : ∀ m : List Fp, 0 < tableBusCount tableQD1.interactions tr 16 pub B_MEM false m →
      (m.getD 1 0).toNat ≤ 2 ^ 25) :
    ∃ ls, RcptV3WfD1 pub ls ∧ TableTraffic tableQD1.interactions tr 16 pub (rcptTraffic3D1 pub ls) ∧
      ∀ x ∈ flatR ls, x.q < 128 :=
  rcptD1_view tr pub 16 (ZkFormal.NearV3.D1.rcptD1Local hH) hx hranges hmem

end ZkFormal.NearV3.D1.RcptD1
