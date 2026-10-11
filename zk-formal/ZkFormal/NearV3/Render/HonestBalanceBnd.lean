import ZkFormal.NearV3.Render.HonestBalanceAkc
import ZkFormal.NearV3.Assembly.RoutingPhysicalBalance
import ZkFormal.NearV3.Assembly.RoutingPhysicalMessages
import ZkFormal.NearV3.Assembly.RoutingCounterTraffic

/-!
# Honest BND balance (`rcptV3` ↔ `bndV3`) and the ranked honest receipt trace

The receipt table chains boundary-lookup use counters (`uB`) through `bndV3`.  No constraint
reads `uB` (`counter_free`), so the honest receipt rows may carry the physical use ranks of
each boundary key (`counterPatch … physicalBoundaryRank`, the routing lane's construction):
the ranked honest trace `rcptTraceB` is locally legal, has the same traffic as
`rcptTraceNative` on every bus but BND, and on BND sends/receives the physical rank chain
`physicalCounterMessages`.  The boundary provider over `boundaryEntries bounds keys`
(`bndTraffic`) closes that chain (`physical_counter_balance`), given that every physical
lookup key is a provider row (coverage — the public boundary ownership obligation; with
`physical_provider_render` it is `key ∈ Public.boundaryRecords`).
-/

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof
open ZkFormal.NearV3.Render RoutingQCandidate RoutingBoundedLayout

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem arith_counter_free :
    receiptArithmeticCandidate.constraints.all (fun e => !(usesCounter e)) = true := by decide

/-- The ranked honest receipt trace. -/
def rcptTraceB (pub : List Fp) (x : RcptInput) : Trace Fp :=
  counterPatch (rcptTraceNative pub x) 0 (physicalBoundaryRank (rcptTraceNative pub x) 0)

def rcptTraceAlignedB (pub : List Fp) (x : RcptInput) : Trace Fp := pinTrace (rcptTraceB pub x) 0

/-- **The honest receipt traffic**: the native list's traffic, with the BND counters ranked. -/
def rcptTrafficB (pub : List Fp) (x : RcptInput) : Traffic :=
  ⟨fun b => if b = B_BND then physicalCounterMessages (rcptTraceNative pub x) 0 true
      else (rcptTraffic3 pub (nativeRcptLists pub x)).sends b,
   fun b => if b = B_BND then physicalCounterMessages (rcptTraceNative pub x) 0 false
      else (rcptTraffic3 pub (nativeRcptLists pub x)).recvs b⟩

theorem rcptTrafficB_other (pub : List Fp) (x : RcptInput) (b : Nat) (hb : b ≠ B_BND) :
    (rcptTrafficB pub x).sends b = (rcptTraffic3 pub (nativeRcptLists pub x)).sends b ∧
    (rcptTrafficB pub x).recvs b = (rcptTraffic3 pub (nativeRcptLists pub x)).recvs b := by
  simp [rcptTrafficB, hb]

theorem rcptTraceB_local (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x) :
    TableLocal receiptArithmeticCandidate (rcptTraceB pub x) 0 pub := by
  have hL := rcptTraceNative_local pub x ok
  refine ⟨hL.log_ge, hL.log_le, ?_, ?_⟩
  · intro r hr e he
    have hf : usesCounter e = false := by
      have := List.all_eq_true.mp arith_counter_free e he
      simpa using this
    rw [rcptTraceB, counterPatch_eval _ e hf]
    exact hL.constr r hr e he
  · intro r hr i hi e he
    have hf : usesCounter e = false := by
      have := List.all_eq_true.mp multiplicities_counter_free e (List.mem_flatMap.mpr ⟨i, hi, he⟩)
      simpa using this
    rw [rcptTraceB, counterPatch_eval _ e hf]
    exact hL.bits r hr i hi e he

theorem rcptTraceB_traffic (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x) :
    TableTraffic RcptV3.interactions (rcptTraceB pub x) 0 pub (rcptTrafficB pub x) := by
  have hL0 := rcptTraceNative_local pub x ok
  obtain ⟨bs, e, hc⟩ := ReceiptCandidateProof.extract_lists hL0
  have hT := ReceiptCandidateProof.ListChain.view_traffic hL0 hc
  rw [native_chain pub x ok hc] at hT
  intro b m
  by_cases hb : b = B_BND
  · subst hb
    have h1 := physical_counter_count (rcptTraceNative pub x) 0 pub true m
    have h2 := physical_counter_count (rcptTraceNative pub x) 0 pub false m
    exact ⟨by rw [rcptTraceB]; simpa [rcptTrafficB] using h1, by rw [rcptTraceB]; simpa [rcptTrafficB] using h2⟩
  · have h1 := counterPatch_other_bus (rcptTraceNative pub x) 0 pub
      (physicalBoundaryRank (rcptTraceNative pub x) 0) b hb true m
    have h2 := counterPatch_other_bus (rcptTraceNative pub x) 0 pub
      (physicalBoundaryRank (rcptTraceNative pub x) 0) b hb false m
    obtain ⟨hs, hr⟩ := rcptTrafficB_other pub x b hb
    refine ⟨?_, ?_⟩
    · show tableBusCount RcptV3.interactions (rcptTraceB pub x) 0 pub b true m = _
      rw [hs]; exact h1.trans (hT b m).1
    · show tableBusCount RcptV3.interactions (rcptTraceB pub x) 0 pub b false m = _
      rw [hr]; exact h2.trans (hT b m).2

/-- **Repaired receipt table completeness with ranked boundary counters** (the honest rows
for render assembly): local legality, exact traffic `rcptTrafficB`, aligned height. -/
theorem rcpt_aligned_completeB (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x) (t : Nat) :
    TableLocal RcptV3.tableR (rcptTraceAlignedB pub x) t pub ∧
      TableTraffic RcptV3.interactions (rcptTraceAlignedB pub x) t pub (rcptTrafficB pub x) ∧
      (rcptTraceAlignedB pub x).log t % 3 = 1 := by
  refine ⟨tableLocal_pin t (rcptTraceB_local pub x ok), tableTraffic_pin t (rcptTraceB_traffic pub x ok), ?_⟩
  have h22 : (rcptTraceB pub x).log 0 = 22 := rfl
  show (rcptTraceB pub x).log 0 % 3 = 1
  rw [h22]

/-- **BND balances** between the ranked honest receipt table and the boundary provider over
`boundaryEntries bounds keys`, given coverage of every physical lookup key. -/
theorem honest_bnd_balance (pub : List Fp) (x : RcptInput)
    (bounds : List (Option NearSpec.Bytes × Option NearSpec.Bytes))
    (hc : ∀ r ∈ physicalActiveRows (rcptTraceNative pub x) 0,
      physicalBoundaryKey (rcptTraceNative pub x) 0 r ∈
        (boundaryEntries bounds (physicalBoundaryKeys (rcptTraceNative pub x) 0)).map BndE.rec4) :
    ((bndTraffic (boundaryEntries bounds (physicalBoundaryKeys (rcptTraceNative pub x) 0))).sends B_BND ++
        (rcptTrafficB pub x).sends B_BND).Perm
      ((rcptTrafficB pub x).recvs B_BND ++
        (bndTraffic (boundaryEntries bounds (physicalBoundaryKeys (rcptTraceNative pub x) 0))).recvs B_BND) := by
  have h := physical_counter_balance (rcptTraceNative pub x) 0 _
    (boundaryEntries_nodup bounds _) hc (physicalEntries_usage_all bounds _ 0)
  simpa [bndTraffic, bndSends, bndRecvs, rcptTrafficB, show B_BND ≠ B_BNDP by decide] using h

end ZkFormal.NearV3.Assembly.RcptSkeleton
