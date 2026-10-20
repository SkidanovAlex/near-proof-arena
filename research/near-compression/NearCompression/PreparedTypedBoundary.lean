import NearCompression.PreparedTypedBus
import NearCompression.PreparedControlBoundary

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

def preparedTypedBoundarySegment (last : Bool) : PubSeg :=
  {bus:=if last then 1 else 0,send:=false,width:=51,countAt:=if last then 4 else 0,start:=if last then 63 else 12}
def preparedTypedPublicBoundary (pub : List Fp) (last : Bool) : List Fp :=
  (List.range 51).map (fun i=>pub.getD ((if last then 63 else 12)+i) 0)
def preparedTypedPublicGas (pub : List Fp) (last : Bool) : Nat :=
  preparedGasWord (fun i=>(pub.getD ((if last then 63 else 12)+7+i) 0).toNat)
theorem prepared_typed_boundary_record (pub : List Fp) (last : Bool) :
    (preparedTypedBoundarySegment last).record pub 0=preparedTypedPublicBoundary pub last := by
  cases last <;> rfl

theorem prepared_typed_boundary_no_receives (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (last : Bool) (message : List Fp) :
    busCount (preparedTypedBusAir ec cc boundary count).toAir tr pub (if last then 1 else 0) false message=0 := by
  cases last <;>
    simp only [busCount,busCount.go,preparedTypedBusAir,preparedTypedBusExecTable,preparedTypedBusDataTable,Nat.add_zero,
      Bool.false_eq_true,ite_false,ite_true] <;>
    rw [ZkFormal.Chacha.tableBusCount_eq,ZkFormal.Chacha.tableBusCount_eq] <;>
    simp only [ZkFormal.Chacha.rowTraffic,List.flatMap_cons,List.flatMap_nil,preparedTypedBusFetch,
      preparedTypedBusReceive,preparedTypedBusPublish,Nat.reduceEqDiff,Bool.true_eq_false,
      and_false,false_and,ite_false,List.append_nil]
  all_goals
    have empty (rows : List Nat) : rows.flatMap (fun _=>([] : List (List Fp)))=[] := by
      induction rows <;> simp_all
    rw [empty,empty]
    rfl

theorem prepared_typed_boundary_public_unique (ec cc boundary : List Expr) (count : Nat)
    (pub : List Fp) (counts : preparedExecBoundaryCountsCheck pub=true)
    (last : Bool) (message : List Fp)
    (positive : pubCount (preparedTypedBusAir ec cc boundary count) pub (if last then 1 else 0) false message≠0) :
    message=preparedTypedPublicBoundary pub last := by
  have counts:=of_decide_eq_true counts
  change (preparedTypedBoundarySegment false).count pub=1 ∧ (preparedTypedBoundarySegment true).count pub=1 at counts
  unfold pubCount at positive
  obtain ⟨entry,member⟩:=List.exists_mem_of_length_pos (Nat.pos_of_ne_zero positive)
  obtain ⟨member,eq⟩:=List.mem_filter.mp member
  have eq:=of_decide_eq_true eq
  subst entry
  unfold pubMsgs at member
  obtain ⟨seg,segments,messages⟩:=List.mem_flatMap.mp member
  obtain ⟨msg,inSegment,eq⟩:=List.mem_map.mp messages
  simp only [preparedTypedBusAir,List.mem_cons,List.not_mem_nil,or_false] at segments
  cases last
  · rcases segments with rfl|rfl|rfl
    · cases eq
      change message∈(preparedTypedBoundarySegment false).msgs pub at inSegment
      simp only [PubSeg.msgs,counts.1,List.range_one,List.map_cons,List.map_nil,List.mem_singleton] at inSegment
      exact inSegment.trans (prepared_typed_boundary_record pub false)
    · cases eq
    · cases eq
  · rcases segments with rfl|rfl|rfl
    · cases eq
    · cases eq
      change message∈(preparedTypedBoundarySegment true).msgs pub at inSegment
      simp only [PubSeg.msgs,counts.2,List.range_one,List.map_cons,List.map_nil,List.mem_singleton] at inSegment
      exact inSegment.trans (prepared_typed_boundary_record pub true)
    · cases eq

/-- Actual natural bus balance binds the complete51-field entry/exit record;
the CODE receive bus2 and public CODE bus3 cannot discharge boundary traffic. -/
theorem prepared_typed_boundary_bound (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (holds : HoldsP (preparedTypedBusAir ec cc boundary count) pub tr)
    (counts : preparedExecBoundaryCountsCheck pub=true) (last : Bool) (r : Nat)
    (hr : r<tr.height 0) (endpoint : if last then r+1=tr.height 0 else r=0) :
    (preparedExecBoundaryInteraction boundary last).msgVal tr 0 r pub=preparedTypedPublicBoundary pub last := by
  have active : (preparedExecBoundaryInteraction boundary last).multNat tr 0 r pub≠0 := by
    cases last <;> simp only [Bool.false_eq_true,ite_false,ite_true] at endpoint ⊢ <;>
      simp [Interaction.multNat,Interaction.multNat.go,preparedExecBoundaryInteraction,
        Expr.eval,Expr.evalWith,rowEnv,endpoint]
  have member : preparedExecBoundaryInteraction boundary last∈(preparedTypedBusExecTable ec boundary).interactions := by
    cases last <;> simp [preparedTypedBusExecTable,preparedExecBoundaryInteraction]
  have traffic:=ZkFormal.Chacha.tableBusCount_pos hr member active
  let message:=(preparedExecBoundaryInteraction boundary last).msgVal tr 0 r pub
  have nonzero : busCount (preparedTypedBusAir ec cc boundary count).toAir tr pub (if last then 1 else 0) true message≠0 := by
    change tableBusCount (preparedTypedBusExecTable ec boundary).interactions tr 0 pub (if last then 1 else 0) true message+
      (tableBusCount (preparedTypedBusDataTable cc).interactions tr 1 pub (if last then 1 else 0) true message+0)≠0
    change tableBusCount (preparedTypedBusExecTable ec boundary).interactions tr 0 pub (if last then 1 else 0) true message≠0 at traffic
    omega
  have sendZero : pubCount (preparedTypedBusAir ec cc boundary count) pub (if last then 1 else 0) true message=0 := by
    apply ZkFormal.Chacha.pubCount_zero
    intro seg member _
    simp only [preparedTypedBusAir,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> decide
  have balance:=holds.balance (if last then 1 else 0) message
  rw [sendZero,prepared_typed_boundary_no_receives,Nat.add_zero,Nat.zero_add] at balance
  apply prepared_typed_boundary_public_unique ec cc boundary count pub counts last message
  rw [←balance]
  exact nonzero

theorem prepared_typed_boundary_gas (count localCount : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir count localCount) pub tr)
    (counts : preparedExecBoundaryCountsCheck pub=true) (last : Bool) (r : Nat)
    (hr : r<tr.height 0) (endpoint : if last then r+1=tr.height 0 else r=0) :
    preparedExecWord64 (tr.cell 0 r) 299=preparedTypedPublicGas pub last := by
  have balanced:=holds
  rw [prepared_typed_bus_literal_air] at balanced
  have message:=prepared_typed_boundary_bound _ _ _ count tr pub balanced counts last r hr endpoint
  have limb (i : Nat) (hi : i<4) :
      preparedCodeLimb (tr.cell 0 r) (299+16*i)=pub.getD ((if last then 63 else 12)+7+i) 0 := by
    have h:=congrArg (fun msg:List Fp=>msg.getD (7+i) 0) message
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3:=by omega
    rcases cases with z|z|z|z <;> subst i
    all_goals cases last
    all_goals change (preparedCodeBits _).eval tr 0 r pub=_ at h
    all_goals rw [prepared_code_bits_eval] at h
    all_goals exact h
  simp only [preparedExecWord64,preparedTypedPublicGas,preparedGasWord]
  rw [limb 0 (by decide),limb 1 (by decide),limb 2 (by decide),limb 3 (by decide)]

end NearCompression
