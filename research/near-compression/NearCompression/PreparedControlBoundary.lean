import NearCompression.PreparedControlAuthenticated

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

theorem prepared_control_boundary_no_receives (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (last : Bool) (message : List Fp) :
    busCount (preparedControlBusAir ec cc boundary count).toAir tr pub (if last then 1 else 0) false message=0 := by
  cases last <;>
    simp only [busCount,busCount.go,preparedControlBusAir,preparedControlBusExecTable,preparedControlBusDataTable,Nat.add_zero,
      Bool.false_eq_true,ite_false,ite_true] <;>
    rw [ZkFormal.Chacha.tableBusCount_eq,ZkFormal.Chacha.tableBusCount_eq] <;>
    simp only [ZkFormal.Chacha.rowTraffic,List.flatMap_cons,List.flatMap_nil,preparedControlBusFetch,
      preparedControlBusReceive,preparedControlBusPublish,Nat.reduceEqDiff,Bool.true_eq_false,
      and_false,false_and,ite_false,List.nil_append,List.append_nil]
  all_goals
    have empty (rows : List Nat) : rows.flatMap (fun _=>([] : List (List Fp)))=[] := by
      induction rows <;> simp_all
    rw [empty,empty]
    rfl

theorem prepared_control_boundary_public_unique (ec cc boundary : List Expr) (count : Nat)
    (pub : List Fp) (counts : preparedExecBoundaryCountsCheck pub=true)
    (last : Bool) (message : List Fp)
    (positive : pubCount (preparedControlBusAir ec cc boundary count) pub (if last then 1 else 0) false message≠0) :
    message=preparedExecPublicBoundary pub last := by
  have counts:=of_decide_eq_true counts
  unfold pubCount at positive
  obtain ⟨entry,member⟩:=List.exists_mem_of_length_pos (Nat.pos_of_ne_zero positive)
  obtain ⟨member,eq⟩:=List.mem_filter.mp member
  have eq:=of_decide_eq_true eq
  subst entry
  unfold pubMsgs at member
  obtain ⟨seg,segments,messages⟩:=List.mem_flatMap.mp member
  obtain ⟨msg,inSegment,eq⟩:=List.mem_map.mp messages
  simp only [preparedControlBusAir,List.mem_cons,List.not_mem_nil,or_false] at segments
  cases last
  · rcases segments with rfl|rfl|rfl
    · cases eq
      change message∈(preparedExecBoundarySegment false).msgs pub at inSegment
      simp only [PubSeg.msgs,counts.1,List.range_one,List.map_cons,List.map_nil,List.mem_singleton] at inSegment
      exact inSegment.trans (prepared_exec_boundary_record pub false)
    · cases eq
    · cases eq
  · rcases segments with rfl|rfl|rfl
    · cases eq
    · cases eq
      change message∈(preparedExecBoundarySegment true).msgs pub at inSegment
      simp only [PubSeg.msgs,counts.2,List.range_one,List.map_cons,List.map_nil,List.mem_singleton] at inSegment
      exact inSegment.trans (prepared_exec_boundary_record pub true)
    · cases eq

/-- Actual natural bus balance binds the complete27-field entry/exit record;
the CODE receive bus2 and public CODE bus3 cannot discharge boundary traffic. -/
theorem prepared_control_boundary_bound (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (holds : HoldsP (preparedControlBusAir ec cc boundary count) pub tr)
    (counts : preparedExecBoundaryCountsCheck pub=true) (last : Bool) (r : Nat)
    (hr : r<tr.height 0) (endpoint : if last then r+1=tr.height 0 else r=0) :
    (preparedExecBoundaryInteraction boundary last).msgVal tr 0 r pub=preparedExecPublicBoundary pub last := by
  have active : (preparedExecBoundaryInteraction boundary last).multNat tr 0 r pub≠0 := by
    cases last <;> simp only [Bool.false_eq_true,ite_false,ite_true] at endpoint ⊢ <;>
      simp [Interaction.multNat,Interaction.multNat.go,preparedExecBoundaryInteraction,
        Expr.eval,Expr.evalWith,rowEnv,endpoint]
  have member : preparedExecBoundaryInteraction boundary last∈(preparedControlBusExecTable ec boundary).interactions := by
    cases last <;> simp [preparedControlBusExecTable,preparedExecBoundaryInteraction]
  have traffic:=ZkFormal.Chacha.tableBusCount_pos hr member active
  let message:=(preparedExecBoundaryInteraction boundary last).msgVal tr 0 r pub
  have nonzero : busCount (preparedControlBusAir ec cc boundary count).toAir tr pub (if last then 1 else 0) true message≠0 := by
    change tableBusCount (preparedControlBusExecTable ec boundary).interactions tr 0 pub (if last then 1 else 0) true message+
      (tableBusCount (preparedControlBusDataTable cc).interactions tr 1 pub (if last then 1 else 0) true message+0)≠0
    change tableBusCount (preparedControlBusExecTable ec boundary).interactions tr 0 pub (if last then 1 else 0) true message≠0 at traffic
    omega
  have sendZero : pubCount (preparedControlBusAir ec cc boundary count) pub (if last then 1 else 0) true message=0 := by
    apply ZkFormal.Chacha.pubCount_zero
    intro seg member _
    simp only [preparedControlBusAir,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> decide
  have balance:=holds.balance (if last then 1 else 0) message
  rw [sendZero,prepared_control_boundary_no_receives,Nat.add_zero,Nat.zero_add] at balance
  apply prepared_control_boundary_public_unique ec cc boundary count pub counts last message
  rw [←balance]
  exact nonzero

theorem prepared_control_boundary_gas (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr)
    (counts : preparedExecBoundaryCountsCheck pub=true) (last : Bool) (r : Nat)
    (hr : r<tr.height 0) (endpoint : if last then r+1=tr.height 0 else r=0) :
    preparedExecWord64 (tr.cell 0 r) 299=preparedExecPublicGas pub last := by
  have balanced:=holds
  rw [prepared_control_bus_literal_air] at balanced
  have message:=prepared_control_boundary_bound _ _ _ count tr pub balanced counts last r hr endpoint
  have limb (i : Nat) (hi : i<4) :
      preparedCodeLimb (tr.cell 0 r) (299+16*i)=pub.getD ((if last then 39 else 12)+7+i) 0 := by
    have h:=congrArg (fun msg:List Fp=>msg.getD (7+i) 0) message
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3:=by omega
    rcases cases with z|z|z|z <;> subst i
    all_goals cases last
    all_goals change (preparedCodeBits _).eval tr 0 r pub=_ at h
    all_goals rw [prepared_code_bits_eval] at h
    all_goals exact h
  simp only [preparedExecWord64,preparedExecPublicGas,preparedGasWord]
  rw [limb 0 (by decide),limb 1 (by decide),limb 2 (by decide),limb 3 (by decide)]

end NearCompression
