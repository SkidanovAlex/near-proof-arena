import NearCompression.GenericCmpPadding

/-! Exact natural message counts of the resized comparator renderer. Padding
has zero active multiplicity. No equality of field sums/products is used as a
substitute for natural-count traffic. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Complete
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Render

/-- Comparator interactions read current-row fields only. Their messages and
natural multiplicities are identical at every height. -/
theorem generic_cmp_interaction_values (cmps : List (Nat × Nat × Nat)) (logSize bus t r : Nat)
    (pub : List Fp) (i : Interaction) (member : i ∈ Cmp.interactions bus) :
    i.msgVal (genericCmpShrunkTrace cmps logSize) t r pub=i.msgVal (CmpHeight.trace cmps) t r pub ∧
    i.multNat (genericCmpShrunkTrace cmps logSize) t r pub=i.multNat (CmpHeight.trace cmps) t r pub := by
  simp only [Cmp.interactions,List.mem_cons,List.not_mem_nil,or_false] at member
  subst i
  constructor
  · change [genericPaddingRow (genericCmpPrefix cmps) cmps.length genericCmpPad r Cmp.colX,
      genericPaddingRow (genericCmpPrefix cmps) cmps.length genericCmpPad r Cmp.colY,
      genericPaddingRow (genericCmpPrefix cmps) cmps.length genericCmpPad r Cmp.colB]=_
    rw [←generic_cmp_padding_cells cmps t r Cmp.colX,←generic_cmp_padding_cells cmps t r Cmp.colY,
      ←generic_cmp_padding_cells cmps t r Cmp.colB]
    rfl
  · change (if genericPaddingRow (genericCmpPrefix cmps) cmps.length genericCmpPad r Cmp.colAct=1
        then 2^0 else 0)+0=_
    rw [←generic_cmp_padding_cells cmps t r Cmp.colAct]
    rfl

theorem generic_cmp_row_count (cmps : List (Nat × Nat × Nat)) (logSize : Nat) (logBound : logSize≤22)
    (bus t r : Nat) (pub : List Fp) (message : List Fp) (hr : r<2^logSize) (send : Bool) :
    ((Cmp.interactions bus).map fun i =>
      if i.bus=bus ∧ i.send=send ∧ i.msgVal (genericCmpShrunkTrace cmps logSize) t r pub=message
      then i.multNat (genericCmpShrunkTrace cmps logSize) t r pub else 0).sum=
      if send=false ∧ r<cmps.length ∧ cmpMsg (cmps.getD r (0,0,0))=message then 1 else 0 := by
  have rows : r<(CmpHeight.trace cmps).height t := by
    have bound := Nat.pow_le_pow_right (by decide : 0<2) logBound
    change r<2^22
    omega
  calc
    _ = ((Cmp.interactions bus).map fun i =>
        if i.bus=bus ∧ i.send=send ∧ i.msgVal (CmpHeight.trace cmps) t r pub=message
        then i.multNat (CmpHeight.trace cmps) t r pub else 0).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro i hi
      have values := generic_cmp_interaction_values cmps logSize bus t r pub i hi
      rw [values.1,values.2]
    _ = _ := CmpHeight.cmp_row_count cmps bus t r pub message rows send

/-- The resized comparator receives exactly the original generated comparison
messages, counted as naturals, and sends no messages. -/
theorem generic_cmp_count (cmps : List (Nat × Nat × Nat)) (logSize : Nat) (logBound : logSize≤22)
    (fits : cmps.length≤2^logSize) (bus t : Nat) (pub : List Fp) (message : List Fp) (send : Bool) :
    tableBusCount (Cmp.interactions bus) (genericCmpShrunkTrace cmps logSize) t pub bus send message=
      if send=false then (fmsgs (Gen.Cmp.expected cmps)).count message else 0 := by
  rw [busCount_sum]
  have height : (genericCmpShrunkTrace cmps logSize).height t=2^logSize := rfl
  rw [height]
  rw [List.map_congr_left (fun r hr => generic_cmp_row_count cmps logSize logBound bus t r pub message
    (List.mem_range.mp hr) send)]
  by_cases direction : send=false
  · subst send
    rw [if_pos rfl,sum_range_trunc (fun r => if false=false ∧ r<cmps.length ∧
      cmpMsg (cmps.getD r (0,0,0))=message then 1 else 0) (len := cmps.length)
      (fun r hr => if_neg (fun h => absurd h.2.1 (by omega))) _ fits]
    rw [fmsgs_expected,count_map_eq_sum,←range_map_getD cmps (0,0,0)]
    apply congrArg
    apply List.map_congr_left
    intro r hr
    have bound := List.mem_range.mp hr
    by_cases eq : cmpMsg (cmps.getD r (0,0,0))=message
    · simp only [eq,bound,true_and,and_self,ite_true]
    · simp only [eq,bound,true_and,and_false,ite_false]
  · rw [if_neg direction]
    rw [List.map_congr_left (g := fun _ => 0) (fun r _ => by rw [if_neg (fun h => direction h.1)])]
    exact sum_map_zero _

/-- Exact traffic contract used by the actual aligned comparator renderer. -/
theorem generic_cmp_padding_traffic (cmps : List (Nat × Nat × Nat)) (logSize : Nat)
    (logBound : logSize≤22) (fits : cmps.length≤2^logSize) (t : Nat) (pub : List Fp) :
    TableTraffic (Cmp.table B_SCMP).interactions (genericCmpShrunkTrace cmps logSize) t pub (cmpTraffic cmps) := by
  intro bus message
  change tableBusCount (Cmp.interactions B_SCMP) _ t pub bus true message=_ ∧
    tableBusCount (Cmp.interactions B_SCMP) _ t pub bus false message=_
  by_cases same : bus=B_SCMP
  · subst bus
    rw [generic_cmp_count cmps logSize logBound fits B_SCMP t pub message true,
      generic_cmp_count cmps logSize logBound fits B_SCMP t pub message false]
    simp [cmpTraffic,fmsgs] <;> rfl
  · have off : ∀ i ∈ Cmp.interactions B_SCMP,i.bus≠bus := by
      intro i hi
      simp only [Cmp.interactions,List.mem_cons,List.not_mem_nil,or_false] at hi
      subst i
      exact fun h => same h.symm
    rw [tableBusCount_off_bus _ _ _ _ _ _ _ off,tableBusCount_off_bus _ _ _ _ _ _ _ off]
    simp [cmpTraffic,same]

end NearCompression
