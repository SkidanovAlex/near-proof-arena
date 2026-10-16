import NearCompression.GKRSlotCertificate
namespace NearCompression

def AllLaneSupportsDisjoint (lanes : List GKRSourceLane) : Prop :=
  ∀ i,∀ hi : i<lanes.length,∀ j,∀ hj : j<lanes.length,∀ ni nj : Bool,
    (i≠j ∨ ni≠nj) → ∀ slot,lanes[i].LiveSlot ni slot → ¬lanes[j].LiveSlot nj slot

/-- All current/next intervals, not just one distinguishing slot per lane. -/
def gkrAllSlotsDisjointCheck (lanes : List GKRSourceLane) : Bool :=
  (List.range lanes.length).all (fun i => (List.range lanes.length).all (fun j =>
    [false,true].all (fun ni => [false,true].all (fun nj =>
      if i=j ∧ ni=nj then true else decide
        ((gkrLaneAt lanes i).slotEnd ni≤(gkrLaneAt lanes j).slotStart nj ∨
          (gkrLaneAt lanes j).slotEnd nj≤(gkrLaneAt lanes i).slotStart ni)))))

theorem checked_all_lane_supports (lanes : List GKRSourceLane)
    (checked : gkrAllSlotsDisjointCheck lanes=true) : AllLaneSupportsDisjoint lanes := by
  intro i hi j hj ni nj different slot live
  have first := List.all_eq_true.mp checked i (List.mem_range.mpr hi)
  have second := List.all_eq_true.mp first j (List.mem_range.mpr hj)
  have third := List.all_eq_true.mp second ni (by cases ni <;> simp)
  have fourth := List.all_eq_true.mp third nj (by cases nj <;> simp)
  have notSame : ¬(i=j ∧ ni=nj) := by
    intro both
    rcases different with h | h
    · exact h both.1
    · exact h both.2
  simp only [notSame,ite_false,decide_eq_true_eq] at fourth
  have lookup (k : Nat) (hk : k<lanes.length) : gkrLaneAt lanes k=lanes[k] := by
    simp [gkrLaneAt,List.getD,hk]
  rw [lookup i hi,lookup j hj] at fourth
  exact live_slot_disjoint lanes[i] lanes[j] ni nj fourth slot live
end NearCompression
