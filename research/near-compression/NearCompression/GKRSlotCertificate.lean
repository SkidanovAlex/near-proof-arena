import NearCompression.GKRJointLaneSeparation
namespace NearCompression

def gkrLaneAt (lanes : List GKRSourceLane) (i : Nat) : GKRSourceLane :=
  lanes.getD i ⟨0,0,0,0,0,0,0⟩

def gkrSlotContains (lane : GKRSourceLane) (next : Bool) (slot : Nat) : Bool :=
  decide (lane.slotStart next≤slot ∧ slot<lane.slotEnd next)

def gkrLaneSelectorCheck (layout : GKRJointLayout) (lanes : List GKRSourceLane) (i : Nat) : Bool :=
  let lane := gkrLaneAt lanes i
  let slot := lane.slotStart false
  decide (slot<2^layout.inputLog) &&
  gkrSlotContains lane false slot && !gkrSlotContains lane true slot &&
  (List.range lanes.length).all (fun j => if i=j then true else
    !gkrSlotContains (gkrLaneAt lanes j) false slot && !gkrSlotContains (gkrLaneAt lanes j) true slot)

def gkrLaneSelectorsCheck (layout : GKRJointLayout) (lanes : List GKRSourceLane) : Bool :=
  (List.range lanes.length).all (gkrLaneSelectorCheck layout lanes)

/-- Executable natural interval checks establish the exact geometry needed
for Boolean separation; duplicate or empty lanes fail this certificate. -/
theorem checked_lane_selectors (layout : GKRJointLayout) (lanes : List GKRSourceLane)
    (checked : gkrLaneSelectorsCheck layout lanes=true) : CanonicalLaneSelectors layout lanes := by
  intro i hi
  have head := List.all_eq_true.mp checked i (List.mem_range.mpr hi)
  simp only [gkrLaneSelectorCheck,Bool.and_eq_true,Bool.not_eq_true,decide_eq_true_eq] at head
  have lookup (j : Nat) (hj : j<lanes.length) : gkrLaneAt lanes j=lanes[j] := by
    simp [gkrLaneAt,List.getD,hj]
  rw [lookup i hi] at head
  obtain ⟨⟨⟨bound,live⟩,noNext⟩,others⟩ := head
  refine ⟨lanes[i].slotStart false,bound,?_,?_,?_⟩
  · exact (live_slot_interval _ _ _).mpr (of_decide_eq_true live)
  · intro next
    have h := (live_slot_interval _ _ _).mp next
    have yes : gkrSlotContains lanes[i] true (lanes[i].slotStart false)=true := by
      simp only [gkrSlotContains,decide_eq_true_eq]
      exact h
    rw [yes] at noNext
    simp at noNext
  · intro j hj different next
    have other := List.all_eq_true.mp others j (List.mem_range.mpr hj)
    simp only [different,ite_false,Bool.and_eq_true,Bool.not_eq_true] at other
    rw [lookup j hj] at other
    intro collision
    have h := (live_slot_interval _ _ _).mp collision
    have yes : gkrSlotContains lanes[j] next (lanes[i].slotStart false)=true := by
      simp only [gkrSlotContains,decide_eq_true_eq]
      exact h
    cases next with
    | false => rw [yes] at other; simp at other
    | true => rw [yes] at other; simp at other
end NearCompression
