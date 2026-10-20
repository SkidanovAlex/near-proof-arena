import NearCompression.RecoveredPrivateSlots
import NearCompression.GKRAllSlotCertificate
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def laneColumnKeys (lane : GKRSourceLane) (col : Nat) : List Nat :=
  if lane.group*2^lane.packingLog+col<lane.width then
    [lane.inputStart+lane.group*2^lane.packingLog+col,
     lane.inputStart+lane.nextOffset+lane.group*2^lane.packingLog+col] else []
def lanePrivateKeys (lane : GKRSourceLane) : List Nat :=
  (List.range (2^lane.packingLog)).flatMap (laneColumnKeys lane)

private theorem key_member (lane : GKRSourceLane) (col slot : Nat) :
    slot∈laneColumnKeys lane col ↔ lane.group*2^lane.packingLog+col<lane.width ∧
      ∃ next : Bool,lane.inputStart+(if next then lane.nextOffset else 0)+lane.group*2^lane.packingLog+col=slot := by
  unfold laneColumnKeys
  split
  · rename_i live
    simp only [live,true_and,List.mem_cons,List.not_mem_nil,or_false]
    constructor
    · intro h
      rcases h with h | h
      · exact ⟨false,by simpa using h.symm⟩
      · exact ⟨true,h.symm⟩
    · rintro ⟨next,h⟩
      cases next
      · left; simpa using h.symm
      · right; exact h.symm
  · rename_i dead
    simp [dead]

/-- Exact key support of the executable live-column enumeration. -/
theorem lane_private_keys_support (lane : GKRSourceLane) (slot : Nat) :
    slot∈lanePrivateKeys lane ↔ lane.LiveSlot false slot ∨ lane.LiveSlot true slot := by
  constructor
  · intro member
    obtain ⟨col,hc,hs⟩ := List.mem_flatMap.mp member
    obtain ⟨live,next,eq⟩ := (key_member lane col slot).mp hs
    have witness : lane.LiveSlot next slot := ⟨col,List.mem_range.mp hc,live,eq⟩
    cases next
    · exact Or.inl witness
    · exact Or.inr witness
  · intro live
    rcases live with ⟨col,hc,hw,he⟩ | ⟨col,hc,hw,he⟩
    · exact List.mem_flatMap.mpr ⟨col,List.mem_range.mpr hc,(key_member lane col slot).mpr ⟨hw,false,he⟩⟩
    · exact List.mem_flatMap.mpr ⟨col,List.mem_range.mpr hc,(key_member lane col slot).mpr ⟨hw,true,he⟩⟩

theorem lane_private_slots_keys (lane : GKRSourceLane) (current next : Nat → K) :
    (lanePrivateSlots lane current next).map Prod.fst=lanePrivateKeys lane := by
  simp only [lanePrivateSlots,lanePrivateKeys,List.map_flatMap]
  congr 1
  funext col
  unfold laneColumnKeys
  split <;> rfl

private theorem flatmap_nodup {A B : Type} (xs : List A) (f : A → List B)
    (inner : ∀ a∈xs,(f a).Nodup)
    (outer : xs.Pairwise (fun a b => ∀ x∈f a,x∉f b)) : (xs.flatMap f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.pairwise_cons] at outer
    rw [List.flatMap_cons,List.nodup_append]
    refine ⟨inner a (by simp),ih (by intro b hb; exact inner b (by simp [hb])) outer.2,?_⟩
    intro x hx y hy eq
    obtain ⟨b,hb,hy⟩ := List.mem_flatMap.mp hy
    subst y
    exact outer.1 b hb x hx hy

theorem lane_private_keys_nodup (lane : GKRSourceLane)
    (separate : ∀ slot,lane.LiveSlot false slot → ¬lane.LiveSlot true slot) :
    (lanePrivateKeys lane).Nodup := by
  apply flatmap_nodup
  · intro col hc
    unfold laneColumnKeys
    split
    · rename_i live
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true,not_false_eq_true]
      intro equal
      apply separate (lane.inputStart+lane.group*2^lane.packingLog+col) ⟨col,List.mem_range.mp hc,live,by simp⟩
      exact ⟨col,List.mem_range.mp hc,live,equal.symm⟩
    · simp
  · apply List.Pairwise.imp_of_mem (R:=fun a b : Nat => a≠b) _ List.nodup_range
    intro a b ha hb different slot sa sb
    obtain ⟨la,na,ea⟩ := (key_member lane a slot).mp sa
    obtain ⟨lb,nb,eb⟩ := (key_member lane b slot).mp sb
    have wa : lane.LiveSlot na slot := ⟨a,List.mem_range.mp ha,la,ea⟩
    have wb : lane.LiveSlot nb slot := ⟨b,List.mem_range.mp hb,lb,eb⟩
    cases na <;> cases nb
    · simp only [Bool.false_eq_true,ite_false] at ea eb; omega
    · exact separate slot wa wb
    · exact separate slot wb wa
    · simp only [ite_true] at ea eb; omega

/-- All-support geometry implies key distinctness for the ENTIRE actual
current/next enumeration, independently of decoded values or rowpoints. -/
theorem recovered_private_keys_nodup (C : Nat) (entries : List (GKRSourceLane × Poly K))
    (disjoint : AllLaneSupportsDisjoint (entries.map Prod.fst))
    (rowpoints : GKRSourceLane → Nat → K) :
    ((recoveredPrivateSlots C entries rowpoints).map Prod.fst).Nodup := by
  have keys : (recoveredPrivateSlots C entries rowpoints).map Prod.fst=
      entries.flatMap (fun entry => lanePrivateKeys entry.1) := by
    rw [recoveredPrivateSlots,List.map_flatMap]
    congr 1
    funext entry
    exact lane_private_slots_keys _ _ _
  rw [keys]
  have apart (i : Nat) (hi : i<entries.length) (j : Nat) (hj : j<entries.length)
      (ni nj : Bool) (different : i≠j ∨ ni≠nj) (slot : Nat)
      (live : entries[i].1.LiveSlot ni slot) : ¬entries[j].1.LiveSlot nj slot := by
    have h := disjoint i (by simpa using hi) j (by simpa using hj) ni nj different slot
    simp only [List.getElem_map] at h
    exact h live
  apply flatmap_nodup
  · intro entry he
    obtain ⟨i,hi,eq⟩ := List.getElem_of_mem he
    subst entry
    apply lane_private_keys_nodup
    intro slot live
    exact apart i hi i hi false true (Or.inr (by decide)) slot live
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj before slot first second
    have a := (lane_private_keys_support entries[i].1 slot).mp first
    have b := (lane_private_keys_support entries[j].1 slot).mp second
    rcases a with a | a <;> rcases b with b | b
    · exact apart i hi j hj false false (Or.inl (by omega)) slot a b
    · exact apart i hi j hj false true (Or.inl (by omega)) slot a b
    · exact apart i hi j hj true false (Or.inl (by omega)) slot a b
    · exact apart i hi j hj true true (Or.inl (by omega)) slot a b

/-- Actual enumeration includes the current/next value for each live column. -/
theorem lane_private_value_covered (lane : GKRSourceLane) (current nextValues : Nat → K)
    (col : Nat) (bound : col<2^lane.packingLog) (live : lane.group*2^lane.packingLog+col<lane.width)
    (next : Bool) :
    (lane.inputStart+(if next then lane.nextOffset else 0)+lane.group*2^lane.packingLog+col,
      if next then nextValues col else current col)∈lanePrivateSlots lane current nextValues := by
  apply List.mem_flatMap.mpr
  refine ⟨col,List.mem_range.mpr bound,?_⟩
  cases next <;> simp [live]

/-- Final slot-read statement: every covered lane contributes exactly its
fixed decoded current/next MLE, with no hidden overlap sum. -/
theorem recovered_private_lane_read (C : Nat) (entries : List (GKRSourceLane × Poly K))
    (disjoint : AllLaneSupportsDisjoint (entries.map Prod.fst))
    (rowpoints : GKRSourceLane → Nat → K) (entry : GKRSourceLane × Poly K) (member : entry∈entries)
    (col : Nat) (bound : col<2^entry.1.packingLog)
    (live : entry.1.group*2^entry.1.packingLog+col<entry.1.width) (next : Bool) :
    let lane := entry.1
    let recovered := recoverProjectedPolynomial (2^(C-(lane.rowLog+lane.packingLog)))
      (2^(lane.rowLog+lane.packingLog)) entry.2
    let table := recoveredGKRTable lane.rowLog lane.packingLog recovered
    gkrScatter (recoveredPrivateSlots C entries rowpoints)
      (lane.inputStart+(if next then lane.nextOffset else 0)+lane.group*2^lane.packingLog+col)=
      if next then genericRowNextMLE lane.rowLog (fun row => table row col) (rowpoints lane)
      else genericRowMLE lane.rowLog (fun row => table row col) (rowpoints lane) := by
  dsimp only
  apply gkr_scatter_owned _ (recovered_private_keys_nodup C entries disjoint rowpoints)
  exact List.mem_flatMap.mpr ⟨entry,member,lane_private_value_covered entry.1 _ _ col bound live next⟩
end NearCompression
