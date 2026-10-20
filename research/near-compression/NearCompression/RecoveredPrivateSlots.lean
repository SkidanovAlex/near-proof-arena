import NearCompression.GKRPrivateVectorGlue
import NearCompression.RecoveredHeterogeneousClaim
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def lanePrivateSlots (lane : GKRSourceLane) (current next : Nat → K) : List (Nat × K) :=
  (List.range (2^lane.packingLog)).flatMap (fun col =>
    if lane.group*2^lane.packingLog+col<lane.width then
      [(lane.inputStart+lane.group*2^lane.packingLog+col,current col),
       (lane.inputStart+lane.nextOffset+lane.group*2^lane.packingLog+col,next col)] else [])

private theorem slots_sum_append (a b : List K) : (a++b).sum=a.sum+b.sum := by
  induction a with
  | nil => simp; grind
  | cons x xs ih => simp only [List.cons_append,List.sum_cons,ih]; grind

private theorem flatmap_sum {A B : Type} (xs : List A) (f : A → List B) (g : B → K) :
    ((xs.flatMap f).map g).sum=(xs.map (fun a => ((f a).map g).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,List.map_append,slots_sum_append,ih,List.map_cons,List.sum_cons]

theorem lane_private_slots_bounds (layout : GKRJointLayout) (lane : GKRSourceLane)
    (valid : lane.WellFormed layout) (current next : Nat → K) :
    ∀ entry∈lanePrivateSlots lane current next,entry.1<2^layout.inputLog := by
  intro entry member
  obtain ⟨col,hc,member⟩ := List.mem_flatMap.mp member
  split at member
  · rename_i live
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    obtain ⟨_,_,a,b,c⟩ := valid
    rcases member with rfl | rfl <;> simp only <;> omega
  · simp at member

/-- Exact lane sum in compiler slot order, including the partial-lane mask. -/
theorem lane_private_slots_weighted_sum (m : Nat) (lane : GKRSourceLane)
    (current next left right : Nat → K) (gamma : K) :
    ((lanePrivateSlots lane current next).map (fun entry =>
      (rowEqualityWeight m left entry.1+gamma*rowEqualityWeight m right entry.1)*entry.2)).sum=
      cubeSum lane.packingLog (fun col =>
        heterogeneousColumnWeight m lane false left right gamma col*current col+
        heterogeneousColumnWeight m lane true left right gamma col*next col) := by
  rw [lanePrivateSlots,flatmap_sum]
  unfold cubeSum
  congr 1
  apply List.map_congr_left
  intro col hc
  unfold heterogeneousColumnWeight
  by_cases live : lane.group*2^lane.packingLog+col<lane.width
  · simp only [live,ite_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      Bool.false_eq_true,ite_false,Nat.add_zero,Nat.add_assoc]
    grind
  · simp only [live,ite_false,List.map_nil,List.sum_nil]
    grind

def recoveredPrivateSlots (C : Nat) (entries : List (GKRSourceLane × Poly K))
    (rowpoints : GKRSourceLane → Nat → K) : List (Nat × K) :=
  entries.flatMap (fun entry =>
    let lane := entry.1
    let recovered := recoverProjectedPolynomial (2^(C-(lane.rowLog+lane.packingLog)))
      (2^(lane.rowLog+lane.packingLog)) entry.2
    let table := recoveredGKRTable lane.rowLog lane.packingLog recovered
    lanePrivateSlots lane
      (fun col => genericRowMLE lane.rowLog (fun row => table row col) (rowpoints lane))
      (fun col => genericRowNextMLE lane.rowLog (fun row => table row col) (rowpoints lane)))

/-- Whole compiler-indexed input vector built by scattering the SAME decoded
lane tables. Known constants are outside this private-vector statement. -/
theorem recovered_private_vector_functional (layout : GKRJointLayout)
    (entries : List (GKRSourceLane × Poly K))
    (valid : ∀ lane∈entries.map Prod.fst,lane.WellFormed layout)
    (rowpoints : GKRSourceLane → Nat → K) (left right : Nat → K) (gamma : K) :
    gkrInputFunctional layout.inputLog left right gamma
      (gkrScatter (recoveredPrivateSlots layout.commonLog entries rowpoints))=
      recoveredHeterogeneousClaim layout.commonLog layout.inputLog entries rowpoints left right gamma := by
  have bounds : ∀ entry∈recoveredPrivateSlots layout.commonLog entries rowpoints,entry.1<2^layout.inputLog := by
    intro entry member
    obtain ⟨pair,hp,he⟩ := List.mem_flatMap.mp member
    exact lane_private_slots_bounds layout pair.1
      (valid pair.1 (List.mem_map.mpr ⟨pair,hp,rfl⟩)) _ _ entry he
  rw [gkr_scatter_functional _ _ bounds,recoveredPrivateSlots,flatmap_sum]
  unfold recoveredHeterogeneousClaim
  congr 1
  apply List.map_congr_left
  intro entry he
  exact lane_private_slots_weighted_sum layout.inputLog entry.1 _ _ left right gamma

/-- Joins the actual lifted PCS coefficient functional to GKR's full
compiler-indexed private-vector functional. Distinct slot ownership is a
separate geometry property, not silently assumed by this equality. -/
theorem recovered_private_vector_pcs (layout : GKRJointLayout)
    (entries : List (GKRSourceLane × Poly K))
    (valid : ∀ lane∈entries.map Prod.fst,lane.WellFormed layout)
    (degrees : ∀ entry∈entries,entry.2.DegLt (2^layout.commonLog))
    (sparse : ∀ entry∈entries,∀ i,¬2^(layout.commonLog-(entry.1.rowLog+entry.1.packingLog))∣i → entry.2.coeff i=0)
    (rowpoints : GKRSourceLane → Nat → K) (left right : Nat → K) (gamma : K) :
    coefficientTableFunctional layout.commonLog
      (liftedHeterogeneousWeights layout.commonLog layout.inputLog (entries.map Prod.fst) rowpoints left right gamma)
      (entries.map Prod.snd)=
      gkrInputFunctional layout.inputLog left right gamma
        (gkrScatter (recoveredPrivateSlots layout.commonLog entries rowpoints)) := by
  rw [recovered_private_vector_functional layout entries valid,
    recovered_heterogeneous_functional layout.commonLog layout.inputLog entries
      (by intro e he; exact (valid e.1 (List.mem_map.mpr ⟨e,he,rfl⟩)).2.1) degrees sparse]
end NearCompression
