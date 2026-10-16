import NearCompression.PackedComputedOpening

/-! Packing with fallible PCS authentication. The PCS failure event is measured
on the same joint experiment; no independence of failure and packing is assumed.
The source, row point and vector precede packing coordinates. Opening strategies
may depend on those coordinates and on all subsequent challenge data. -/
namespace NearCompression
open Lean.Grind ArenaCore.Security
variable {K : Type} [Field K]

/-- An accepted scalar opening inconsistent with the computed source tensor. -/
def packedComputedPCSFailure {R : Type} (rows pack width group : Nat)
    (table : Nat → Nat → K) (rowPoint : Nat → K)
    (accepts : List K → R → K → Prop) (point : List K) (randomness : R) : Prop :=
  ∃ value, accepts point randomness value ∧ value ≠
    genericMonomialTensor (rows+pack)
      (packedComputedCoefficients rows pack width group table)
      (packedOpeningPoint rows rowPoint point)

/-- Deterministic event decomposition, valid even for adaptively chosen opening
proofs and correlated failure events. It assumes no exact PCS contract. -/
theorem packed_computed_accept_decomposition {R : Type} (rows pack width group : Nat)
    (table : Nat → Nat → K) (rowPoint sent : Nat → K)
    (accepts : List K → R → K → Prop) (point : List K) (randomness : R)
    (accepted : ∃ value, accepts point randomness value ∧ packedGridEval pack sent point=value) :
    packedGridEval pack sent point=
      packedGridEval pack (packedSourceClaims rows pack width group table rowPoint) point ∨
    packedComputedPCSFailure rows pack width group table rowPoint accepts point randomness := by
  classical
  obtain ⟨value,haccept,hsent⟩ := accepted
  by_cases same : value=genericMonomialTensor (rows+pack)
      (packedComputedCoefficients rows pack width group table)
      (packedOpeningPoint rows rowPoint point)
  · left
    rw [packed_computed_tensor,packed_opening_point_identity] at same
    exact hsent.trans same
  · exact Or.inr ⟨value,haccept,same⟩

private theorem count_union {A : Type} (sample : List A) (p q : A → Prop) :
    count sample (fun a => p a ∨ q a)≤count sample p+count sample q := by
  classical
  induction sample with
  | nil => simp [count]
  | cons a rest ih =>
    simp only [count,List.countP_cons] at ih ⊢
    by_cases hp : p a <;> by_cases hq : q a <;> simp_all <;> omega

private theorem count_rectangle {A B : Type} (xs : List A) (ys : List B) (p : A → Prop) :
    count (xs.flatMap (fun x => ys.map (fun y => (x,y)))) (fun pair => p pair.1)=
      count xs p*ys.length := by
  classical
  induction xs with
  | nil => simp [count]
  | cons x xs ih =>
    simp only [List.flatMap_cons,count,List.countP_append,List.countP_map,Function.comp_def] at ih ⊢
    rw [ih]
    by_cases h : p x <;> simp [h,Nat.add_mul,Nat.add_comm]

/-- Uniform packing coordinates followed by a fixed-size subsequent challenge
space. Counted PCS failures are added once, without conditioning them on a good
packing event. The theorem supplies composition, not a bound on PCS failure. -/
theorem packed_computed_opening_failure_budget {R : Type}
    (rows packPred width group lane : Nat) (table : Nat → Nat → K)
    (rowPoint sent : Nat → K) (accepts : List K → R → K → Prop)
    (valid : lane<2^(packPred+1))
    (wrong : sent lane ≠ packedSourceClaims rows (packPred+1) width group table rowPoint lane)
    (sample : List K) (distinct : sample.Nodup) (randomness : List R) :
    let experiment := (packedGrid sample (packPred+1)).flatMap
      (fun point => randomness.map (fun r => (point,r)))
    count experiment (fun pair => ∃ value, accepts pair.1 pair.2 value ∧
      packedGridEval (packPred+1) sent pair.1=value) ≤
      ((packPred+1)*sample.length^packPred)*randomness.length+
      count experiment (fun pair => packedComputedPCSFailure rows (packPred+1)
        width group table rowPoint accepts pair.1 pair.2) := by
  dsimp only
  let collision := fun point => packedGridEval (packPred+1) sent point=
    packedGridEval (packPred+1)
      (packedSourceClaims rows (packPred+1) width group table rowPoint) point
  have packing := packed_claim_grid_bad_count packPred lane sent
    (packedSourceClaims rows (packPred+1) width group table rowPoint) valid wrong sample distinct
  have subset := count_mono
    ((packedGrid sample (packPred+1)).flatMap (fun point => randomness.map (fun r => (point,r))))
    (fun pair h => packed_computed_accept_decomposition rows (packPred+1) width group
      table rowPoint sent accepts pair.1 pair.2 h)
  have union := count_union
    ((packedGrid sample (packPred+1)).flatMap (fun point => randomness.map (fun r => (point,r))))
    (fun pair => collision pair.1)
    (fun pair => packedComputedPCSFailure rows (packPred+1) width group table rowPoint accepts pair.1 pair.2)
  rw [count_rectangle] at union
  exact Nat.le_trans subset (Nat.le_trans union
    (Nat.add_le_add_right (Nat.mul_le_mul_right randomness.length packing) _))

end NearCompression
