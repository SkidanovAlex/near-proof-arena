import NearCompression.RecoveredPrivateSlots
import NearCompression.GKRCircuitPath
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Same sequential subtraction as the executable obligation builder, in
constant-entry order. Padding is represented by absent (zero) slots. -/
def gkrRemoveConstants (m : Nat) (left right : Nat → K) (gamma : K)
    (constants : List (Nat × K)) (claim : K) : K :=
  constants.foldl (fun acc entry => acc-
    (rowEqualityWeight m left entry.1+gamma*rowEqualityWeight m right entry.1)*entry.2) claim

theorem gkr_remove_constants_exact (m : Nat) (left right : Nat → K) (gamma claim : K)
    (constants : List (Nat × K)) (bounds : ∀ entry∈constants,entry.1<2^m) :
    gkrRemoveConstants m left right gamma constants claim=
      claim-gkrInputFunctional m left right gamma (gkrScatter constants) := by
  rw [gkr_scatter_functional m constants bounds]
  induction constants generalizing claim with
  | nil => simp [gkrRemoveConstants];grind
  | cons entry rest ih =>
    change gkrRemoveConstants m left right gamma rest
      (claim-(rowEqualityWeight m left entry.1+gamma*rowEqualityWeight m right entry.1)*entry.2)=_
    rw [ih _ (by intro e he;exact bounds e (by simp [he]))]
    simp only [List.map_cons,List.sum_cons]
    grind

/-- The actual constant-subtracted opening equals the recovered PCS
functional exactly when the combined full-input obligation is correct.
Polynomial ownership, degree and sparse-image assumptions remain explicit;
this algebraic equivalence does not authenticate a commitment. -/
theorem gkr_recovered_terminal_iff (layout : GKRJointLayout)
    (entries : List (GKRSourceLane × Poly K))
    (valid : ∀ lane∈entries.map Prod.fst,lane.WellFormed layout)
    (degrees : ∀ entry∈entries,entry.2.DegLt (2^layout.commonLog))
    (sparse : ∀ entry∈entries,∀ i,¬2^(layout.commonLog-(entry.1.rowLog+entry.1.packingLog))∣i → entry.2.coeff i=0)
    (rowpoints : GKRSourceLane → Nat → K) (left right : Nat → K) (gamma claim : K)
    (constants : List (Nat × K)) (bounds : ∀ entry∈constants,entry.1<2^layout.inputLog) :
    (gkrRemoveConstants layout.inputLog left right gamma constants claim=
      coefficientTableFunctional layout.commonLog
        (liftedHeterogeneousWeights layout.commonLog layout.inputLog (entries.map Prod.fst) rowpoints left right gamma)
        (entries.map Prod.snd)) ↔
    claim=gkrInputFunctional layout.inputLog left right gamma
      (fun i => gkrScatter (recoveredPrivateSlots layout.commonLog entries rowpoints) i+gkrScatter constants i) := by
  rw [gkr_remove_constants_exact _ _ _ _ _ _ bounds,
    recovered_private_vector_pcs layout entries valid degrees sparse]
  unfold gkrInputFunctional
  rw [generic_row_mle_add,generic_row_mle_add]
  constructor <;> intro h <;> grind
end NearCompression
