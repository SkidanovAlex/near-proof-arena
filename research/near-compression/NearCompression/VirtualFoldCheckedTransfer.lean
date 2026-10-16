import NearCompression.VirtualFoldPrefix
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

private theorem split_exact (weights : List K) (n : Nat) (shape : weights.length=2*n) :
    (monomialEvenCoefficients weights).length=n ∧ (monomialOddCoefficients weights).length=n := by
  have h:=monomial_split_lengths weights
  omega

private theorem split_rebuild (n : Nat) (weights : List K) (shape : weights.length=2*n) :
    rsInterleave (monomialEvenCoefficients weights) (monomialOddCoefficients weights)=weights := by
  induction n generalizing weights with
  | zero =>
    have empty : weights=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst weights;simp [rsInterleave,monomialEvenCoefficients,monomialOddCoefficients]
  | succ n ih =>
    cases weights with
    | nil => simp at shape
    | cons a rest => cases rest with
      | nil => simp only [List.length_cons,List.length_nil] at shape;omega
      | cons b rest =>
        simp only [monomialEvenCoefficients,monomialOddCoefficients,rsInterleave]
        rw [ih rest (by simp only [List.length_cons] at shape;omega)]

theorem virtual_prefix_weight_length (weights history : List K) (degrees : Nat→Nat) (stage : Nat)
    (shape : weights.length=degrees 0) (halves : ∀ i<stage,degrees i=2*degrees (i+1)) :
    (virtualPrefixWeights weights history stage).length=degrees stage := by
  induction stage with
  | zero => exact shape
  | succ i ih =>
    have previous:=ih (fun j hj=>halves j (by omega))
    have split:=split_exact (virtualPrefixWeights weights history i) (degrees (i+1))
      (previous.trans (halves i (by omega)))
    simp only [virtualPrefixWeights,generalFoldWeights,List.length_zipWith,split.1,split.2,Nat.min_self]

theorem virtual_prefix_weight_layout (weights history : List K) (degrees : Nat→Nat) (i : Nat)
    (shape : weights.length=degrees 0) (halves : ∀ j≤i,degrees j=2*degrees (j+1)) :
    (monomialEvenCoefficients (virtualPrefixWeights weights history i)).length=
      (monomialOddCoefficients (virtualPrefixWeights weights history i)).length ∧
    virtualPrefixWeights weights history i=rsInterleave
      (monomialEvenCoefficients (virtualPrefixWeights weights history i))
      (monomialOddCoefficients (virtualPrefixWeights weights history i)) := by
  have length:=(virtual_prefix_weight_length weights history degrees i shape (fun j hj=>halves j (by omega))).trans (halves i (by omega))
  have split:=split_exact (virtualPrefixWeights weights history i) (degrees (i+1)) length
  exact ⟨split.1.trans split.2.symm,(split_rebuild _ _ length).symm⟩

/-- Literal endpoint equations checked before replacing the running claim. -/
def virtualPrefixEndpointChecks [DecidableEq K] (sizes : Nat→Nat) (roots source : Nat→K)
    (weights : List K) (claim : K) (prover : Nat→List K→WhirQuadratic K) (path : List K) : Bool :=
  (List.range path.length).all (fun i=>decide ((virtualPrefixSent prover path i).eval 0+
    (virtualPrefixSent prover path i).eval 1=(virtualPrefixTranscript sizes roots source weights claim prover path).claims i))

/-- Checked endpoint equations plus derived weight layout and causal bad-event
exclusion preserve absence of a candidate through the actual virtual strategy.
The stage-zero candidate predicate is definitionally independent of future draws. -/
theorem virtual_prefix_checked_absence [DecidableEq K]
    (N T : Nat) (sizes degrees : Nat→Nat) (roots source : Nat→K)
    (weights path : List K) (claim : K) (prover : Nat→List K→WhirQuadratic K)
    (weightShape : weights.length=degrees 0)
    (sizeHalves : ∀ i<path.length,sizes i=2*sizes (i+1))
    (degreeHalves : ∀ i<path.length,degrees i=2*degrees (i+1))
    (h2 : (2:K)≠0) (nonzero : ∀ i<path.length,∀ y<sizes (i+1),roots i^y≠0)
    (squared : ∀ i<path.length,∀ y<sizes (i+1),roots (i+1)^y=roots i^y*roots i^y)
    (negative : ∀ i<path.length,∀ y<sizes (i+1),roots i^(y+sizes (i+1))= -(roots i^y))
    (checked : virtualPrefixEndpointChecks sizes roots source weights claim prover path=true)
    (initial : ¬indexedChainCandidate N sizes degrees roots (fun _=>0) (fun _=>source)
      (fun _=>weights) (fun _=>claim) T 0)
    (good : ¬adaptivePathBad (generalFoldHistoryBad
      (virtualPrefixTranscript sizes roots source weights claim prover) N sizes degrees T) [] path) :
    let tr:=virtualPrefixTranscript sizes roots source weights claim prover path
    ¬indexedChainCandidate N sizes degrees tr.roots tr.challenges tr.oracles tr.weights tr.claims T path.length := by
  let tr:=virtualPrefixTranscript sizes roots source weights claim prover path
  have layout (i : Nat) (hi : i<path.length) := virtual_prefix_weight_layout weights path degrees i weightShape
    (fun j hj=>degreeHalves j (by omega))
  apply general_chain_no_candidate_outside_bad N sizes degrees tr.roots tr.challenges tr.oracles
    tr.weights tr.claims tr.evenWeights tr.oddWeights tr.sent T path.length sizeHalves degreeHalves
  · intro i hi;exact (layout i hi).1
  · intro i hi;exact (layout i hi).2
  · intro i hi;rfl
  · intro i hi
    have check:=List.all_eq_true.mp checked i (List.mem_range.mpr hi)
    exact (_root_.of_decide_eq_true check).symm
  · intro i hi;rfl
  · exact h2
  · exact nonzero
  · exact squared
  · exact negative
  · simpa only [tr,virtualPrefixTranscript,indexedChainCandidate,virtualFoldOracles,
      virtualPrefixWeights,globalChainWeight] using initial
  · exact virtual_prefix_no_bad_transitions sizes degrees roots source weights claim prover path N T good
/-- Direct noClose premise for source-query transfer from checked prior folds. -/
theorem virtual_prefix_checked_no_close [DecidableEq K]
    (N T : Nat) (sizes degrees : Nat→Nat) (roots source : Nat→K)
    (weights path : List K) (claim : K) (prover : Nat→List K→WhirQuadratic K)
    (weightShape : weights.length=degrees 0)
    (sizeHalves : ∀ i<path.length,sizes i=2*sizes (i+1))
    (degreeHalves : ∀ i<path.length,degrees i=2*degrees (i+1))
    (h2 : (2:K)≠0) (nonzero : ∀ i<path.length,∀ y<sizes (i+1),roots i^y≠0)
    (squared : ∀ i<path.length,∀ y<sizes (i+1),roots (i+1)^y=roots i^y*roots i^y)
    (negative : ∀ i<path.length,∀ y<sizes (i+1),roots i^(y+sizes (i+1))= -(roots i^y))
    (checked : virtualPrefixEndpointChecks sizes roots source weights claim prover path=true)
    (initial : ¬indexedChainCandidate N sizes degrees roots (fun _=>0) (fun _=>source)
      (fun _=>weights) (fun _=>claim) T 0)
    (good : ¬adaptivePathBad (generalFoldHistoryBad
      (virtualPrefixTranscript sizes roots source weights claim prover) N sizes degrees T) [] path)
    (sizeInitial : sizes 0=N) (minimum : Nat) (threshold : T≤2^path.length*minimum)
    (candidate : Poly K) (degree : candidate.DegLt (degrees path.length))
    (functional : scalarRSResidual (virtualPrefixWeights weights path path.length) candidate=
      (virtualPrefixTranscript sizes roots source weights claim prover path).claims path.length) :
    count (List.range (sizes path.length)) (fun y=>candidate.eval (roots path.length^y)=
      virtualFoldOracles sizes roots (fun i=>path.getD i 0) source path.length y)<minimum := by
  have absent:=virtual_prefix_checked_absence N T sizes degrees roots source weights path claim prover
    weightShape sizeHalves degreeHalves h2 nonzero squared negative checked initial good
  exact virtual_fold_insufficient_agreement N T path.length minimum sizes degrees roots
    (fun i=>path.getD i 0) source (virtualPrefixWeights weights path)
    (virtualPrefixTranscript sizes roots source weights claim prover path).claims sizeInitial sizeHalves
    threshold absent candidate degree functional

end NearCompression
