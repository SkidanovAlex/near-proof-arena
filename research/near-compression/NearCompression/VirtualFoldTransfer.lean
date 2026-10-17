import NearCompression.GeneralIndexedExtraction
import NearCompression.GeneralInteractiveFold
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- No intermediate commitment: every oracle is the exact fold of its parent. -/
def virtualFoldOracles (sizes : Nat→Nat) (roots challenges : Nat→K) (source : Nat→K) : Nat→Nat→K
  | 0=>source
  | i+1=>indexedPairFold (sizes (i+1)) (virtualFoldOracles sizes roots challenges source i) (roots i) (challenges i)

theorem virtual_fold_consistency (sizes : Nat→Nat) (roots challenges : Nat→K) (source : Nat→K)
    (i y : Nat) : globalRSChainCheck sizes roots challenges (virtualFoldOracles sizes roots challenges source) i y := by
  rfl

theorem general_chain_no_candidate_outside_bad
    (N0 : Nat) (sizes degrees : Nat → Nat) (roots challenges : Nat → K)
    (oracles : Nat → Nat → K) (allWeights : Nat → List K) (claims : Nat → K)
    (evenWeights oddWeights : Nat → List K) (sent : Nat → Poly K)
    (T rounds : Nat)
    (sizeSteps : ∀ i<rounds,sizes i=2*sizes (i+1))
    (degreeSteps : ∀ i<rounds,degrees i=2*degrees (i+1))
    (weightShapes : ∀ i<rounds,(evenWeights i).length=(oddWeights i).length)
    (parentWeights : ∀ i<rounds,allWeights i=rsInterleave (evenWeights i) (oddWeights i))
    (nextWeights : ∀ i<rounds,allWeights (i+1)=generalFoldWeights (evenWeights i) (oddWeights i) (challenges i))
    (parentClaims : ∀ i<rounds,claims i=(sent i).eval 0+(sent i).eval 1)
    (nextClaims : ∀ i<rounds,claims (i+1)=(sent i).eval (challenges i))
    (h2 : (2:K)≠0)
    (nonzero : ∀ i<rounds,∀ y<sizes (i+1),roots i^y≠0)
    (squared : ∀ i<rounds,∀ y<sizes (i+1),roots (i+1)^y=roots i^y*roots i^y)
    (negative : ∀ i<rounds,∀ y<sizes (i+1),roots i^(y+sizes (i+1))= -(roots i^y))
    (initial : ¬indexedChainCandidate N0 sizes degrees roots challenges oracles allWeights claims T 0)
    (noBad : ∀ i<rounds,¬generalIndexedFoldBad (sizes (i+1)) (degrees (i+1)) T
      (globalChainWeight (List.range N0) sizes (globalRSChainCheck sizes roots challenges oracles) i)
      (oracles i) (roots i) (roots (i+1)) (evenWeights i) (oddWeights i) (sent i) (challenges i)) :
    ¬indexedChainCandidate N0 sizes degrees roots challenges oracles allWeights claims T rounds := by
  have absent : ∀ i,i≤rounds→¬indexedChainCandidate N0 sizes degrees roots challenges oracles allWeights claims T i := by
    intro i hi
    induction i with
    | zero => exact initial
    | succ i ih =>
      intro child
      have noParent:=ih (by omega)
      have success:=general_indexed_child_implies_success N0 sizes degrees roots challenges oracles
        allWeights claims T i (evenWeights i) (oddWeights i) (weightShapes i (by omega)) (sent i)
        (nextWeights i (by omega)) (nextClaims i (by omega)) child
      have noOutcome : ¬generalIndexedFoldOutcome (sizes (i+1)) (degrees (i+1)) T
          (globalChainWeight (List.range N0) sizes (globalRSChainCheck sizes roots challenges oracles) i)
          (oracles i) (roots i) (roots (i+1)) (evenWeights i) (oddWeights i) (sent i) := by
        intro outcome
        exact noParent (general_indexed_outcome_implies_parent N0 sizes degrees roots challenges oracles
          allWeights claims T i (evenWeights i) (oddWeights i) (weightShapes i (by omega)) (sent i)
          (sizeSteps i (by omega)) (degreeSteps i (by omega)) (parentWeights i (by omega))
          (parentClaims i (by omega)) h2 (nonzero i (by omega)) (squared i (by omega))
          (negative i (by omega)) outcome)
      exact noBad i (by omega) ⟨success,noOutcome⟩
  exact absent rounds (Nat.le_refl _)

private theorem initial_residue_weight_one (N y : Nat) (hy : y<N) :
    count (List.range N) (fun s => s%N=y)=1 := by
  classical
  have equal : count (List.range N) (fun s => s%N=y)=List.count y (List.range N) := by
    rw [List.count_eq_countP]
    unfold count
    apply List.countP_congr
    intro s hs
    have mod := Nat.mod_eq_of_lt (List.mem_range.mp hs)
    constructor
    · intro h
      have eq : s%N=y := @_root_.of_decide_eq_true _ (Classical.propDecidable _) h
      rw [mod] at eq
      exact beq_iff_eq.mpr eq
    · intro h
      have eq : s%N=y := by rw [mod]; exact beq_iff_eq.mp h
      exact @_root_.decide_eq_true _ (Classical.propDecidable _) eq
  rw [equal,List.Nodup.count List.nodup_range]
  simp [List.mem_range.mpr hy]


theorem virtual_fold_weight_exact (N : Nat) (sizes : Nat→Nat) (roots challenges : Nat→K)
    (source : Nat→K) (stage : Nat) (initial : sizes 0=N)
    (halves : ∀ i<stage,sizes i=2*sizes (i+1)) (y : Nat) (hy : y<sizes stage) :
    globalChainWeight (List.range N) sizes
      (globalRSChainCheck sizes roots challenges (virtualFoldOracles sizes roots challenges source)) stage y=2^stage := by
  induction stage generalizing y with
  | zero =>
    simp only [globalChainWeight,initial,Nat.pow_zero]
    exact initial_residue_weight_one N y (by rw [initial] at hy;exact hy)
  | succ i ih =>
    have step:=halves i (by omega)
    have left:=ih (fun j hj=>halves j (by omega)) y (by omega)
    have right:=ih (fun j hj=>halves j (by omega)) (y+sizes (i+1)) (by omega)
    simp only [globalChainWeight,if_pos (virtual_fold_consistency sizes roots challenges source i y),
      left,right,Nat.pow_succ]
    omega

private theorem constant_mass {A : Type} (domain : List A) (weight : A→Nat) (event : A→Prop)
    (k : Nat) (same : ∀ x∈domain,weight x=k) :
    consistencyMass domain weight event=k*count domain event := by
  classical
  induction domain with
  | nil => simp [consistencyMass,count]
  | cons x xs ih =>
    have head:=same x (by simp)
    have tail:=ih (fun y hy=>same y (by simp [hy]))
    simp only [consistencyMass,count,List.map_cons,List.sum_cons,List.countP_cons] at tail ⊢
    by_cases h : event x <;> simp_all <;> grind

/-- Candidate absence at the virtually folded stage implies the exact
unweighted agreement bound required by source-query transfer. -/
theorem virtual_fold_insufficient_agreement (N T stage minimum : Nat) (sizes degrees : Nat→Nat)
    (roots challenges : Nat→K) (source : Nat→K) (weights : Nat→List K) (claims : Nat→K)
    (initial : sizes 0=N) (halves : ∀ i<stage,sizes i=2*sizes (i+1))
    (threshold : T≤2^stage*minimum)
    (absent : ¬indexedChainCandidate N sizes degrees roots challenges
      (virtualFoldOracles sizes roots challenges source) weights claims T stage)
    (candidate : Poly K) (degree : candidate.DegLt (degrees stage))
    (functional : scalarRSResidual (weights stage) candidate=claims stage) :
    count (List.range (sizes stage)) (fun y=>candidate.eval (roots stage^y)=
      virtualFoldOracles sizes roots challenges source stage y)<minimum := by
  classical
  apply Nat.lt_of_not_ge
  intro many
  apply absent
  refine ⟨candidate,degree,functional,?_⟩
  rw [constant_mass _ _ _ (2^stage) (fun y hy=>virtual_fold_weight_exact N sizes roots challenges
    source stage initial halves y (List.mem_range.mp hy))]
  have same : count (List.range (sizes stage)) (fun y=>candidate.eval (roots stage^y)=
      virtualFoldOracles sizes roots challenges source stage y)=
      count (List.range (sizes stage)) (fun y=>virtualFoldOracles sizes roots challenges source stage y=
      candidate.eval (roots stage^y)) := by
    unfold count
    apply List.countP_congr
    intro y hy
    simp only [decide_eq_true_eq,eq_comm]
  rw [same] at many
  exact Nat.le_trans threshold (Nat.mul_le_mul_left (2^stage) many)

end NearCompression
