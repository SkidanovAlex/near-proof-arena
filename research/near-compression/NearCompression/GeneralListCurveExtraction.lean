import NearCompression.GeneralWeightedExtraction
import NearCompression.FiniteBatchCandidates
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

private theorem count_or {A : Type} (sample : List A) (p q : A→Prop) :
    count sample (fun a=>p a ∨ q a)≤count sample p+count sample q := by
  classical
  induction sample with
  | nil=>simp [count]
  | cons a rest ih=>
    simp only [count,List.countP_cons] at ih ⊢
    by_cases hp : p a <;> by_cases hq : q a <;> simp_all <;> omega

/-- A same-support correlated-agreement result supplies the coefficient identity
needed by the constrained bridge whenever the support has at least D points. -/
theorem list_curve_candidate_identity (support : List K) (distinct : support.Nodup)
    (D : Nat) (enough : D≤support.length) (p even odd : Poly K) (r : K)
    (dp : p.DegLt D) (de : even.DegLt D) (do_ : odd.DegLt D)
    (agreement : ∀ x∈support,p.eval x=(1-r)*even.eval x+r*odd.eval x) :
    (p-(Poly.smul (1-r) even+Poly.smul r odd)).IsZero := by
  apply PolyRoots.eqZeroOfRoots_of polyEval polyDeg quotFacts isZeroEval K
    (p-(Poly.smul (1-r) even+Poly.smul r odd)) D support
  · exact Poly.degLt_sub dp (Poly.degLt_add (Poly.degLt_smul _ de) (Poly.degLt_smul _ do_))
  · exact distinct
  · exact enough
  · intro x hx
    simp only [Poly.eval_sub,Poly.eval_add,Poly.eval_smul]
    rw [agreement x hx]
    grind

/-- Conditional reduction from a prechallenge list of jointly agreeing curves
and an exceptional-set transfer to arbitrary-weight constrained extraction.
This proves the constraint penalty (two roots per curve), not the unproved
list-correlated agreement premise or a numerical bound on the complete list. -/
theorem general_list_curve_extraction_bad_count (domain sample : List K)
    (distinct : sample.Nodup) (weight : K→Nat) (D T : Nat)
    (sourceEven sourceOdd : K→K) (ew ow : List K) (sent : Poly K)
    (sentDegree : sent.DegLt 3) (family : List (Poly K×Poly K)) (bad : K→Prop)
    (familyCorrect : ∀ pair∈family,pair.1.DegLt D ∧ pair.2.DegLt D ∧
      T≤consistencyMass domain weight
        (fun x=>sourceEven x=pair.1.eval x ∧ sourceOdd x=pair.2.eval x))
    (transfer : ∀ r,¬bad r→∀ p : Poly K,p.DegLt D→
      T≤consistencyMass domain weight (fun x=>p.eval x=(1-r)*sourceEven x+r*sourceOdd x)→
      ∃ pair∈family,(p-(Poly.smul (1-r) pair.1+Poly.smul r pair.2)).IsZero)
    (noOutcome : ¬∃ even odd : Poly K,even.DegLt D ∧ odd.DegLt D ∧
      T≤consistencyMass domain weight
        (fun x=>sourceEven x=even.eval x ∧ sourceOdd x=odd.eval x) ∧
      (sent-generalFoldResidualPolynomial ew ow even odd).IsZero) :
    count sample (generalWeightedCurveSuccess domain weight sourceEven sourceOdd D T ew ow sent)
      ≤count sample bad+family.length*2 := by
  classical
  let event := fun (pair : Poly K×Poly K) r=>
    (sent-generalFoldResidualPolynomial ew ow pair.1 pair.2).eval r=0
  have each : ∀ pair∈family,count sample (event pair)≤2 := by
    intro pair member
    have facts:=familyCorrect pair member
    have nz : ¬(sent-generalFoldResidualPolynomial ew ow pair.1 pair.2).IsZero := by
      intro zero
      exact noOutcome ⟨pair.1,pair.2,facts.1,facts.2.1,facts.2.2,zero⟩
    have degree : (sent-generalFoldResidualPolynomial ew ow pair.1 pair.2).DegLt 3 :=
      Poly.degLt_sub sentDegree (Poly.degLt_length _)
    have bound:=PolyRoots.cardRootsLe_of polyEval polyDeg quotFacts isZeroEval K
      (sent-generalFoldResidualPolynomial ew ow pair.1 pair.2) 3 sample nz degree distinct
    dsimp only [event]
    omega
  have subset : count sample (generalWeightedCurveSuccess domain weight sourceEven sourceOdd D T ew ow sent)≤
      count sample (fun r=>bad r ∨ ∃ pair∈family,event pair r) := by
    apply count_mono
    intro r success
    by_cases exceptional : bad r
    · exact Or.inl exceptional
    · right
      obtain ⟨p,degree,agreement,residual⟩:=success
      obtain ⟨pair,member,zero⟩:=transfer r exceptional p degree agreement
      have equal (weights : List K) : scalarRSResidual weights p=
          scalarRSResidual weights (Poly.smul (1-r) pair.1+Poly.smul r pair.2) := by
        apply scalar_rs_residual_congr
        intro i
        have h:=zero i
        change (p-(Poly.smul (1-r) pair.1+Poly.smul r pair.2)).coeff i=0 at h
        rw [Poly.coeff_sub] at h
        grind
      refine ⟨pair,member,?_⟩
      dsimp only [event]
      rw [Poly.eval_sub,general_fold_residual_eval]
      rw [equal ew,equal ow] at residual
      grind
  have union:=finite_candidate_union_count sample family event 2 each
  have disjunction:=count_or sample bad (fun r=>∃ pair∈family,event pair r)
  omega
end NearCompression
