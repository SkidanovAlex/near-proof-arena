import NearCompression.CanonicalPolynomial
import NearCompression.InterleavedResidual
import NearCompression.AffineFoldReconstruction
import NearCompression.FiniteRSUniqueDecoding

/-! One actual weighted fold reduction. Nonlinear concentration is an explicit
hypothesis with adaptive scalar candidates and a formal polynomial identity
conclusion. This module does NOT prove that hypothesis or hash/FS security. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def weightedFoldResidualPolynomial (w0 w1 E O : K) : Poly K :=
  Poly.mk [w0*E,w0*(O-E)+(w1-w0)*E,(w1-w0)*(O-E)]

theorem weighted_fold_residual_polynomial_eval (w0 w1 E O r : K) :
    (weightedFoldResidualPolynomial w0 w1 E O).eval r=affineWeightedResidual w0 w1 E O r := by
  rw [affine_weighted_residual_quadratic]
  simp only [weightedFoldResidualPolynomial,Poly.eval,Poly.evalL]
  grind

noncomputable def weightedFoldSuccess (reps : List K) (weight : K → Nat)
    (source : K → K) (D threshold : Nat) (weights : List K)
    (w0 w1 : K) (sent : Poly K) (r : K) : Prop :=
  ∃ candidate : Poly K,candidate.DegLt D ∧
    threshold≤consistencyMass reps (fun x => weight x+weight (-x))
      (fun x => arbitraryRSPairFold source r x=candidate.eval (x*x)) ∧
    ((1-r)*w0+r*w1)*scalarRSResidual weights candidate=sent.eval r

/-- Exact missing nonlinear extraction contract for this fixed prechallenge
state. The scalar candidate may depend on r; the extracted pair does not.
The formal identity is stronger than agreement at two selected challenges. -/
noncomputable def WeightedFoldExtraction (reps sample : List K) (weight : K → Nat)
    (source : K → K) (D threshold error : Nat) (weights : List K)
    (w0 w1 : K) (sent : Poly K) : Prop :=
  error<count sample (weightedFoldSuccess reps weight source D threshold weights w0 w1 sent) →
  ∃ even odd : Poly K,even.DegLt D ∧ odd.DegLt D ∧
    threshold≤consistencyMass reps (fun x => weight x+weight (-x))
      (fun x => rsPairDecode x (source x,source (-x))=(even.eval (x*x),odd.eval (x*x))) ∧
    (sent-weightedFoldResidualPolynomial w0 w1
      (scalarRSResidual weights even) (scalarRSResidual weights odd)).IsZero

/-- Extraction supplies the SAME weighted threshold for a concrete parent
polynomial of degree<2D satisfying the actual parent coefficient residual. -/
theorem weighted_fold_parent_of_extraction (reps sample : List K) (weight : K → Nat)
    (source : K → K) (D threshold error : Nat) (weights : List K)
    (w0 w1 : K) (sent : Poly K) (h2 : (2:K)≠0)
    (nonzero : ∀ x∈reps,x≠0)
    (extract : WeightedFoldExtraction reps sample weight source D threshold error weights w0 w1 sent)
    (many : error<count sample (weightedFoldSuccess reps weight source D threshold weights w0 w1 sent)) :
    ∃ parent : Poly K,parent.DegLt (2*D) ∧
      threshold≤consistencyMass (reps.flatMap (fun x => [x,-x])) weight
        (fun x => source x=parent.eval x) ∧
      scalarRSResidual (rsInterleave (weights.map (fun w => w0*w))
        (weights.map (fun w => w1*w))) parent=sent.eval 0+sent.eval 1 := by
  obtain ⟨even,odd,de,do_,agree,identity⟩ := extract many
  let ce := canonicalPolynomial D even
  let co := canonicalPolynomial D odd
  let parent := Poly.mk (rsInterleave ce.coeffs co.coeffs)
  have ep : ∀ x,(Poly.mk ce.coeffs).eval x=even.eval x := canonical_polynomial_eval D even de
  have op : ∀ x,(Poly.mk co.coeffs).eval x=odd.eval x := canonical_polynomial_eval D odd do_
  have pull := weighted_rs_interleaved_pullback reps weight source ce.coeffs co.coeffs h2 nonzero
  simp only [ep,op] at pull
  refine ⟨parent,?_,Nat.le_trans agree pull,?_⟩
  · exact rs_interleave_degree ce.coeffs co.coeffs D
      (canonical_polynomial_length D even) (canonical_polynomial_length D odd)
  · change scalarRSResidual _ (Poly.mk (rsInterleave ce.coeffs co.coeffs))=_
    rw [scalar_residual_interleaved]
    change w0*scalarRSResidual weights ce+w1*scalarRSResidual weights co=_
    rw [canonical_polynomial_residual D even de,canonical_polynomial_residual D odd do_]
    have values (r : K) : sent.eval r=affineWeightedResidual w0 w1
        (scalarRSResidual weights even) (scalarRSResidual weights odd) r := by
      have eq := Poly.eval_of_isZero identity r
      rw [Poly.eval_sub,weighted_fold_residual_polynomial_eval] at eq
      grind
    rw [values 0,values 1,affine_weighted_residual_endpoints]

/-- Contrapositive one-round soundness skeleton. All actual parent candidate
properties are discharged above; ONLY extraction remains a premise here. -/
theorem weighted_fold_bad_count (reps sample : List K) (weight : K → Nat)
    (source : K → K) (D threshold error : Nat) (weights : List K)
    (w0 w1 : K) (sent : Poly K) (h2 : (2:K)≠0)
    (nonzero : ∀ x∈reps,x≠0)
    (extract : WeightedFoldExtraction reps sample weight source D threshold error weights w0 w1 sent)
    (noParent : ¬∃ parent : Poly K,parent.DegLt (2*D) ∧
      threshold≤consistencyMass (reps.flatMap (fun x => [x,-x])) weight
        (fun x => source x=parent.eval x) ∧
      scalarRSResidual (rsInterleave (weights.map (fun w => w0*w))
        (weights.map (fun w => w1*w))) parent=sent.eval 0+sent.eval 1) :
    count sample (weightedFoldSuccess reps weight source D threshold weights w0 w1 sent)≤error := by
  have cannot : ¬error<count sample
      (weightedFoldSuccess reps weight source D threshold weights w0 w1 sent) := by
    intro many
    exact noParent (weighted_fold_parent_of_extraction reps sample weight source D threshold error
      weights w0 w1 sent h2 nonzero extract many)
  omega

/-- A prover may choose the next oracle AFTER r. Its consistency measure gates
projected weights by the literal fold equality, then tests candidate agreement.
No honest next oracle is assumed. -/
noncomputable def weightedGatedFoldSuccess [DecidableEq K]
    (reps : List K) (weight : K → Nat) (source : K → K)
    (D threshold : Nat) (weights : List K) (w0 w1 : K) (sent : Poly K) (r : K) : Prop :=
  ∃ next : K → K,∃ candidate : Poly K,candidate.DegLt D ∧
    threshold≤consistencyMass reps
      (fun x => if next (x*x)=arbitraryRSPairFold source r x then weight x+weight (-x) else 0)
      (fun x => next (x*x)=candidate.eval (x*x)) ∧
    ((1-r)*w0+r*w1)*scalarRSResidual weights candidate=sent.eval r

theorem weighted_gated_fold_success_transfer [DecidableEq K]
    (reps : List K) (weight : K → Nat) (source : K → K)
    (D threshold : Nat) (weights : List K) (w0 w1 : K) (sent : Poly K) (r : K)
    (accepted : weightedGatedFoldSuccess reps weight source D threshold weights w0 w1 sent r) :
    weightedFoldSuccess reps weight source D threshold weights w0 w1 sent r := by
  obtain ⟨next,candidate,degree,agreement,residual⟩ := accepted
  refine ⟨candidate,degree,?_,residual⟩
  exact Nat.le_trans agreement (consistency_gated_agreement reps
    (fun x => weight x+weight (-x)) (arbitraryRSPairFold source r)
    (fun x => next (x*x)) (fun x => candidate.eval (x*x)))

theorem weighted_gated_fold_bad_count [DecidableEq K]
    (reps sample : List K) (weight : K → Nat) (source : K → K)
    (D threshold error : Nat) (weights : List K) (w0 w1 : K) (sent : Poly K)
    (h2 : (2:K)≠0) (nonzero : ∀ x∈reps,x≠0)
    (extract : WeightedFoldExtraction reps sample weight source D threshold error weights w0 w1 sent)
    (noParent : ¬∃ parent : Poly K,parent.DegLt (2*D) ∧
      threshold≤consistencyMass (reps.flatMap (fun x => [x,-x])) weight
        (fun x => source x=parent.eval x) ∧
      scalarRSResidual (rsInterleave (weights.map (fun w => w0*w))
        (weights.map (fun w => w1*w))) parent=sent.eval 0+sent.eval 1) :
    count sample (weightedGatedFoldSuccess reps weight source D threshold weights w0 w1 sent)≤error := by
  apply Nat.le_trans _ (weighted_fold_bad_count reps sample weight source D threshold error
    weights w0 w1 sent h2 nonzero extract noParent)
  apply count_mono
  intro r accepted
  exact weighted_gated_fold_success_transfer reps weight source D threshold weights w0 w1 sent r accepted

end NearCompression
