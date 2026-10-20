import NearCompression.FiniteBatchCandidates
import NearCompression.FiniteRSUniqueDecoding
import NearCompression.WeightedConsistencyTransfer
import NearCompression.WeightedFoldComposition

/-! A substantive concentration component AFTER a shared affine polynomial
curve is fixed. It neither assumes source words are polynomials nor constructs
that curve from adaptive decoded candidates. Arbitrary natural weights work. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

private theorem affine_pair_coincidence_count (sample : List K) (distinct : sample.Nodup)
    (a b c d : K) (different : ¬(a=c ∧ b=d)) :
    count sample (fun r => (1-r)*a+r*b=(1-r)*c+r*d)≤1 := by
  let p : Poly K := Poly.mk [a,b-a]
  let q : Poly K := Poly.mk [c,d-c]
  have nz : ¬(p-q).IsZero := by
    intro zero
    have h0 := zero 0
    have h1 := zero 1
    change (p-q).coeff 0=0 at h0
    change (p-q).coeff 1=0 at h1
    rw [Poly.coeff_sub] at h0 h1
    simp only [p,q,Poly.coeff,List.getD_cons_zero,
      List.getD_cons_succ] at h0 h1
    apply different
    constructor <;> grind
  have roots := finite_rs_distinct_agreement sample distinct p q 2
    (Poly.degLt_length _) (Poly.degLt_length _) nz
  have subset : count sample (fun r => (1-r)*a+r*b=(1-r)*c+r*d)≤
      count sample (fun r => p.eval r=q.eval r) := by
    apply count_mono
    intro r equal
    simp only [p,q,Poly.eval,Poly.evalL]
    grind
  omega

/-- If joint agreement is below T, every successful scalar challenge must
create an accidental agreement at some nonjoint point. Each such point allows
at most one challenge, so weighted success is supported on at most |domain|
challenges. No division by weights, no positivity or distinct-domain premise. -/
theorem shared_curve_below_threshold_count {A : Type} (domain : List A)
    (weight : A → Nat) (sourceEven sourceOdd candidateEven candidateOdd : A → K)
    (threshold : Nat) (below : consistencyMass domain weight
      (fun x => sourceEven x=candidateEven x ∧ sourceOdd x=candidateOdd x)<threshold)
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun r => threshold≤consistencyMass domain weight
      (fun x => (1-r)*sourceEven x+r*sourceOdd x=
        (1-r)*candidateEven x+r*candidateOdd x))≤domain.length := by
  classical
  let exceptional : A → K → Prop := fun x r =>
    ¬(sourceEven x=candidateEven x ∧ sourceOdd x=candidateOdd x) ∧
      (1-r)*sourceEven x+r*sourceOdd x=(1-r)*candidateEven x+r*candidateOdd x
  have each : ∀ x∈domain,count sample (exceptional x)≤1 := by
    intro x hx
    by_cases joint : sourceEven x=candidateEven x ∧ sourceOdd x=candidateOdd x
    · simp [exceptional,joint,count]
    · apply Nat.le_trans _ (affine_pair_coincidence_count sample distinct
        (sourceEven x) (sourceOdd x) (candidateEven x) (candidateOdd x) joint)
      apply count_mono
      intro r h
      exact h.2
  have union := finite_candidate_union_count sample domain exceptional 1 each
  have inclusion : count sample (fun r => threshold≤consistencyMass domain weight
      (fun x => (1-r)*sourceEven x+r*sourceOdd x=
        (1-r)*candidateEven x+r*candidateOdd x))≤
      count sample (fun r => ∃ x∈domain,exceptional x r) := by
    apply count_mono
    intro r success
    apply Classical.byContradiction
    intro absent
    have mass := consistency_mass_mono domain weight
      (fun x => (1-r)*sourceEven x+r*sourceOdd x=(1-r)*candidateEven x+r*candidateOdd x)
      (fun x => sourceEven x=candidateEven x ∧ sourceOdd x=candidateOdd x) (by
        intro x hx equal
        apply Classical.byContradiction
        intro different
        exact absent ⟨x,hx,different,equal⟩)
    omega
  simp only [Nat.mul_one] at union
  omega

/-- A sufficiently large set of challenges sharing ONE candidate curve
preserves the original weighted threshold, rather than intersecting their
agreement sets and losing proximity. -/
theorem shared_curve_joint_agreement {A : Type} (domain : List A)
    (weight : A → Nat) (sourceEven sourceOdd candidateEven candidateOdd : A → K)
    (threshold : Nat) (sample : List K) (distinct : sample.Nodup)
    (many : domain.length<count sample (fun r => threshold≤consistencyMass domain weight
      (fun x => (1-r)*sourceEven x+r*sourceOdd x=
        (1-r)*candidateEven x+r*candidateOdd x))) :
    threshold≤consistencyMass domain weight
      (fun x => sourceEven x=candidateEven x ∧ sourceOdd x=candidateOdd x) := by
  have impossible : ¬consistencyMass domain weight
      (fun x => sourceEven x=candidateEven x ∧ sourceOdd x=candidateOdd x)<threshold := by
    intro below
    have bound := shared_curve_below_threshold_count domain weight sourceEven sourceOdd
      candidateEven candidateOdd threshold below sample distinct
    omega
  omega

/-- Once a fixed affine candidate curve is shared by sufficiently many decoded
successes, the remaining weighted nonlinear extraction conclusion is proved.
The curve-selection/concentration theorem itself is NOT assumed proved. -/
theorem shared_polynomial_curve_extraction {A : Type} (domain : List A)
    (weight : A → Nat) (sourceEven sourceOdd point : A → K)
    (even odd sent : Poly K) (weights : List K) (w0 w1 : K) (threshold : Nat)
    (sample : List K) (distinct : sample.Nodup)
    (many : domain.length<sample.length) (three : 3≤sample.length)
    (sentDegree : sent.DegLt 3)
    (agreement : ∀ r∈sample,threshold≤consistencyMass domain weight
      (fun x => (1-r)*sourceEven x+r*sourceOdd x=
        (1-r)*even.eval (point x)+r*odd.eval (point x)))
    (residual : ∀ r∈sample,((1-r)*w0+r*w1)*scalarRSResidual weights
      (Poly.smul (1-r) even+Poly.smul r odd)=sent.eval r) :
    threshold≤consistencyMass domain weight
      (fun x => sourceEven x=even.eval (point x) ∧ sourceOdd x=odd.eval (point x)) ∧
    (sent-weightedFoldResidualPolynomial w0 w1
      (scalarRSResidual weights even) (scalarRSResidual weights odd)).IsZero := by
  classical
  constructor
  · apply shared_curve_joint_agreement domain weight sourceEven sourceOdd
      (fun x => even.eval (point x)) (fun x => odd.eval (point x)) threshold sample distinct
    have all : count sample (fun r => threshold≤consistencyMass domain weight
        (fun x => (1-r)*sourceEven x+r*sourceOdd x=
          (1-r)*even.eval (point x)+r*odd.eval (point x)))=sample.length := by
      unfold count
      apply List.countP_eq_length.mpr
      intro r hr
      exact @_root_.decide_eq_true _ (Classical.propDecidable _) (agreement r hr)
    rw [all]
    exact many
  · apply PolyRoots.eqZeroOfRoots_of polyEval polyDeg quotFacts isZeroEval K
      (sent-weightedFoldResidualPolynomial w0 w1
        (scalarRSResidual weights even) (scalarRSResidual weights odd)) 3 sample
    · exact Poly.degLt_sub sentDegree (Poly.degLt_length _)
    · exact distinct
    · exact three
    · intro r hr
      rw [Poly.eval_sub,weighted_fold_residual_polynomial_eval]
      have value := residual r hr
      rw [affine_weighted_residual_actual] at value
      grind

end NearCompression
