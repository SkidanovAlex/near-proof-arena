import NearCompression.GeneralCurveConcentrationReduction
import NearCompression.SharedLaneInterpolation

/-! Constructive affine-curve identification from D common agreement points.
This is an unconditional per-support bound, not an efficient global bound:
summing over all possible supports can be exponentially expensive. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- D fixed distinct points determine the candidate for every challenge as the
same affine combination of the two source interpolants. -/
theorem curve_support_interpolation [DecidableEq K]
    (points : List K) (distinct : points.Nodup) (D : Nat) (size : points.length=D)
    (sourceEven sourceOdd : K → K) (r : K) (candidate : Poly K)
    (degree : candidate.DegLt D)
    (agreement : ∀ x∈points,candidate.eval x=(1-r)*sourceEven x+r*sourceOdd x) :
    (∀ i,candidate.coeff i=
      (Poly.smul (1-r) (Poly.lagrange points sourceEven)+
        Poly.smul r (Poly.lagrange points sourceOdd)).coeff i) ∧
    (∀ x,candidate.eval x=
      (Poly.smul (1-r) (Poly.lagrange points sourceEven)+
        Poly.smul r (Poly.lagrange points sourceOdd)).eval x) := by
  apply scalar_rs_domain_unique candidate _ D points degree
  · apply Poly.degLt_add
    · apply Poly.degLt_smul
      simpa only [size] using (PolyRoots.lagrange_of polyEval polyDeg K points sourceEven).1
    · apply Poly.degLt_smul
      simpa only [size] using (PolyRoots.lagrange_of polyEval polyDeg K points sourceOdd).1
  · exact distinct
  · omega
  · intro x hx
    rw [Poly.eval_add,Poly.eval_smul,Poly.eval_smul,
      (PolyRoots.lagrange_of polyEval polyDeg K points sourceEven).2 distinct x hx,
      (PolyRoots.lagrange_of polyEval polyDeg K points sourceOdd).2 distinct x hx]
    exact agreement x hx

/-- Candidate existence remains inside the challenge event. Each candidate
must also agree on this particular prechallenge support. -/
def generalSupportedCurveSuccess (domain points : List K) (weight : K → Nat)
    (sourceEven sourceOdd : K → K) (D T : Nat) (ew ow : List K)
    (sent : Poly K) (r : K) : Prop :=
  ∃ p : Poly K,p.DegLt D ∧
    (∀ x∈points,p.eval x=(1-r)*sourceEven x+r*sourceOdd x) ∧
    T≤consistencyMass domain weight
      (fun x => p.eval x=(1-r)*sourceEven x+r*sourceOdd x) ∧
    (1-r)*scalarRSResidual ew p+r*scalarRSResidual ow p=sent.eval r

/-- Per-support concentration bound with no concentration or transfer premise.
Supports need not themselves carry threshold mass. -/
theorem supported_curve_bad_count [DecidableEq K]
    (domain points sample : List K) (distinct : points.Nodup) (sampleDistinct : sample.Nodup)
    (D T : Nat) (size : points.length=D) (weight : K → Nat)
    (sourceEven sourceOdd : K → K) (ew ow : List K) (sent : Poly K)
    (sentDegree : sent.DegLt 3)
    (noOutcome : ¬∃ even odd : Poly K,even.DegLt D ∧ odd.DegLt D ∧
      T≤consistencyMass domain weight
        (fun x => sourceEven x=even.eval x ∧ sourceOdd x=odd.eval x) ∧
      (sent-generalFoldResidualPolynomial ew ow even odd).IsZero) :
    count sample (generalSupportedCurveSuccess domain points weight sourceEven sourceOdd D T ew ow sent)
      ≤max domain.length 2 := by
  classical
  let even := Poly.lagrange points sourceEven
  let odd := Poly.lagrange points sourceOdd
  have de : even.DegLt D := by
    simpa only [size] using (PolyRoots.lagrange_of polyEval polyDeg K points sourceEven).1
  have do_ : odd.DegLt D := by
    simpa only [size] using (PolyRoots.lagrange_of polyEval polyDeg K points sourceOdd).1
  have subset : count sample
      (generalSupportedCurveSuccess domain points weight sourceEven sourceOdd D T ew ow sent)≤
      count sample (generalFixedCurveSuccess domain weight sourceEven sourceOdd T ew ow sent even odd) := by
    apply count_mono
    intro r success
    obtain ⟨p,degree,atPoints,agree,residual⟩ := success
    have equal := curve_support_interpolation points distinct D size sourceEven sourceOdd r p degree atPoints
    constructor
    · apply Nat.le_trans agree
      apply consistency_mass_mono
      intro x hx h
      rw [equal.2 x,Poly.eval_add,Poly.eval_smul,Poly.eval_smul] at h
      exact h.symm
    · rw [scalar_rs_residual_congr p _ ew equal.1,
        scalar_rs_residual_congr p _ ow equal.1] at residual
      exact residual
  apply Classical.byContradiction
  intro notBound
  have many : max domain.length 2<count sample
      (generalFixedCurveSuccess domain weight sourceEven sourceOdd T ew ow sent even odd) := by omega
  exact noOutcome ⟨even,odd,de,do_,general_fixed_curve_many_outcome domain sample sampleDistinct
    weight sourceEven sourceOdd T ew ow sent even odd sentDegree many⟩

end NearCompression
