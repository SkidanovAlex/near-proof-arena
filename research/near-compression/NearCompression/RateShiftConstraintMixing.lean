import NearCompression.ScalarRSTerminal
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- One candidate supplies the old functional AND all OOD/query evaluations.
Candidate selection/extraction from a committed oracle is deliberately external. -/
def rateShiftCandidateValues (weights points : List K) (candidate : Poly K) : List K :=
  scalarRSResidual weights candidate :: points.map candidate.eval

def rateShiftAccumulatedFunctional (weights points : List K) (gamma : K) (candidate : Poly K) : K :=
  (Poly.mk (rateShiftCandidateValues weights points candidate)).eval gamma

def rateShiftAccumulatedClaim (claim : K) (values : List K) (gamma : K) : K :=
  (Poly.mk (claim::values)).eval gamma

/-- No division by equality weights or mixing challenge. -/
theorem rate_shift_mixing_completeness (weights points : List K) (candidate : Poly K)
    (claim gamma : K) (values : List K)
    (old : scalarRSResidual weights candidate=claim) (evaluations : points.map candidate.eval=values) :
    rateShiftAccumulatedFunctional weights points gamma candidate=rateShiftAccumulatedClaim claim values gamma := by
  simp only [rateShiftAccumulatedFunctional,rateShiftAccumulatedClaim,rateShiftCandidateValues,old,evaluations]

/-- Explicit polynomial discrepancy for the implemented power-weight accumulator. -/
theorem rate_shift_mixing_error (weights points : List K) (candidate : Poly K)
    (claim gamma : K) (values : List K) :
    rateShiftAccumulatedFunctional weights points gamma candidate-rateShiftAccumulatedClaim claim values gamma=
    ((Poly.mk (rateShiftCandidateValues weights points candidate))-(Poly.mk (claim::values))).eval gamma := by
  simp only [Poly.eval_sub,rateShiftAccumulatedFunctional,rateShiftAccumulatedClaim]

/-- Fixed-candidate bound. The candidate and all claims must precede gamma.
It cannot be applied to a candidate selected after seeing gamma. A future
rate-shift proof needs an independently bounded prechallenge candidate list. -/
theorem rate_shift_fixed_candidate_bad_count (weights points : List K) (candidate : Poly K)
    (claim : K) (values sample : List K) (shape : values.length=points.length)
    (distinct : sample.Nodup) (slot : Nat)
    (wrong : (rateShiftCandidateValues weights points candidate).getD slot 0≠(claim::values).getD slot 0) :
    count sample (fun gamma=>rateShiftAccumulatedFunctional weights points gamma candidate=
      rateShiftAccumulatedClaim claim values gamma)≤points.length := by
  let difference := (Poly.mk (rateShiftCandidateValues weights points candidate))-(Poly.mk (claim::values))
  have nz : ¬difference.IsZero := by
    intro zero
    have h:=zero slot
    change ((Poly.mk (rateShiftCandidateValues weights points candidate))-(Poly.mk (claim::values))).coeff slot=0 at h
    rw [Poly.coeff_sub] at h
    change (rateShiftCandidateValues weights points candidate).getD slot 0-(claim::values).getD slot 0=0 at h
    exact wrong (by grind)
  have degree : difference.DegLt (points.length+1) := by
    apply Poly.degLt_sub
    · simpa [rateShiftCandidateValues] using Poly.degLt_length (Poly.mk (rateShiftCandidateValues weights points candidate))
    · simpa [shape] using Poly.degLt_length (Poly.mk (claim::values))
  have roots:=PolyRoots.cardRootsLe_of polyEval polyDeg quotFacts isZeroEval K difference (points.length+1) sample nz degree distinct
  have subset : count sample (fun gamma=>rateShiftAccumulatedFunctional weights points gamma candidate=
      rateShiftAccumulatedClaim claim values gamma)≤count sample (fun gamma=>difference.eval gamma=0) := by
    apply count_mono
    intro gamma equal
    change ((Poly.mk (rateShiftCandidateValues weights points candidate))-(Poly.mk (claim::values))).eval gamma=0
    rw [←rate_shift_mixing_error,equal]
    grind
  omega
end NearCompression
