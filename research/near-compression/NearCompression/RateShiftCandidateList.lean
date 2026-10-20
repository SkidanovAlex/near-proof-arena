import NearCompression.RateShiftConstraintMixing
import NearCompression.FiniteBatchCandidates
import NearCompression.FiniteRSUniqueDecoding
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- False constituent constraints on a fixed candidate; true candidates are
not included in the bad mixing event. -/
def rateShiftCandidateWrong (weights points : List K) (candidate : Poly K)
    (claim : K) (values : List K) : Prop :=
  ∃ slot,(rateShiftCandidateValues weights points candidate).getD slot 0≠(claim::values).getD slot 0

/-- The family is fixed before gamma, but the accepting candidate may vary
with gamma within that family. No assumption that every candidate is false. -/
theorem rate_shift_list_mixing_bound (family : List (Poly K)) (weights points : List K)
    (claim : K) (values sample : List K) (shape : values.length=points.length)
    (distinct : sample.Nodup) :
    count sample (fun gamma=>∃ candidate∈family,
      rateShiftCandidateWrong weights points candidate claim values ∧
      rateShiftAccumulatedFunctional weights points gamma candidate=rateShiftAccumulatedClaim claim values gamma)
      ≤family.length*points.length := by
  apply finite_candidate_union_count
  intro candidate member
  classical
  by_cases wrong : rateShiftCandidateWrong weights points candidate claim values
  · obtain ⟨slot,hslot⟩:=wrong
    apply Nat.le_trans ?_ (rate_shift_fixed_candidate_bad_count weights points candidate claim values sample shape distinct slot hslot)
    apply count_mono
    intro gamma h
    exact h.2
  · simp [wrong,count]

/-- Normalized degree-bounded candidates near the already fixed next oracle.
Exactly D coefficients prevents distinct trailing-zero encodings. -/
def RateShiftCloseCandidate (domain : List K) (received : K→K) (D radius : Nat) (candidate : Poly K) : Prop :=
  candidate.coeffs.length=D ∧ finiteRSMismatches domain received candidate.eval≤radius

theorem rate_shift_close_unique (domain : List K) (distinct : domain.Nodup)
    (received : K→K) (D radius : Nat) (separation : 2*radius+D≤domain.length)
    (left right : Poly K) (hl : RateShiftCloseCandidate domain received D radius left)
    (hr : RateShiftCloseCandidate domain received D radius right) : left=right := by
  have dl : left.DegLt D := by simpa only [hl.1] using Poly.degLt_length left
  have dr : right.DegLt D := by simpa only [hr.1] using Poly.degLt_length right
  have zero:=finite_rs_unique_candidate domain distinct received left right D radius radius dl dr hl.2 hr.2 (by omega)
  have lists : left.coeffs=right.coeffs := by
    apply List.ext_getElem (hl.1.trans hr.1.symm)
    intro i hi hj
    have h:=zero i
    rw [Poly.coeff_sub,Poly.coeff_def,Poly.coeff_def] at h
    simp only [List.getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,Option.getD_some] at h
    grind
  cases left;cases right
  simp_all

/-- Choice depends on domain, received oracle and radius only: it has no
mixing challenge, OOD point, query list, or new functional as an argument.
This constructs the list without assuming existence of a close candidate. -/
noncomputable def rateShiftUniqueList (domain : List K) (received : K→K) (D radius : Nat) : List (Poly K) := by
  classical
  exact if h : ∃ p,RateShiftCloseCandidate domain received D radius p then [Classical.choose h] else []

theorem rate_shift_unique_list_length (domain : List K) (received : K→K) (D radius : Nat) :
    (rateShiftUniqueList domain received D radius).length≤1 := by
  classical
  unfold rateShiftUniqueList
  split <;> simp

/-- Every close candidate belongs to the prechallenge list under the explicit
integer unique-decoding separation. No Merkle-root extraction is claimed. -/
theorem rate_shift_unique_list_complete (domain : List K) (distinct : domain.Nodup)
    (received : K→K) (D radius : Nat) (separation : 2*radius+D≤domain.length)
    (candidate : Poly K) (close : RateShiftCloseCandidate domain received D radius candidate) :
    candidate∈rateShiftUniqueList domain received D radius := by
  classical
  unfold rateShiftUniqueList
  split
  next existsCandidate=>
    have same:=rate_shift_close_unique domain distinct received D radius separation candidate
      (Classical.choose existsCandidate) close (Classical.choose_spec existsCandidate)
    simp [same]
  next missing=>exact False.elim (missing ⟨candidate,close⟩)

/-- Union over all close, normalized candidates has no list-size penalty in
the unique regime. Closeness is in the counted event, not an existence premise. -/
theorem rate_shift_unique_mixing_bound (domain : List K) (domainDistinct : domain.Nodup)
    (received : K→K) (D radius : Nat) (separation : 2*radius+D≤domain.length)
    (weights points : List K) (claim : K) (values sample : List K)
    (shape : values.length=points.length) (sampleDistinct : sample.Nodup) :
    count sample (fun gamma=>∃ candidate,
      RateShiftCloseCandidate domain received D radius candidate ∧
      rateShiftCandidateWrong weights points candidate claim values ∧
      rateShiftAccumulatedFunctional weights points gamma candidate=rateShiftAccumulatedClaim claim values gamma)
      ≤points.length := by
  have union:=rate_shift_list_mixing_bound (rateShiftUniqueList domain received D radius)
    weights points claim values sample shape sampleDistinct
  have len:=rate_shift_unique_list_length domain received D radius
  have subset : count sample (fun gamma=>∃ candidate,
      RateShiftCloseCandidate domain received D radius candidate ∧
      rateShiftCandidateWrong weights points candidate claim values ∧
      rateShiftAccumulatedFunctional weights points gamma candidate=rateShiftAccumulatedClaim claim values gamma)
      ≤count sample (fun gamma=>∃ candidate∈rateShiftUniqueList domain received D radius,
      rateShiftCandidateWrong weights points candidate claim values ∧
      rateShiftAccumulatedFunctional weights points gamma candidate=rateShiftAccumulatedClaim claim values gamma) := by
    apply count_mono
    intro gamma h
    obtain ⟨candidate,close,wrong,equal⟩:=h
    exact ⟨candidate,rate_shift_unique_list_complete domain domainDistinct received D radius separation candidate close,wrong,equal⟩
  have small:=Nat.mul_le_mul_right points.length len
  simp only [Nat.one_mul] at small
  exact Nat.le_trans subset (Nat.le_trans union small)
end NearCompression
