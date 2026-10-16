import NearCompression.RateShiftCandidateList
import NearCompression.IndependentQueryBudget
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- False-constraint complement gives every equation, not merely their mix. -/
theorem rate_shift_unmixed_constraints (weights points values : List K) (candidate : Poly K)
    (claim : K) (shape : values.length=points.length)
    (correct : ¬rateShiftCandidateWrong weights points candidate claim values) :
    scalarRSResidual weights candidate=claim ∧ points.map candidate.eval=values := by
  have entries : ∀ i,(rateShiftCandidateValues weights points candidate).getD i 0=(claim::values).getD i 0 := by
    intro i
    apply Classical.byContradiction
    intro different
    exact correct ⟨i,different⟩
  have equal : rateShiftCandidateValues weights points candidate=claim::values := by
    apply List.ext_getElem (by simp [rateShiftCandidateValues,shape])
    intro i hi hj
    have h:=entries i
    simpa only [List.getD,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,Option.getD_some] using h
  exact List.cons.inj equal

/-- The candidate family precedes all query draws. Selection after seeing the
queries is allowed inside the finite-family union. -/
theorem rate_shift_query_family_bound {I : Type} (seeds : List I) (q T : Nat)
    (family : List (Poly K)) (point source : I→K) (weights : List K) (claim : K)
    (noClose : ∀ p∈family,scalarRSResidual weights p=claim →
      count seeds (fun i=>p.eval (point i)=source i)<T) :
    count (uniformTuples seeds q) (fun queries=>∃ p∈family,
      scalarRSResidual weights p=claim ∧ allQueriesPass (fun i=>p.eval (point i)=source i) queries)
      ≤family.length*(T-1)^q := by
  classical
  apply finite_candidate_union_count
  intro p hp
  by_cases functional : scalarRSResidual weights p=claim
  · have few:=noClose p hp functional
    have bound : count seeds (fun i=>p.eval (point i)=source i)≤T-1 := by omega
    have subset : count (uniformTuples seeds q) (fun queries=>scalarRSResidual weights p=claim ∧
        allQueriesPass (fun i=>p.eval (point i)=source i) queries)≤
        count (uniformTuples seeds q) (allQueriesPass (fun i=>p.eval (point i)=source i)) :=
      count_mono _ (fun _ h=>h.2)
    rw [independent_query_count] at subset
    exact Nat.le_trans subset (Nat.pow_le_pow_left bound q)
  · simp [functional,count]

/-- Failure of the joint theorem's noCorrect premise is bounded by source
query sampling. The OOD constraint is retained in the event but need not
improve this bound. Transfer of noClose from the prior oracle is separate. -/
theorem rate_shift_query_no_correct_bound {I : Type} (seeds : List I) (q T : Nat)
    (domain : List K) (received : K→K) (D radius : Nat)
    (point source : I→K) (weights : List K) (claim z y : K)
    (noClose : ∀ p∈rateShiftUniqueList domain received D radius,
      scalarRSResidual weights p=claim → count seeds (fun i=>p.eval (point i)=source i)<T) :
    count (uniformTuples seeds q) (fun queries=>∃ p∈rateShiftUniqueList domain received D radius,
      ¬rateShiftCandidateWrong weights (z::queries.map point) p claim (y::queries.map source))≤(T-1)^q := by
  let family:=rateShiftUniqueList domain received D radius
  have bound:=rate_shift_query_family_bound seeds q T family point source weights claim noClose
  have subset : count (uniformTuples seeds q) (fun queries=>∃ p∈family,
      ¬rateShiftCandidateWrong weights (z::queries.map point) p claim (y::queries.map source))≤
      count (uniformTuples seeds q) (fun queries=>∃ p∈family,
        scalarRSResidual weights p=claim ∧ allQueriesPass (fun i=>p.eval (point i)=source i) queries) := by
    apply count_mono
    intro queries h
    obtain ⟨p,hp,correct⟩:=h
    have equations:=rate_shift_unmixed_constraints weights (z::queries.map point) (y::queries.map source)
      p claim (by simp) correct
    refine ⟨p,hp,equations.1,?_⟩
    have tails:= (List.cons.inj equations.2).2
    simp only [List.map_map,Function.comp_def] at tails
    exact List.map_eq_map_iff.mp tails
  have len:=rate_shift_unique_list_length domain received D radius
  have small:=Nat.mul_le_mul_right ((T-1)^q) len
  simp only [Nat.one_mul] at small
  exact Nat.le_trans subset (Nat.le_trans bound small)
end NearCompression
