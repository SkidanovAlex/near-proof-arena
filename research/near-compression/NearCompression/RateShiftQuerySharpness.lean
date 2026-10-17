import NearCompression.RateShiftQueryTransfer
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- If the old functional is correct and the OOD answer is the candidate's
own evaluation, the same-candidate condition reduces exactly to source queries.
This does not assert that such a candidate meets all earlier protocol checks. -/
theorem rate_shift_truthful_ood_iff {I : Type}
    (candidate : Poly K) (weights : List K) (claim z : K)
    (point source : I → K) (queries : List I)
    (functional : scalarRSResidual weights candidate=claim) :
    (¬rateShiftCandidateWrong weights (z::queries.map point) candidate claim
      (candidate.eval z::queries.map source)) ↔
      allQueriesPass (fun i=>candidate.eval (point i)=source i) queries := by
  constructor
  · intro correct
    have equations:=rate_shift_unmixed_constraints weights (z::queries.map point)
      (candidate.eval z::queries.map source) candidate claim (by simp) correct
    have tails:=(List.cons.inj equations.2).2
    simp only [List.map_map,Function.comp_def] at tails
    exact List.map_eq_map_iff.mp tails
  · intro passes
    have tails : (queries.map point).map candidate.eval=queries.map source := by
      simp only [List.map_map,Function.comp_def]
      exact List.map_eq_map_iff.mpr passes
    have same : rateShiftCandidateValues weights (z::queries.map point) candidate=
        claim::(candidate.eval z::queries.map source) := by
      simp only [rateShiftCandidateValues,List.map_cons,functional,tails]
    intro wrong
    obtain ⟨slot,different⟩:=wrong
    exact different (congrArg (fun xs=>xs.getD slot 0) same)

/-- Exact acceptance count for the source-query/same-candidate interface,
for EVERY OOD point. A truthful OOD value alone gives no additional factor. -/
theorem rate_shift_truthful_ood_query_count {I : Type}
    (seeds : List I) (q : Nat) (candidate : Poly K)
    (weights : List K) (claim z : K) (point source : I → K)
    (functional : scalarRSResidual weights candidate=claim) :
    count (uniformTuples seeds q) (fun queries=>
      ¬rateShiftCandidateWrong weights (z::queries.map point) candidate claim
        (candidate.eval z::queries.map source))=
      (count seeds (fun i=>candidate.eval (point i)=source i))^q := by
  have same : count (uniformTuples seeds q) (fun queries=>
      ¬rateShiftCandidateWrong weights (z::queries.map point) candidate claim
        (candidate.eval z::queries.map source))=
      count (uniformTuples seeds q) (allQueriesPass (fun i=>candidate.eval (point i)=source i)) := by
    apply Nat.le_antisymm
    · apply count_mono
      intro queries h
      exact (rate_shift_truthful_ood_iff candidate weights claim z point source queries functional).mp h
    · apply count_mono
      intro queries h
      exact (rate_shift_truthful_ood_iff candidate weights claim z point source queries functional).mpr h
  rw [same,independent_query_count]

/-- The existing strict agreement threshold is attained at T-1 matches.
Any stronger source-query bound needs stronger premises, not just an OOD
point whose answer is unconstrained by a separate prior-oracle relation. -/
theorem rate_shift_source_threshold_sharp {I : Type}
    (seeds : List I) (q T : Nat) (candidate : Poly K)
    (weights : List K) (claim z : K) (point source : I → K)
    (functional : scalarRSResidual weights candidate=claim)
    (agreement : count seeds (fun i=>candidate.eval (point i)=source i)=T-1) :
    count (uniformTuples seeds q) (fun queries=>
      ¬rateShiftCandidateWrong weights (z::queries.map point) candidate claim
        (candidate.eval z::queries.map source))=(T-1)^q := by
  rw [rate_shift_truthful_ood_query_count seeds q candidate weights claim z point source functional,agreement]


end NearCompression
