import NearCompression.TwoTablePCSExperiment
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra ArenaCore.Security

/-- An invalid decoded table may be proved after an arbitrary earlier
transcript. Its local strategy can depend on that entire transcript. Only
the final joint error sum is budgeted; errors need not be small for each
earlier transcript or each local rowpoint. -/
theorem decoded_invalid_table_after_earlier_budget {K A R : Type} [Field K]
    (sample : List K) (distinct : sample.Nodup) (earlier : List A)
    (decoded : Nat → Nat → K) (publicValues : List K)
    (source : List Expr) (auxiliary : List (BusProgramFormula K))
    (residuals : List (AIRBusResidual K × Nat))
    (order : residuals.map Prod.fst=source.map Sum.inl++auxiliary.map Sum.inr)
    (d n row lane : Nat) (positive : 0<source.length+auxiliary.length) (rowBound : row<2^(n+1))
    (wrong : (airCombinedRowResiduals (decodedTableTrace (n+1) decoded) 0 publicValues source auxiliary row).getD lane 0≠0)
    (sourceDegrees : ∀ e∈source,e.degree≤d) (auxDegrees : ∀ e∈auxiliary,busFormulaDegree e≤d)
    (sent : A → K → List K → List K → Poly K) (claim : A → K → List K → List K → K)
    (initialZero : ∀ a∈earlier,∀ mixing tau,claim a mixing tau []=0)
    (continuations : List R) (accept : A → LocalChallengePrefix K → R → Prop)
    (checks : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ r∈continuations,
      accept a p r → decodedLocalChecks d (sent a) (claim a) p)
    (repair pcsBudget : Nat) (errors : A → LocalChallengePrefix K → Nat)
    (wrongTerminal : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),
      ¬decodedLocalTerminalCorrect (n+1) decoded publicValues residuals (claim a) p →
      count continuations (accept a p)*sample.length≤repair+errors a p*sample.length)
    (jointErrors : (earlier.map (fun a => ((decodedLocalPrefixes sample (n+1)).map (errors a)).sum)).sum*
      sample.length≤pcsBudget) :
    count (earlier.flatMap (fun a => (decodedLocalPrefixes sample (n+1)).flatMap (fun p =>
      continuations.map (fun r => (a,p,r))))) (fun x => accept x.1 x.2.1 x.2.2)*sample.length≤
      earlier.length*
        (((source.length+auxiliary.length-1+(n+1)+(d+1)*(n+1))*sample.length^(2*(n+1)+1))*continuations.length+
          (decodedLocalPrefixes sample (n+1)).length*repair)+pcsBudget := by
  classical
  have each := fun a ha => decoded_invalid_trace_continuation_budget sample distinct decoded publicValues
    source auxiliary residuals order d n row lane positive rowBound wrong sourceDegrees auxDegrees
    (sent a) (claim a) (initialZero a ha) continuations (accept a) (checks a ha) repair
    (((decodedLocalPrefixes sample (n+1)).map (errors a)).sum*sample.length) (errors a)
    (wrongTerminal a ha) (Nat.le_refl _)
  have summed := sum_scaled_error_budget earlier
    (fun a => ((decodedLocalPrefixes sample (n+1)).map (fun p => count continuations (accept a p))).sum)
    (fun a => ((decodedLocalPrefixes sample (n+1)).map (errors a)).sum)
    sample.length _ each
  have result := Nat.le_trans summed (Nat.add_le_add_left jointErrors _)
  simpa only [count,List.countP_flatMap,List.countP_map,Function.comp_def] using result

/-- Error sums over earlier/local prefixes are a single chronological count,
which can include the absent-representative event as well as terminal errors. -/
theorem earlier_local_error_count {K A R : Type} [Field K]
    (sample : List K) (rowLog : Nat) (earlier : List A) (continuations : List R)
    (event : A → LocalChallengePrefix K → R → Prop) :
    (earlier.map (fun a => ((decodedLocalPrefixes sample rowLog).map
      (fun p => count continuations (event a p))).sum)).sum=
    count (earlier.flatMap (fun a => (decodedLocalPrefixes sample rowLog).flatMap (fun p =>
      continuations.map (fun r => (a,p,r))))) (fun x => event x.1 x.2.1 x.2.2) := by
  classical
  simp only [count,List.countP_flatMap,List.countP_map,Function.comp_def]

end NearCompression
