import NearCompression.CheckedBusFailureSelection
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra ArenaCore.Security

/-- On an earlier-transcript family where this table has invalid generated
bus residuals, exact certificate checks derive the adaptive local error bound.
Decoded traces, formula lists and violated rows may vary with earlier history,
but cannot depend on this table's later local challenges. Terminal repair and
the joint downstream error budget remain explicit composition premises. -/
theorem checked_auxiliary_after_earlier_budget {A R : Type}
    (sample : List Fp8) (distinct : sample.Nodup) (earlier : List A)
    (tr : A → Trace Fp8) (t : Nat) (sourceWidth : Nat → Nat) (publicValues : List Fp8)
    (interactions : A → List (BusFormulaInteraction Fp8)) (finals : A → Nat → Fp8)
    (source : List Expr) (auxiliary : A → List (BusProgramFormula Fp8))
    (auxiliaryLength : Nat) (auxiliaryShape : ∀ a∈earlier,(auxiliary a).length=auxiliaryLength)
    (residuals : A → List (AIRBusResidual Fp8 × Nat))
    (order : ∀ a∈earlier,(residuals a).map Prod.fst=source.map Sum.inl++(auxiliary a).map Sum.inr)
    (d n : Nat) (positive : 0<source.length+auxiliaryLength)
    (logs : ∀ a∈earlier,(tr a).log t=n+1)
    (checked : ∀ a∈earlier,generatedExt8BusSpecCheck (interactions a) (sourceWidth t)
      (finals a) (auxiliary a)=true)
    (base : ∀ a∈earlier,∀ e∈auxiliary a,∀ row c,
      c<busFormulaColumnBound e → Fp8.IsBase ((tr a).cell t row c))
    (invalid : ∀ a∈earlier,¬∀ row,row<(tr a).height t →
      ∀ e∈busTableResiduals (interactions a) (sourceWidth t) (finals a),
        busProgramFormulaValue
          (busRowProgramEnv (airAuxCoordinateTrace (decodedBaseTrace (tr a)) sourceWidth) t row) e=0)
    (sourceDegrees : ∀ e∈source,e.degree≤d) (auxDegrees : ∀ a∈earlier,∀ e∈auxiliary a,busFormulaDegree e≤d)
    (sent : A → Fp8 → List Fp8 → List Fp8 → Poly Fp8) (claim : A → Fp8 → List Fp8 → List Fp8 → Fp8)
    (initialZero : ∀ a∈earlier,∀ mixing tau,claim a mixing tau []=0)
    (continuations : List R) (accept : A → LocalChallengePrefix Fp8 → R → Prop)
    (checks : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ r∈continuations,
      accept a p r → decodedLocalChecks d (sent a) (claim a) p)
    (repair pcsBudget : Nat) (errors : A → LocalChallengePrefix Fp8 → Nat)
    (wrongTerminal : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),
      ¬decodedLocalTerminalCorrect (n+1) (fun column row=>(tr a).cell t row column) publicValues (residuals a) (claim a) p →
      count continuations (accept a p)*sample.length≤repair+errors a p*sample.length)
    (jointErrors : (earlier.map (fun a => ((decodedLocalPrefixes sample (n+1)).map (errors a)).sum)).sum*
      sample.length≤pcsBudget) :
    count (earlier.flatMap (fun a => (decodedLocalPrefixes sample (n+1)).flatMap (fun p =>
      continuations.map (fun r => (a,p,r))))) (fun x => accept x.1 x.2.1 x.2.2)*sample.length≤
      earlier.length*
        (((source.length+auxiliaryLength-1+(n+1)+(d+1)*(n+1))*sample.length^(2*(n+1)+1))*continuations.length+
          (decodedLocalPrefixes sample (n+1)).length*repair)+pcsBudget := by
  classical
  have invalidRows : ∀ a∈earlier,¬∀ row,row<2^(n+1) → ∀ lane,
      (airCombinedRowResiduals
        (decodedTableTrace (n+1) (fun column row=>(tr a).cell t row column)) 0
        publicValues source (auxiliary a) row).getD lane 0=0 := by
    intro a ha zero
    apply invalid a ha
    intro row hr e he
    apply Classical.byContradiction
    intro wrong
    obtain ⟨_,lane,nonzero⟩ := checked_bus_failure_combined_index (tr a) sourceWidth t row
      publicValues source (interactions a) (finals a) (auxiliary a) (checked a ha) (base a ha) e he wrong
    have same := decoded_table_combined_residuals (tr a) t row publicValues source (auxiliary a)
    rw [logs a ha] at same
    rw [←same] at nonzero
    exact nonzero (zero row (by simpa only [Trace.height,logs a ha] using hr) lane)
  exact decoded_adaptive_invalid_rows_budget sample distinct earlier
    (fun a column row=>(tr a).cell t row column) publicValues source auxiliary auxiliaryLength
    auxiliaryShape residuals order d n positive invalidRows sourceDegrees auxDegrees sent claim
    initialZero continuations accept checks repair pcsBudget errors wrongTerminal jointErrors

end NearCompression
