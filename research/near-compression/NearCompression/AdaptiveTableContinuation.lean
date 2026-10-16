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

/-- Earlier bus challenges may change decoded auxiliary columns and auxiliary
formula constants. Local challenges still follow those choices. The residual
witness remains nonzero in each earlier fiber, and the PCS error is bounded
only after summing the whole chronological experiment. -/
theorem decoded_adaptive_table_after_earlier_budget {K A R : Type} [Field K]
    (sample : List K) (distinct : sample.Nodup) (earlier : List A)
    (decoded : A → Nat → Nat → K) (publicValues : List K)
    (source : List Expr) (auxiliary : A → List (BusProgramFormula K))
    (auxiliaryLength : Nat) (auxiliaryShape : ∀ a∈earlier,(auxiliary a).length=auxiliaryLength)
    (residuals : A → List (AIRBusResidual K × Nat))
    (order : ∀ a∈earlier,(residuals a).map Prod.fst=source.map Sum.inl++(auxiliary a).map Sum.inr)
    (d n row lane : Nat) (positive : 0<source.length+auxiliaryLength) (rowBound : row<2^(n+1))
    (wrong : ∀ a∈earlier,(airCombinedRowResiduals (decodedTableTrace (n+1) (decoded a)) 0 publicValues source (auxiliary a) row).getD lane 0≠0)
    (sourceDegrees : ∀ e∈source,e.degree≤d) (auxDegrees : ∀ a∈earlier,∀ e∈auxiliary a,busFormulaDegree e≤d)
    (sent : A → K → List K → List K → Poly K) (claim : A → K → List K → List K → K)
    (initialZero : ∀ a∈earlier,∀ mixing tau,claim a mixing tau []=0)
    (continuations : List R) (accept : A → LocalChallengePrefix K → R → Prop)
    (checks : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ r∈continuations,
      accept a p r → decodedLocalChecks d (sent a) (claim a) p)
    (repair pcsBudget : Nat) (errors : A → LocalChallengePrefix K → Nat)
    (wrongTerminal : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),
      ¬decodedLocalTerminalCorrect (n+1) (decoded a) publicValues (residuals a) (claim a) p →
      count continuations (accept a p)*sample.length≤repair+errors a p*sample.length)
    (jointErrors : (earlier.map (fun a => ((decodedLocalPrefixes sample (n+1)).map (errors a)).sum)).sum*
      sample.length≤pcsBudget) :
    count (earlier.flatMap (fun a => (decodedLocalPrefixes sample (n+1)).flatMap (fun p =>
      continuations.map (fun r => (a,p,r))))) (fun x => accept x.1 x.2.1 x.2.2)*sample.length≤
      earlier.length*
        (((source.length+auxiliaryLength-1+(n+1)+(d+1)*(n+1))*sample.length^(2*(n+1)+1))*continuations.length+
          (decodedLocalPrefixes sample (n+1)).length*repair)+pcsBudget := by
  classical
  have each : ∀ a∈earlier,
      ((decodedLocalPrefixes sample (n+1)).map (fun p=>count continuations (accept a p))).sum*sample.length ≤
      (((source.length+auxiliaryLength-1+(n+1)+(d+1)*(n+1))*sample.length^(2*(n+1)+1))*continuations.length+
        (decodedLocalPrefixes sample (n+1)).length*repair)+
      ((decodedLocalPrefixes sample (n+1)).map (errors a)).sum*sample.length := by
    intro a ha
    have h := decoded_invalid_trace_continuation_budget sample distinct (decoded a) publicValues
      source (auxiliary a) (residuals a) (order a ha) d n row lane
      (by rw [auxiliaryShape a ha];exact positive) rowBound (wrong a ha) sourceDegrees (auxDegrees a ha)
      (sent a) (claim a) (initialZero a ha) continuations (accept a) (checks a ha) repair
      (((decodedLocalPrefixes sample (n+1)).map (errors a)).sum*sample.length) (errors a)
      (wrongTerminal a ha) (Nat.le_refl _)
    simpa only [auxiliaryShape a ha] using h
  have summed := sum_scaled_error_budget earlier
    (fun a => ((decodedLocalPrefixes sample (n+1)).map (fun p => count continuations (accept a p))).sum)
    (fun a => ((decodedLocalPrefixes sample (n+1)).map (errors a)).sum)
    sample.length _ each
  have result := Nat.le_trans summed (Nat.add_le_add_left jointErrors _)
  simpa only [count,List.countP_flatMap,List.countP_map,Function.comp_def] using result

/-- An invalid auxiliary witness may depend on earlier bus challenges.
Its violated row and residual index may also vary with that earlier history,
but must be selected before this table's local challenges. -/
theorem decoded_adaptive_witness_after_earlier_budget {K A R : Type} [Field K]
    (sample : List K) (distinct : sample.Nodup) (earlier : List A)
    (decoded : A → Nat → Nat → K) (publicValues : List K)
    (source : List Expr) (auxiliary : A → List (BusProgramFormula K))
    (auxiliaryLength : Nat) (auxiliaryShape : ∀ a∈earlier,(auxiliary a).length=auxiliaryLength)
    (residuals : A → List (AIRBusResidual K × Nat))
    (order : ∀ a∈earlier,(residuals a).map Prod.fst=source.map Sum.inl++(auxiliary a).map Sum.inr)
    (d n : Nat) (row lane : A → Nat) (positive : 0<source.length+auxiliaryLength) (rowBound : ∀ a∈earlier,row a<2^(n+1))
    (wrong : ∀ a∈earlier,(airCombinedRowResiduals (decodedTableTrace (n+1) (decoded a)) 0 publicValues source (auxiliary a) (row a)).getD (lane a) 0≠0)
    (sourceDegrees : ∀ e∈source,e.degree≤d) (auxDegrees : ∀ a∈earlier,∀ e∈auxiliary a,busFormulaDegree e≤d)
    (sent : A → K → List K → List K → Poly K) (claim : A → K → List K → List K → K)
    (initialZero : ∀ a∈earlier,∀ mixing tau,claim a mixing tau []=0)
    (continuations : List R) (accept : A → LocalChallengePrefix K → R → Prop)
    (checks : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ r∈continuations,
      accept a p r → decodedLocalChecks d (sent a) (claim a) p)
    (repair pcsBudget : Nat) (errors : A → LocalChallengePrefix K → Nat)
    (wrongTerminal : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),
      ¬decodedLocalTerminalCorrect (n+1) (decoded a) publicValues (residuals a) (claim a) p →
      count continuations (accept a p)*sample.length≤repair+errors a p*sample.length)
    (jointErrors : (earlier.map (fun a => ((decodedLocalPrefixes sample (n+1)).map (errors a)).sum)).sum*
      sample.length≤pcsBudget) :
    count (earlier.flatMap (fun a => (decodedLocalPrefixes sample (n+1)).flatMap (fun p =>
      continuations.map (fun r => (a,p,r))))) (fun x => accept x.1 x.2.1 x.2.2)*sample.length≤
      earlier.length*
        (((source.length+auxiliaryLength-1+(n+1)+(d+1)*(n+1))*sample.length^(2*(n+1)+1))*continuations.length+
          (decodedLocalPrefixes sample (n+1)).length*repair)+pcsBudget := by
  classical
  have each : ∀ a∈earlier,
      ((decodedLocalPrefixes sample (n+1)).map (fun p=>count continuations (accept a p))).sum*sample.length ≤
      (((source.length+auxiliaryLength-1+(n+1)+(d+1)*(n+1))*sample.length^(2*(n+1)+1))*continuations.length+
        (decodedLocalPrefixes sample (n+1)).length*repair)+
      ((decodedLocalPrefixes sample (n+1)).map (errors a)).sum*sample.length := by
    intro a ha
    have h := decoded_invalid_trace_continuation_budget sample distinct (decoded a) publicValues
      source (auxiliary a) (residuals a) (order a ha) d n (row a) (lane a)
      (by rw [auxiliaryShape a ha];exact positive) (rowBound a ha) (wrong a ha) sourceDegrees (auxDegrees a ha)
      (sent a) (claim a) (initialZero a ha) continuations (accept a) (checks a ha) repair
      (((decodedLocalPrefixes sample (n+1)).map (errors a)).sum*sample.length) (errors a)
      (wrongTerminal a ha) (Nat.le_refl _)
    simpa only [auxiliaryShape a ha] using h
  have summed := sum_scaled_error_budget earlier
    (fun a => ((decodedLocalPrefixes sample (n+1)).map (fun p => count continuations (accept a p))).sum)
    (fun a => ((decodedLocalPrefixes sample (n+1)).map (errors a)).sum)
    sample.length _ each
  have result := Nat.le_trans summed (Nat.add_le_add_left jointErrors _)
  simpa only [count,List.countP_flatMap,List.countP_map,Function.comp_def] using result

/-- Select a violated row/index from failure of complete residual validity
for each earlier transcript, then instantiate the adaptive local bound. -/
theorem decoded_adaptive_invalid_rows_budget {K A R : Type} [Field K]
    (sample : List K) (distinct : sample.Nodup) (earlier : List A)
    (decoded : A → Nat → Nat → K) (publicValues : List K)
    (source : List Expr) (auxiliary : A → List (BusProgramFormula K))
    (auxiliaryLength : Nat) (auxiliaryShape : ∀ a∈earlier,(auxiliary a).length=auxiliaryLength)
    (residuals : A → List (AIRBusResidual K × Nat))
    (order : ∀ a∈earlier,(residuals a).map Prod.fst=source.map Sum.inl++(auxiliary a).map Sum.inr)
    (d n : Nat) (positive : 0<source.length+auxiliaryLength)
    (invalid : ∀ a∈earlier,¬∀ row,row<2^(n+1) → ∀ lane,
      (airCombinedRowResiduals (decodedTableTrace (n+1) (decoded a)) 0 publicValues source (auxiliary a) row).getD lane 0=0)
    (sourceDegrees : ∀ e∈source,e.degree≤d) (auxDegrees : ∀ a∈earlier,∀ e∈auxiliary a,busFormulaDegree e≤d)
    (sent : A → K → List K → List K → Poly K) (claim : A → K → List K → List K → K)
    (initialZero : ∀ a∈earlier,∀ mixing tau,claim a mixing tau []=0)
    (continuations : List R) (accept : A → LocalChallengePrefix K → R → Prop)
    (checks : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ r∈continuations,
      accept a p r → decodedLocalChecks d (sent a) (claim a) p)
    (repair pcsBudget : Nat) (errors : A → LocalChallengePrefix K → Nat)
    (wrongTerminal : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),
      ¬decodedLocalTerminalCorrect (n+1) (decoded a) publicValues (residuals a) (claim a) p →
      count continuations (accept a p)*sample.length≤repair+errors a p*sample.length)
    (jointErrors : (earlier.map (fun a => ((decodedLocalPrefixes sample (n+1)).map (errors a)).sum)).sum*
      sample.length≤pcsBudget) :
    count (earlier.flatMap (fun a => (decodedLocalPrefixes sample (n+1)).flatMap (fun p =>
      continuations.map (fun r => (a,p,r))))) (fun x => accept x.1 x.2.1 x.2.2)*sample.length≤
      earlier.length*
        (((source.length+auxiliaryLength-1+(n+1)+(d+1)*(n+1))*sample.length^(2*(n+1)+1))*continuations.length+
          (decodedLocalPrefixes sample (n+1)).length*repair)+pcsBudget := by
  classical
  have witnesses : ∀ a,∃ pair : Nat × Nat,a∈earlier → pair.1<2^(n+1) ∧
      (airCombinedRowResiduals (decodedTableTrace (n+1) (decoded a)) 0 publicValues source (auxiliary a) pair.1).getD pair.2 0≠0 := by
    intro a
    by_cases ha : a∈earlier
    · have existsWrong : ∃ row,row<2^(n+1) ∧ ∃ lane,
          (airCombinedRowResiduals (decodedTableTrace (n+1) (decoded a)) 0 publicValues source (auxiliary a) row).getD lane 0≠0 := by
        apply Classical.byContradiction
        intro absent
        apply invalid a ha
        intro row hr lane
        exact Classical.byContradiction (fun wrong=>absent ⟨row,hr,lane,wrong⟩)
      obtain ⟨row,hr,lane,wrong⟩ := existsWrong
      exact ⟨(row,lane),fun _=>⟨hr,wrong⟩⟩
    · exact ⟨(0,0),fun h=>False.elim (ha h)⟩
  let selected := fun a=>Classical.choose (witnesses a)
  exact decoded_adaptive_witness_after_earlier_budget sample distinct earlier decoded publicValues source auxiliary
    auxiliaryLength auxiliaryShape residuals order d n (fun a=>(selected a).1) (fun a=>(selected a).2)
    positive (fun a ha=>(Classical.choose_spec (witnesses a) ha).1)
    (fun a ha=>(Classical.choose_spec (witnesses a) ha).2)
    sourceDegrees auxDegrees sent claim initialZero continuations accept checks repair pcsBudget errors wrongTerminal jointErrors

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
