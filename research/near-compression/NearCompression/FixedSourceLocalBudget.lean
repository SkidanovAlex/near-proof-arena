import NearCompression.AdaptiveTableContinuation
import NearCompression.DecodedAdaptiveBus
namespace NearCompression
open Lean.Grind ZkFormal.Near ZkFormal.Udr ZkFormal.V2 ZkFormal.Air ZkFormal.Algebra ArenaCore.Security

/-- Restricting a trace to one decoded table preserves expression evaluation,
including selector values and cyclic next-row references. -/
theorem decoded_table_expression {K : Type} [Field K] (tr : Trace K)
    (t row : Nat) (pub : List K) (e : Expr) :
    e.eval (decodedTableTrace (tr.log t) (fun column row=>tr.cell t row column)) 0 row pub=
      e.eval tr t row pub := by
  unfold Expr.eval
  congr 1

/-- A failed source table selects a source-list index once. Every later
auxiliary attachment has a nonzero combined residual at that same index. -/
theorem fixed_source_invalid_residual_index {A : Type}
    (table : Table) (source : Trace Fp) (sourceWidth : Nat → Nat) (t n : Nat)
    (log : source.log t=n+1) (upper : source.log t≤table.maxLog)
    (pub : List Fp) (invalid : ¬TableLocal table source t pub)
    (bounds : ∀ e∈tableSourceResiduals table,e.colBound≤sourceWidth t)
    (earlier : List A) (decoded : A → Trace Fp8)
    (logs : ∀ a∈earlier,(decoded a).log=source.log)
    (fixed : ∀ a∈earlier,∀ s row column,column<sourceWidth s →
      (decoded a).cell s row column=Fp8.ofBase (source.cell s row column)) :
    ∃ row,row<2^(n+1) ∧ ∃ lane,lane<(tableSourceResiduals table).length ∧
      ∀ a∈earlier,∀ auxiliary : List (BusProgramFormula Fp8),
        (airCombinedRowResiduals
          (decodedTableTrace (n+1) (fun column row=>(decoded a).cell t row column)) 0
          (pub.map Fp8.ofBase) (tableSourceResiduals table) auxiliary row).getD lane 0≠0 := by
  obtain ⟨row,hr,e,he,wrong⟩ := table_local_failure_residual table source t pub (by omega) upper invalid
  obtain ⟨lane,hl,same⟩ := List.mem_iff_getElem.mp he
  refine ⟨row,?_,lane,hl,?_⟩
  · simpa only [Trace.height,log] using hr
  · intro a ha auxiliary
    have nonzero := fixed_source_decoded_nonzero source sourceWidth (decoded a) (logs a ha)
      (fixed a ha) t row pub e (bounds e he) wrong
    have localLog : (decoded a).log t=n+1 := by rw [logs a ha,log]
    have eq := decoded_table_expression (decoded a) t row (pub.map Fp8.ofBase) e
    rw [localLog] at eq
    rw [←eq] at nonzero
    simpa only [airCombinedRowResiduals,List.getD,List.getElem?_append,
      List.length_map,show ¬(tableSourceResiduals table).length≤lane by omega,
      hl,ite_true,ite_false,List.getElem?_map,List.getElem?_eq_getElem hl,Option.map_some,
      Option.getD_some,same] using nonzero

/-- Derive the adaptive local acceptance budget directly from a failed fixed
source table, without a supplied nonzero combined-residual index. -/
theorem fixed_source_invalid_local_budget {A R : Type}
    (sample : List Fp8) (distinct : sample.Nodup) (earlier : List A)
    (table : Table) (sourceTrace : Trace Fp) (sourceWidth : Nat → Nat) (t n : Nat)
    (log : sourceTrace.log t=n+1) (upper : sourceTrace.log t≤table.maxLog)
    (pub : List Fp) (invalid : ¬TableLocal table sourceTrace t pub)
    (bounds : ∀ e∈tableSourceResiduals table,e.colBound≤sourceWidth t)
    (traces : A → Trace Fp8)
    (logs : ∀ a∈earlier,(traces a).log=sourceTrace.log)
    (fixed : ∀ a∈earlier,∀ s row column,column<sourceWidth s →
      (traces a).cell s row column=Fp8.ofBase (sourceTrace.cell s row column)) (auxiliary : A → List (BusProgramFormula Fp8))
    (auxiliaryLength : Nat) (auxiliaryShape : ∀ a∈earlier,(auxiliary a).length=auxiliaryLength)
    (residuals : A → List (AIRBusResidual Fp8 × Nat))
    (order : ∀ a∈earlier,(residuals a).map Prod.fst=(tableSourceResiduals table).map Sum.inl++(auxiliary a).map Sum.inr)
    (d : Nat)
    (sourceDegrees : ∀ e∈tableSourceResiduals table,e.degree≤d) (auxDegrees : ∀ a∈earlier,∀ e∈auxiliary a,busFormulaDegree e≤d)
    (sent : A → Fp8 → List Fp8 → List Fp8 → Poly Fp8) (claim : A → Fp8 → List Fp8 → List Fp8 → Fp8)
    (initialZero : ∀ a∈earlier,∀ mixing tau,claim a mixing tau []=0)
    (continuations : List R) (accept : A → LocalChallengePrefix Fp8 → R → Prop)
    (checks : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ r∈continuations,
      accept a p r → decodedLocalChecks d (sent a) (claim a) p)
    (repair pcsBudget : Nat) (errors : A → LocalChallengePrefix Fp8 → Nat)
    (wrongTerminal : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),
      ¬decodedLocalTerminalCorrect (n+1) (fun column row=>(traces a).cell t row column) (pub.map Fp8.ofBase) (residuals a) (claim a) p →
      count continuations (accept a p)*sample.length≤repair+errors a p*sample.length)
    (jointErrors : (earlier.map (fun a => ((decodedLocalPrefixes sample (n+1)).map (errors a)).sum)).sum*
      sample.length≤pcsBudget) :
    count (earlier.flatMap (fun a => (decodedLocalPrefixes sample (n+1)).flatMap (fun p =>
      continuations.map (fun r => (a,p,r))))) (fun x => accept x.1 x.2.1 x.2.2)*sample.length≤
      earlier.length*
        ((((tableSourceResiduals table).length+auxiliaryLength-1+(n+1)+(d+1)*(n+1))*sample.length^(2*(n+1)+1))*continuations.length+
          (decodedLocalPrefixes sample (n+1)).length*repair)+pcsBudget := by
  obtain ⟨row,hr,lane,hl,nonzero⟩ := fixed_source_invalid_residual_index table sourceTrace sourceWidth t n
    log upper pub invalid bounds earlier traces logs fixed
  exact decoded_adaptive_table_after_earlier_budget sample distinct earlier
    (fun a column row=>(traces a).cell t row column) (pub.map Fp8.ofBase)
    (tableSourceResiduals table) auxiliary auxiliaryLength auxiliaryShape residuals order
    d n row lane (by omega) hr (fun a ha=>nonzero a ha (auxiliary a)) sourceDegrees auxDegrees
    sent claim initialZero continuations accept checks repair pcsBudget errors wrongTerminal jointErrors

end NearCompression
