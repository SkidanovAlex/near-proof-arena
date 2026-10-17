import NearCompression.CheckedBusResidualTransport
import NearCompression.FixedSourceLocalBudget
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra

/-- Selecting one table preserves the entire ordered local residual vector,
including cyclic next-row reads and boundary selectors. -/
theorem decoded_table_combined_residuals {K : Type} [Field K] (tr : Trace K)
    (t row : Nat) (pub : List K) (source : List Expr)
    (auxiliary : List (BusProgramFormula K)) :
    airCombinedRowResiduals
      (decodedTableTrace (tr.log t) (fun column row=>tr.cell t row column)) 0
      pub source auxiliary row = airCombinedRowResiduals tr t pub source auxiliary row := by
  unfold airCombinedRowResiduals
  have expressions : source.map (fun e=>e.eval
      (decodedTableTrace (tr.log t) (fun column row=>tr.cell t row column)) 0 row pub)=
      source.map (fun e=>e.eval tr t row pub) := by
    apply List.map_congr_left
    intro e _
    exact decoded_table_expression tr t row pub e
  rw [expressions]
  rfl

/-- Invalid bus auxiliaries select a genuine table, bounded row and nonzero
lane in the checked local list. A chronological application must fix these
inputs before local challenges; source validity alone does not imply auxiliary validity. -/
theorem checked_bus_invalid_table_witness (tables : List Table) (tr : Trace Fp8)
    (sourceWidth : Nat → Nat) (pub : List Fp) (alpha gamma : Fp8)
    (finals : Nat → Nat → Fp8) (formulas : Nat → List (BusProgramFormula Fp8)) (start : Nat)
    (widths : ∀ j,∀ hj : j<tables.length,tables[j].width=sourceWidth (start+j))
    (source : ∀ j,∀ hj : j<tables.length,
      (∀ e∈tables[j].allConstraints,e.colBound≤sourceWidth (start+j)) ∧
      (∀ i∈tables[j].interactions,∀ e∈i.exprs,e.colBound≤sourceWidth (start+j)) ∧
      (∀ row,row<tr.height (start+j) → ∀ e∈tables[j].allConstraints,
        e.eval (decodedBaseTrace tr) (start+j) row pub=0))
    (checked : ∀ j,∀ hj : j<tables.length,
      generatedExt8BusSpecCheck
        (tables[j].interactions.map (lowerBusInteraction (pub.map Fp8.ofBase) alpha gamma))
        (sourceWidth (start+j)) (finals (start+j)) (formulas (start+j))=true)
    (base : ∀ j,∀ hj : j<tables.length,∀ e∈formulas (start+j),∀ row c,
      c<busFormulaColumnBound e → Fp8.IsBase (tr.cell (start+j) row c))
    (invalid : ¬busExt8TablesResidualsZero (decodedBaseTrace tr) sourceWidth pub alpha gamma finals tables start) :
    ∃ j,∃ hj : j<tables.length,
      0<(tableSourceResiduals tables[j]).length+(formulas (start+j)).length ∧
      ∃ row,row<2^(tr.log (start+j)) ∧ ∃ lane,
        (airCombinedRowResiduals
          (decodedTableTrace (tr.log (start+j)) (fun column row=>tr.cell (start+j) row column)) 0
          (pub.map Fp8.ofBase) (tableSourceResiduals tables[j]) (formulas (start+j)) row).getD lane 0≠0 := by
  obtain ⟨j,hj,row,hr,e,he,wrong⟩ := bus_ext8_generated_residual_failure
    tables (decodedBaseTrace tr) sourceWidth pub alpha gamma finals start source invalid
  rw [widths j hj] at he
  obtain ⟨positive,lane,nonzero⟩ := checked_bus_failure_combined_index tr sourceWidth (start+j) row
    (pub.map Fp8.ofBase) (tableSourceResiduals tables[j])
    (tables[j].interactions.map (lowerBusInteraction (pub.map Fp8.ofBase) alpha gamma))
    (finals (start+j)) (formulas (start+j)) (checked j hj) (base j hj) e he wrong
  refine ⟨j,hj,positive,row,hr,lane,?_⟩
  rw [decoded_table_combined_residuals]
  exact nonzero

end NearCompression
