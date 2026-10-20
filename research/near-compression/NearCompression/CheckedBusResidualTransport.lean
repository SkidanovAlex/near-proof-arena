import NearCompression.GeneratedExt8BusSpecCheck
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra

/-- Accepted native-style formula lists have the exact reconstructed bus
row values, provided their referenced PCS coordinate cells descend to Fp. -/
theorem checked_bus_decoded_row_values (tr : Trace Fp8) (sourceWidth : Nat → Nat)
    (t row : Nat) (interactions : List (BusFormulaInteraction Fp8)) (finals : Nat → Fp8)
    (formulas : List (BusProgramFormula Fp8))
    (checked : generatedExt8BusSpecCheck interactions (sourceWidth t) finals formulas=true)
    (base : ∀ e∈formulas,∀ r c,c<busFormulaColumnBound e → Fp8.IsBase (tr.cell t r c)) :
    formulas.map (busProgramFormulaValue (busRowProgramEnv tr t row))=
      (busTableResiduals interactions (sourceWidth t) finals).map
        (busProgramFormulaValue (busRowProgramEnv (airAuxCoordinateTrace (decodedBaseTrace tr) sourceWidth) t row)) := by
  have projected : formulas.map (busProgramFormulaValue (busRowProgramEnv tr t row))=
      formulas.map (busProgramFormulaValue (busRowProgramEnv (airExt8Trace (decodedBaseTrace tr)) t row)) := by
    apply List.map_congr_left
    intro e he
    exact bus_formula_bounded_base_projection tr t row e (base e he)
  rw [projected,generated_ext8_bus_spec_checked interactions (sourceWidth t) finals formulas checked,
    bus_coordinate_row_environment]

/-- A violation of the formal bus model survives in the checked certificate's
combined local residual list. Exact specification checking supplies list
coverage/order; no separately assumed formula-list identity is used. -/
theorem checked_bus_failure_combined_index (tr : Trace Fp8) (sourceWidth : Nat → Nat)
    (t row : Nat) (pub : List Fp8) (source : List Expr)
    (interactions : List (BusFormulaInteraction Fp8)) (finals : Nat → Fp8)
    (formulas : List (BusProgramFormula Fp8))
    (checked : generatedExt8BusSpecCheck interactions (sourceWidth t) finals formulas=true)
    (base : ∀ e∈formulas,∀ r c,c<busFormulaColumnBound e → Fp8.IsBase (tr.cell t r c))
    (e : BusProgramFormula Fp8) (member : e∈busTableResiduals interactions (sourceWidth t) finals)
    (wrong : busProgramFormulaValue
      (busRowProgramEnv (airAuxCoordinateTrace (decodedBaseTrace tr) sourceWidth) t row) e≠0) :
    0<source.length+formulas.length ∧ ∃ lane,
      (airCombinedRowResiduals tr t pub source formulas row).getD lane 0≠0 := by
  have values := checked_bus_decoded_row_values tr sourceWidth t row interactions finals formulas checked base
  have present : busProgramFormulaValue
      (busRowProgramEnv (airAuxCoordinateTrace (decodedBaseTrace tr) sourceWidth) t row) e∈
      formulas.map (busProgramFormulaValue (busRowProgramEnv tr t row)) := by
    rw [values]
    exact List.mem_map.mpr ⟨e,member,rfl⟩
  obtain ⟨actual,ha,same⟩ := List.mem_map.mp present
  apply auxiliary_nonzero_combined_index tr t row pub source formulas actual ha
  rw [same]
  exact wrong

/-- Zero checked auxiliary residuals discharge the auxiliary part of the
bus predicate, on precisely the reconstructed decoded coordinate trace. -/
theorem checked_bus_rows_zero (tr : Trace Fp8) (sourceWidth : Nat → Nat)
    (t : Nat) (interactions : List (BusFormulaInteraction Fp8)) (finals : Nat → Fp8)
    (formulas : List (BusProgramFormula Fp8))
    (checked : generatedExt8BusSpecCheck interactions (sourceWidth t) finals formulas=true)
    (base : ∀ e∈formulas,∀ r c,c<busFormulaColumnBound e → Fp8.IsBase (tr.cell t r c))
    (zero : ∀ row,row<tr.height t → ∀ e∈formulas,busProgramFormulaValue (busRowProgramEnv tr t row) e=0) :
    ∀ row,row<tr.height t → ∀ e∈busTableResiduals interactions (sourceWidth t) finals,
      busProgramFormulaValue
        (busRowProgramEnv (airAuxCoordinateTrace (decodedBaseTrace tr) sourceWidth) t row) e=0 := by
  intro row hr e he
  have values := checked_bus_decoded_row_values tr sourceWidth t row interactions finals formulas checked base
  have present : busProgramFormulaValue
      (busRowProgramEnv (airAuxCoordinateTrace (decodedBaseTrace tr) sourceWidth) t row) e∈
      formulas.map (busProgramFormulaValue (busRowProgramEnv tr t row)) := by
    rw [values]
    exact List.mem_map.mpr ⟨e,he,rfl⟩
  obtain ⟨actual,ha,same⟩ := List.mem_map.mp present
  rw [←same]
  exact zero row hr actual ha

/-- All checked table residuals reconstruct the exact bus validity predicate
used by the fixed-source bus acceptance theorem. Source constraints and
interaction bounds remain separate from auxiliary validity. -/
theorem checked_bus_tables_residuals_zero (tables : List Table) (tr : Trace Fp8)
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
    (zero : ∀ j,∀ hj : j<tables.length,∀ row,row<tr.height (start+j) → ∀ e∈formulas (start+j),
      busProgramFormulaValue (busRowProgramEnv tr (start+j) row) e=0) :
    busExt8TablesResidualsZero (decodedBaseTrace tr) sourceWidth pub alpha gamma finals tables start := by
  apply bus_ext8_tables_from_generated_residuals tables (decodedBaseTrace tr) sourceWidth pub alpha gamma finals start source
  intro j hj row hr e he
  rw [widths j hj] at he
  exact checked_bus_rows_zero tr sourceWidth (start+j)
    (tables[j].interactions.map (lowerBusInteraction (pub.map Fp8.ofBase) alpha gamma))
    (finals (start+j)) (formulas (start+j)) (checked j hj) (base j hj) (zero j hj) row hr e he

end NearCompression
