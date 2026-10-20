import NearCompression.HistoryFixedCoordinates
import NearCompression.CheckedBusFailureSelection
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra

/-- Validity of the actual checked auxiliary formula list on all live rows. -/
def checkedAuxiliaryRowsZero (tr : Trace Fp8) (t : Nat)
    (formulas : List (BusProgramFormula Fp8)) : Prop :=
  ∀ row,row<tr.height t → ∀ e∈formulas,busProgramFormulaValue (busRowProgramEnv tr t row) e=0

/-- Analytical selector on the earlier fixed trace, not an executable prover
operation. Prefer the first invalid table; none means both tables are valid. -/
noncomputable def twoTableAuxiliaryBranch (tr : Trace Fp8)
    (formulas : Nat → List (BusProgramFormula Fp8)) (start : Nat) : Option Bool := by
  classical
  exact if checkedAuxiliaryRowsZero tr start (formulas start) then
    if checkedAuxiliaryRowsZero tr (start+1) (formulas (start+1)) then none else some true
    else some false

theorem two_table_auxiliary_none (tr : Trace Fp8)
    (formulas : Nat → List (BusProgramFormula Fp8)) (start : Nat) :
    twoTableAuxiliaryBranch tr formulas start=none ↔
      checkedAuxiliaryRowsZero tr start (formulas start) ∧
      checkedAuxiliaryRowsZero tr (start+1) (formulas (start+1)) := by
  classical
  unfold twoTableAuxiliaryBranch
  by_cases first : checkedAuxiliaryRowsZero tr start (formulas start) <;>
    by_cases second : checkedAuxiliaryRowsZero tr (start+1) (formulas (start+1)) <;> simp [first,second]

theorem two_table_auxiliary_selected_invalid (tr : Trace Fp8)
    (formulas : Nat → List (BusProgramFormula Fp8)) (start : Nat) (b : Bool)
    (selected : twoTableAuxiliaryBranch tr formulas start=some b) :
    ¬checkedAuxiliaryRowsZero tr (start+(if b then 1 else 0))
      (formulas (start+(if b then 1 else 0))) := by
  classical
  unfold twoTableAuxiliaryBranch at selected
  by_cases first : checkedAuxiliaryRowsZero tr start (formulas start)
  · simp only [first,ite_true] at selected
    by_cases second : checkedAuxiliaryRowsZero tr (start+1) (formulas (start+1))
    · simp [second] at selected
    · simp only [second,ite_false,Option.some.injEq] at selected
      subst b
      exact second
  · simp only [first,ite_false,Option.some.injEq] at selected
    subst b
    simpa using first

/-- A selected invalid table in the earlier fixed trace stays invalid in
all decoded continuations with the same covered coordinates. -/
theorem selected_auxiliary_decoded_witness (fixed : Trace Fp) (decoded : Trace Fp8)
    (width : Nat → Nat) (logs : decoded.log=fixed.log)
    (cells : ∀ t row column,column<width t →
      decoded.cell t row column=Fp8.ofBase (fixed.cell t row column))
    (formulas : Nat → List (BusProgramFormula Fp8)) (start : Nat) (b : Bool)
    (selected : twoTableAuxiliaryBranch (airExt8Trace fixed) formulas start=some b)
    (bounds : ∀ e∈formulas (start+(if b then 1 else 0)),
      busFormulaColumnBound e≤width (start+(if b then 1 else 0)))
    (pub : List Fp8) (source : List Expr) :
    let t := start+(if b then 1 else 0)
    0<source.length+(formulas t).length ∧ ∃ row,row<2^(decoded.log t) ∧ ∃ lane,
      (airCombinedRowResiduals
        (decodedTableTrace (decoded.log t) (fun column row=>decoded.cell t row column)) 0
        pub source (formulas t) row).getD lane 0≠0 := by
  classical
  intro t
  have invalid := two_table_auxiliary_selected_invalid (airExt8Trace fixed) formulas start b selected
  have witness : ∃ row,row<(airExt8Trace fixed).height t ∧ ∃ e∈formulas t,
      busProgramFormulaValue (busRowProgramEnv (airExt8Trace fixed) t row) e≠0 := by
    apply Classical.byContradiction
    intro absent
    apply invalid
    intro row hr e he
    exact Classical.byContradiction (fun wrong=>absent ⟨row,hr,e,he,wrong⟩)
  obtain ⟨row,hr,e,he,wrong⟩ := witness
  have transported : busProgramFormulaValue (busRowProgramEnv decoded t row) e≠0 := by
    rw [fixed_coordinate_bus_formula fixed decoded width logs cells t row e (bounds e he)]
    exact wrong
  obtain ⟨positive,lane,nonzero⟩ := auxiliary_nonzero_combined_index decoded t row pub source (formulas t) e he transported
  refine ⟨positive,row,?_,lane,?_⟩
  · simpa only [Trace.height,airExt8Trace,logs] using hr
  · rw [decoded_table_combined_residuals]
    exact nonzero

/-- The unselected branch supplies bus residual validity for every covered
decoded continuation, using exact specification checks and source checks. -/
theorem unselected_auxiliary_decoded_bus_validity (tables : List Table) (two : tables.length=2)
    (fixed : Trace Fp) (tr : Trace Fp8) (coordinateWidth : Nat → Nat)
    (logs : tr.log=fixed.log)
    (cells : ∀ t row column,column<coordinateWidth t →
      tr.cell t row column=Fp8.ofBase (fixed.cell t row column))
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
    (bounds : ∀ j,∀ hj : j<tables.length,∀ e∈formulas (start+j),
      busFormulaColumnBound e≤coordinateWidth (start+j))
    (selected : twoTableAuxiliaryBranch (airExt8Trace fixed) formulas start=none) :
    busExt8TablesResidualsZero (decodedBaseTrace tr) sourceWidth pub alpha gamma finals tables start := by
  have valid := (two_table_auxiliary_none (airExt8Trace fixed) formulas start).mp selected
  apply checked_bus_tables_residuals_zero tables tr sourceWidth pub alpha gamma finals formulas start
    widths source checked
  · intro j hj e he row c hc
    rw [cells (start+j) row c (Nat.lt_of_lt_of_le hc (bounds j hj e he))]
    exact (Fp8.isBase_iff _).mpr ⟨fixed.cell (start+j) row c,rfl⟩
  · intro j hj row hr e he
    rw [fixed_coordinate_bus_formula fixed tr coordinateWidth logs cells (start+j) row e (bounds j hj e he)]
    have height : row<(airExt8Trace fixed).height (start+j) := by
      simpa only [Trace.height,airExt8Trace,logs] using hr
    have cases : j=0 ∨ j=1 := by omega
    rcases cases with h | h
    · subst j
      exact valid.1 row height e he
    · subst j
      exact valid.2 row height e he

end NearCompression
