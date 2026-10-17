import NearCompression.DecodedAdaptiveBus
import NearCompression.AdaptiveTableContinuation
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra

/-- Source validity and zero generated auxiliary formulas reconstruct the
recursive bus residual predicate, with exact table offsets. -/
theorem bus_ext8_tables_from_generated_residuals
    (tables : List Table) (raw : Trace Fp) (sourceWidth : Nat → Nat)
    (pub : List Fp) (alpha gamma : Fp8) (finals : Nat → Nat → Fp8) (start : Nat)
    (source : ∀ j,∀ hj : j<tables.length,
      (∀ e∈tables[j].allConstraints,e.colBound≤sourceWidth (start+j)) ∧
      (∀ i∈tables[j].interactions,∀ e∈i.exprs,e.colBound≤sourceWidth (start+j)) ∧
      (∀ row,row<raw.height (start+j) → ∀ e∈tables[j].allConstraints,e.eval raw (start+j) row pub=0))
    (auxiliary : ∀ j,∀ hj : j<tables.length,∀ row,row<raw.height (start+j) →
      ∀ e∈busTableResiduals (tables[j].interactions.map (lowerBusInteraction (pub.map Fp8.ofBase) alpha gamma))
        tables[j].width (finals (start+j)),
      busProgramFormulaValue (busRowProgramEnv (airAuxCoordinateTrace raw sourceWidth) (start+j) row) e=0) :
    busExt8TablesResidualsZero raw sourceWidth pub alpha gamma finals tables start := by
  induction tables generalizing start with
  | nil => trivial
  | cons table rest ih =>
    have head := source 0 (by simp)
    have aux := auxiliary 0 (by simp)
    simp only [Nat.add_zero,List.getElem_cons_zero] at head aux
    refine ⟨head.1,head.2.1,head.2.2,aux,?_⟩
    apply ih (start+1)
    · intro j hj
      have h := source (Nat.succ j) (by simp;omega)
      simp only [List.getElem_cons_succ] at h
      simpa only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm 1 j] using h
    · intro j hj
      have h := auxiliary (Nat.succ j) (by simp;omega)
      simp only [List.getElem_cons_succ] at h
      simpa only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm 1 j] using h

/-- Once source checks hold, failure of bus residual validity identifies an
actual generated auxiliary formula, not an arbitrary assumed bad lane. -/
theorem bus_ext8_generated_residual_failure
    (tables : List Table) (raw : Trace Fp) (sourceWidth : Nat → Nat)
    (pub : List Fp) (alpha gamma : Fp8) (finals : Nat → Nat → Fp8) (start : Nat)
    (source : ∀ j,∀ hj : j<tables.length,
      (∀ e∈tables[j].allConstraints,e.colBound≤sourceWidth (start+j)) ∧
      (∀ i∈tables[j].interactions,∀ e∈i.exprs,e.colBound≤sourceWidth (start+j)) ∧
      (∀ row,row<raw.height (start+j) → ∀ e∈tables[j].allConstraints,e.eval raw (start+j) row pub=0))
    (invalid : ¬busExt8TablesResidualsZero raw sourceWidth pub alpha gamma finals tables start) :
    ∃ j,∃ hj : j<tables.length,∃ row,row<raw.height (start+j) ∧
      ∃ e∈busTableResiduals (tables[j].interactions.map (lowerBusInteraction (pub.map Fp8.ofBase) alpha gamma))
        tables[j].width (finals (start+j)),
      busProgramFormulaValue (busRowProgramEnv (airAuxCoordinateTrace raw sourceWidth) (start+j) row) e≠0 := by
  classical
  apply Classical.byContradiction
  intro absent
  apply invalid
  apply bus_ext8_tables_from_generated_residuals tables raw sourceWidth pub alpha gamma finals start source
  intro j hj row hr e he
  exact Classical.byContradiction (fun wrong=>absent ⟨j,hj,row,hr,e,he,wrong⟩)

/-- The generated auxiliary violation survives appending it after any source
residual list in the combined local sumcheck polynomial. -/
theorem auxiliary_nonzero_combined_index {K : Type} [Field K]
    (tr : Trace K) (t row : Nat) (pub : List K) (source : List Expr)
    (auxiliary : List (BusProgramFormula K)) (e : BusProgramFormula K) (member : e∈auxiliary)
    (wrong : busProgramFormulaValue (busRowProgramEnv tr t row) e≠0) :
    0<source.length+auxiliary.length ∧ ∃ lane,
      (airCombinedRowResiduals tr t pub source auxiliary row).getD lane 0≠0 := by
  have valueMember : busProgramFormulaValue (busRowProgramEnv tr t row) e∈
      airCombinedRowResiduals tr t pub source auxiliary row :=
    List.mem_append_right _ (List.mem_map.mpr ⟨e,member,rfl⟩)
  obtain ⟨lane,hl,same⟩ := List.mem_iff_getElem.mp valueMember
  have size : (airCombinedRowResiduals tr t pub source auxiliary row).length=source.length+auxiliary.length := by
    simp only [airCombinedRowResiduals,List.length_append,List.length_map]
  refine ⟨by omega,lane,?_⟩
  simpa only [List.getD,List.getElem?_eq_getElem hl,Option.getD_some,same] using wrong

end NearCompression
