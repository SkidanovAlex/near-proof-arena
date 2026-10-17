import NearCompression.PreparedLiteralBusSoundness
import NearCompression.AirCombinedResidualRows
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ZkFormal.V2 ZkFormal.Udr NearSpecV3.Wasm

/-- Source constraints in the same order as the native constraints(table):
explicit table constraints, then every interaction multiplicity bit check. -/
def tableSourceResiduals (table : Table) : List Expr :=
  table.constraints++table.interactions.flatMap (fun interaction =>
    interaction.mult.map (fun bit => Expr.mul bit (Expr.add bit (Expr.neg (Expr.const 1)))))

/-- Log geometry and zero source residuals imply actual TableLocal, including
boolean multiplicities. This theorem is about base-field execution traces. -/
theorem table_source_residuals_local (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (lower : 1≤tr.log t) (upper : tr.log t≤table.maxLog)
    (zero : ∀ r,r<tr.height t → ∀ e∈tableSourceResiduals table,e.eval tr t r pub=0) :
    TableLocal table tr t pub := by
  refine ⟨lower,upper,?_,?_⟩
  · intro r hr e he
    exact zero r hr e (List.mem_append_left _ he)
  · intro r hr interaction hi bit hb
    have member : Expr.mul bit (Expr.add bit (Expr.neg (Expr.const 1)))∈tableSourceResiduals table := by
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨interaction,hi,List.mem_map.mpr ⟨bit,hb,rfl⟩⟩
    have h := zero r hr _ member
    change bit.eval tr t r pub*(bit.eval tr t r pub + -1)=0 at h
    grind

/-- Failure of local validity at valid row geometry supplies one concrete
nonzero source residual, before any local challenge is sampled. -/
theorem table_local_failure_residual (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (lower : 1≤tr.log t) (upper : tr.log t≤table.maxLog)
    (invalid : ¬TableLocal table tr t pub) :
    ∃ row,row<tr.height t ∧ ∃ e∈tableSourceResiduals table,e.eval tr t row pub≠0 := by
  classical
  by_cases witness : ∃ row,row<tr.height t ∧ ∃ e∈tableSourceResiduals table,e.eval tr t row pub≠0
  · exact witness
  · apply False.elim
    apply invalid
    apply table_source_residuals_local table tr t pub lower upper
    intro row hr e he
    by_cases zero : e.eval tr t row pub=0
    · exact zero
    · exact False.elim (witness ⟨row,hr,e,he,zero⟩)

/-- The source witness is an indexed coefficient in the exact combined
source/auxiliary list used by the local soundness theorem. Auxiliary values
cannot erase it because their residuals are appended after source residuals. -/
theorem table_local_failure_combined_residual (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (auxiliary : List (BusProgramFormula Fp))
    (lower : 1≤tr.log t) (upper : tr.log t≤table.maxLog)
    (invalid : ¬TableLocal table tr t pub) :
    0<(tableSourceResiduals table).length+auxiliary.length ∧
      ∃ row,row<tr.height t ∧ ∃ lane,
        (airCombinedRowResiduals tr t pub (tableSourceResiduals table) auxiliary row).getD lane 0≠0 := by
  obtain ⟨row,hr,e,he,wrong⟩ := table_local_failure_residual table tr t pub lower upper invalid
  have member : e.eval tr t row pub∈airCombinedRowResiduals tr t pub (tableSourceResiduals table) auxiliary row :=
    List.mem_append_left _ (List.mem_map.mpr ⟨e,he,rfl⟩)
  obtain ⟨lane,hl,same⟩ := List.mem_iff_getElem.mp member
  have length : (airCombinedRowResiduals tr t pub (tableSourceResiduals table) auxiliary row).length=
      (tableSourceResiduals table).length+auxiliary.length := by
    simp [airCombinedRowResiduals]
  refine ⟨by omega,row,hr,lane,?_⟩
  simpa only [List.getD,List.getElem?_eq_getElem hl,Option.getD_some,same] using wrong

/-- A wrong published Wasm outcome has either a fixed nonzero local source
residual or a bus imbalance, assuming prepared execution and row geometry.
The alternative is chosen from the base trace before challenge sampling. -/
theorem prepared_wrong_output_residual_or_bus (codeCount : Nat) (tr : Trace Fp) (pub : List Fp)
    (logs : ∀ t (ht : t<(preparedLiteralAir codeCount).tables.length),
      1≤tr.log t ∧ tr.log t≤(preparedLiteralAir codeCount).tables[t].maxLog)
    (fits : pubFit (preparedLiteralAir codeCount) pub=true)
    (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (blockLevel full : Bool) (eligible : PreparedRunCallEligible)
    (accepted : preparedLiteralRunCallCheck cfg code method ctx pub blockLevel=some eligible)
    (fuel : Nat) (enoughFuel : tr.height 0≤fuel)
    (wrong : ¬∃ final error,runCall cfg code method ctx fuel blockLevel full none=.done final error ∧
      PreparedExecPublishedOutput pub final error) :
    (∃ t,∃ ht : t<(preparedLiteralAir codeCount).tables.length,
      ∃ row,row<tr.height t ∧ ∃ e∈tableSourceResiduals (preparedLiteralAir codeCount).tables[t],
        e.eval tr t row pub≠0) ∨
    (¬∀ b m,busCount (preparedLiteralAir codeCount).toAir tr pub b true m+
      pubCount (preparedLiteralAir codeCount) pub b true m=
      busCount (preparedLiteralAir codeCount).toAir tr pub b false m+pubCount (preparedLiteralAir codeCount) pub b false m) := by
  classical
  by_cases locals : ∀ t (ht : t<(preparedLiteralAir codeCount).tables.length),
      TableLocal (preparedLiteralAir codeCount).tables[t] tr t pub
  · apply Or.inr
    intro balance
    have holds : HoldsP (preparedLiteralAir codeCount) pub tr := {
      logBound:=fun t ht=>logs t ht
      constr:=fun t ht=>(locals t ht).constr
      bits:=fun t ht=>(locals t ht).bits
      pubFit:=fits
      balance:=balance}
    obtain ⟨w,actual,published⟩ := prepared_literal_public_run_call codeCount tr pub holds cfg code method ctx
      blockLevel full eligible accepted fuel enoughFuel
    exact wrong ⟨w.final,w.error,actual,published⟩
  · apply Or.inl
    by_cases witness : ∃ t,∃ ht : t<(preparedLiteralAir codeCount).tables.length,
        ¬TableLocal (preparedLiteralAir codeCount).tables[t] tr t pub
    · obtain ⟨t,ht,invalid⟩ := witness
      obtain ⟨row,hr,e,he,nonzero⟩ := table_local_failure_residual _ tr t pub (logs t ht).1 (logs t ht).2 invalid
      exact ⟨t,ht,row,hr,e,he,nonzero⟩
    · exact False.elim (locals (fun t ht => Classical.byContradiction (fun h => witness ⟨t,ht,h⟩)))

end NearCompression
