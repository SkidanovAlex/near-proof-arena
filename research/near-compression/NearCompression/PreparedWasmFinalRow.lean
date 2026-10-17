import NearCompression.PreparedDonePadding

namespace NearCompression
open ZkFormal.Algebra ZkFormal.Air NearSpecV3.Wasm

/-- Semantic terminal snapshot: the output PC is retained diagnostic metadata;
the interpreter has no live frame after successful final return. -/
def PreparedWasmFinalRow (row : Nat → Fp) (pub : List Fp) (final : St) (error : Option String) : Prop :=
  row 25=1 ∧ row 26=(if error.isSome then 1 else 0) ∧ final.gas.g=preparedGasValue row pub ∧
  ∃ sp,sp<9 ∧ (∀ i,i<9 → row (16+i)=if i=sp then 1 else 0) ∧ final.stack=preparedWasmStack row sp

theorem prepared_final_row_padding (row next : Nat → Fp) (pub : List Fp) (final : St) (error : Option String)
    (binding : PreparedWasmFinalRow row pub final error) (same : PreparedSnapshotEq row next pub) :
    PreparedWasmFinalRow next pub final error := by
  rcases binding with ⟨done,fail,gas,sp,bound,selected,stack⟩
  refine ⟨same.1.trans done,same.2.1.trans fail,gas.trans same.2.2.1.symm,sp,bound,?_,?_⟩
  · intro i hi;rw [same.2.2.2.2.1 i hi];exact selected i hi
  · rw [prepared_wasm_stack_congr row next sp (fun i hi=>same.2.2.2.2.2 i (by omega))]
    exact stack

theorem prepared_end_final_row (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (air : PreparedWasmAir table tr t pub) (p : Prepared) (r : Nat) (s : St)
    (c : PreparedWasmEnd p tr t r pub s) :
    PreparedWasmFinalRow (tr.cell t (r+1)) pub c.final none := by
  have terminal:=prepared_table_end table air.source.terminal air.source.prefixPart air.source.middle
    air.source.dead air.source.transition air.source.endDepth tr t r pub air.localH c.nonlast c.active
    air.fees c.publicEnd c.enough
  have selected:=c.location.state.2.2.2.1
  have currentZero : c.location.sp=0 := by
    have h:=selected 0 (by decide)
    simp only [Nat.add_zero,terminal.1] at h
    by_cases eq:0=c.location.sp
    · exact eq.symm
    · simp only [eq,ite_false] at h
      exact False.elim ((by decide : (1:Fp)≠0) h)
  refine ⟨terminal.2.1,terminal.2.2.1,rfl,0,by decide,?_,rfl⟩
  intro i hi
  rw [terminal.2.2.2.2.2.1 i hi]
  simpa only [currentZero] using selected i hi

theorem prepared_failure_gas_fast (s : St) (amount : Nat) :
    (preparedWasmFailureGas s amount).g=s.gas.g := by
  unfold preparedWasmFailureGas
  dsimp only
  split <;> rfl

theorem prepared_exhausted_final_row (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (air : PreparedWasmAir table tr t pub) (p : Prepared) (r : Nat) (s : St)
    (c : PreparedWasmExhausted p tr t r pub s) :
    PreparedWasmFinalRow (tr.cell t (r+1)) pub c.final (some c.error) := by
  have terminal:=prepared_table_exhaustion_projection table air.source.terminal air.source.prefixPart air.source.middle
    air.source.dead air.source.transition tr t r pub air.localH c.nonlast c.active air.fees c.exhausted
  rcases c.location.state with ⟨_,spBound,_,selected,_,_,stack,gas⟩
  unfold PreparedWasmFinalRow PreparedWasmExhausted.final
  dsimp only
  refine ⟨terminal.1,terminal.2.1,?_,c.location.sp,spBound,?_,?_⟩
  · change (preparedWasmFailureGas s _).g=_
    rw [prepared_failure_gas_fast,gas]
    exact terminal.2.2.1.symm
  · intro i hi
    rw [terminal.2.2.2.2.1 i hi]
    exact selected i hi
  · change s.stack=_
    rw [prepared_wasm_stack_congr (tr.cell t r) (tr.cell t (r+1)) c.location.sp (by
      intro i hi;exact terminal.2.2.2.2.2 i (by omega))]
    exact stack

/-- Every source-constructed execution ends at the actual next terminal row;
the relation is proved for every concrete constructor of the certificate. -/
theorem prepared_execution_final_row (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (air : PreparedWasmAir table tr t pub) (p : Prepared)
    {r n : Nat} {s final : St} {error : Option String}
    (execution : PreparedWasmExecution p tr t pub r s n final error) :
    r+n<tr.height t ∧ PreparedWasmFinalRow (tr.cell t (r+n)) pub final error := by
  induction execution with
  | finish c => exact ⟨c.nonlast,prepared_end_final_row table tr t pub air p _ _ c⟩
  | fail c => exact ⟨c.nonlast,prepared_exhausted_final_row table tr t pub air p _ _ c⟩
  | advance c tail ih =>
    simpa only [Nat.add_assoc,Nat.add_comm 1] using ih

theorem prepared_execution_last_row (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (air : PreparedWasmAir table tr t pub) (p : Prepared)
    {r n : Nat} {s final : St} {error : Option String}
    (execution : PreparedWasmExecution p tr t pub r s n final error) :
    PreparedWasmFinalRow (tr.cell t (tr.height t-1)) pub final error := by
  have terminal:=prepared_execution_final_row table tr t pub air p execution
  have frozen:=prepared_done_padding_suffix table tr t (r+n) pub air terminal.2.1
    (tr.height t-1-(r+n)) (by omega)
  have index : r+n+(tr.height t-1-(r+n))=tr.height t-1 := by omega
  rw [index] at frozen
  exact prepared_final_row_padding _ _ pub final error terminal.2 frozen

end NearCompression
