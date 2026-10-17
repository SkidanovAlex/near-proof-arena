import NearCompression.BulkTable

/-! Exhaustive instruction simulation. The only remaining simulation premise is
for the prepared program's imported hosts. This is the existing D3 interpreter,
including rejection of float instructions, not full PV86 coverage. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem exec_equiv_of_imports (cfg : NearCfg) (p : Prepared) (imports : ImportsPreserveMaps p)
    (s t : St) (h : StateEquivalent s t) (f : Frame) (pf : PFunc) (i : Instr) :
    ResultEquivalent (exec cfg p s f pf i) (exec cfg p t f pf i) := by
  cases i <;> solve
    | (with_reducible apply stack_control_instruction_equiv cfg p s t h f pf; simp only [StackControlInstruction])
    | (with_reducible apply memory_table_instruction_equiv cfg p s t h f pf; simp only [MemoryTableInstruction])
    | (with_reducible apply bulk_table_instruction_equiv cfg p s t h f pf; simp only [BulkTableInstruction])
    | with_reducible exact exec_call_equiv cfg p imports s t h f pf _
    | with_reducible exact exec_call_indirect_equiv cfg p imports s t h f pf _ _
    | with_reducible exact exec_numeric_instruction_equiv cfg p s t h f pf _
    | with_reducible exact load_instruction_equiv cfg p s t h f pf _ _ _
    | with_reducible exact store_instruction_equiv cfg p s t h f pf _ _ _
    | with_reducible exact table_init_instruction_equiv cfg p s t h f pf _ _
    | (with_reducible apply bulk_memory_instruction_equiv cfg p s t h f pf; exact Or.inl rfl)
    | (with_reducible apply bulk_memory_instruction_equiv cfg p s t h f pf; exact Or.inr (Or.inl rfl))
    | (with_reducible apply bulk_memory_instruction_equiv cfg p s t h f pf; exact Or.inr (Or.inr ⟨_, rfl⟩))

theorem step_preserves_maps_of_imports (cfg : NearCfg) (p : Prepared)
    (imports : ImportsPreserveMaps p) : StepPreservesMaps cfg p :=
  step_equiv_of_exec cfg p (exec_equiv_of_imports cfg p imports)

end NearCompression
