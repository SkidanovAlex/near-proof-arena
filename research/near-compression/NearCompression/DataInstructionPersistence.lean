import NearCompression.NumericPersistence

/-! Stack/control and direct memory/table instruction backend persistence. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem stack_control_instruction_keeps_backend (cfg : NearCfg) (p : Prepared)
    (s : St) (f : Frame) (pf : PFunc)
    (i : Instr) (covered : StackControlInstruction i) :
    ResultKeepsBackend s (exec cfg p s f pf i) := by
  cases i <;> simp only [StackControlInstruction] at covered
  all_goals simp only [exec, pop_n_stack_form, pop_ref_stack_form, popV, pushI32, pushV]
  all_goals repeat' (split <;> (try simp_all only []))
  all_goals first
    | rfl
    | trivial
    | exact return_keeps_backend p s
    | exact branch_keeps_backend p s _ _
    | (change (setFrame _ _).real.isSome = s.real.isSome; rw [set_frame_real])
    | (apply result_keeps_backend_change_start s _ _ rfl; exact branch_keeps_backend p _ _ _)

theorem memory_table_instruction_keeps_backend (cfg : NearCfg) (p : Prepared)
    (s : St) (f : Frame) (pf : PFunc)
    (i : Instr) (covered : MemoryTableInstruction i) :
    ResultKeepsBackend s (exec cfg p s f pf i) := by
  cases i <;> simp only [MemoryTableInstruction] at covered
  all_goals simp only [exec, pop_n_stack_form, pop_ref_stack_form, pushI32, pushV]
  all_goals repeat' (split <;> (try simp_all only []))
  all_goals first
    | rfl
    | trivial
    | (change (setFrame _ _).real.isSome = s.real.isSome; rw [set_frame_real])

theorem load_instruction_keeps_backend (cfg : NearCfg) (p : Prepared)
    (s : St) (f : Frame) (pf : PFunc) (op align off : Nat) :
    ResultKeepsBackend s (exec cfg p s f pf (.load op align off)) := by
  simp only [exec]
  rcases he : loadSpec op with ⟨w, sgn, is64⟩
  simp only [he]
  repeat' (split <;> (try simp_all only []))
  all_goals first
    | exact congrArg Option.isSome (pop_n_real s)
    | (change (setFrame _ _).real.isSome = s.real.isSome
       simp only [set_frame_real, pushI32, pushI64, pushV, pop_n_real])

end NearCompression
