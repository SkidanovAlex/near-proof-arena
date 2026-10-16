import NearCompression.DataInstructionPersistence

/-! Backend persistence through byte loops and bulk memory instructions. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem for_in_plain_real (xs : List Nat) (f : Nat → St → St) (s : St)
    (hf : ∀ i u, (f i u).real = u.real) :
    (forIn (m := Id) xs s fun i st => ForInStep.yield (f i st)).real = s.real := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons]
    exact (ih (f x s)).trans (hf x s)

theorem write_le_real (s : St) (a w v : Nat) : (writeLE s a w v).real = s.real := by
  unfold writeLE
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  apply for_in_plain_real
  intro i u
  rfl

theorem mem_copy_keeps_backend (s : St) (d src n : Nat) :
    ResultKeepsBackend s (memCopy s d src n) := by
  unfold memCopy
  split
  · rfl
  · exact congrArg Option.isSome (write_bytes_real s _ _)

theorem mem_init_keeps_backend (s : St) (seg d src n : Nat) :
    ResultKeepsBackend s (memInit s seg d src n) := by
  unfold memInit
  dsimp only
  split
  · rfl
  · exact congrArg Option.isSome (write_bytes_real s _ _)

theorem mem_fill_keeps_backend (s : St) (d v n : Nat) :
    ResultKeepsBackend s (memFill s d v n) := by
  unfold memFill
  split
  · rfl
  · simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', ResultKeepsBackend]
    apply congrArg Option.isSome
    apply for_in_plain_real
    intro i u
    rfl

theorem store_instruction_keeps_backend (cfg : NearCfg) (p : Prepared)
    (s : St) (f : Frame) (pf : PFunc) (op align off : Nat) :
    ResultKeepsBackend s (exec cfg p s f pf (.store op align off)) := by
  simp only [exec]
  split
  · change (popN (popN s).2).2.real.isSome = s.real.isSome
    simp only [pop_n_real]
  · change (setFrame _ _).real.isSome = s.real.isSome
    simp only [set_frame_real, write_le_real, pop_n_real]

theorem bulk_memory_instruction_keeps_backend (cfg : NearCfg) (p : Prepared)
    (s : St) (f : Frame) (pf : PFunc) (i : Instr)
    (covered : i = .memCopy ∨ i = .memFill ∨ ∃ seg, i = .memInit seg) :
    ResultKeepsBackend s (exec cfg p s f pf i) := by
  rcases covered with rfl | rfl | ⟨seg, rfl⟩
  all_goals simp only [exec]
  all_goals apply result_keeps_backend_change_start s (popN (popN (popN s).2).2).2
  all_goals try simp only [pop_n_real]
  · apply result_bind_keeps_backend
    · exact mem_copy_keeps_backend _ _ _ _
    · intro u; exact congrArg Option.isSome (set_frame_real u _)
  · apply result_bind_keeps_backend
    · exact mem_fill_keeps_backend _ _ _ _
    · intro u; exact congrArg Option.isSome (set_frame_real u _)
  · apply result_bind_keeps_backend
    · exact mem_init_keeps_backend _ _ _ _ _
    · intro u; exact congrArg Option.isSome (set_frame_real u _)

theorem table_init_keeps_backend (s : St) (seg d src n : Nat) :
    ResultKeepsBackend s (tableInit s seg d src n) := by
  unfold tableInit
  dsimp only
  split <;> rfl

theorem bulk_table_instruction_keeps_backend (cfg : NearCfg) (p : Prepared)
    (s : St) (f : Frame) (pf : PFunc) (i : Instr) (covered : BulkTableInstruction i) :
    ResultKeepsBackend s (exec cfg p s f pf i) := by
  cases i <;> simp only [BulkTableInstruction] at covered
  all_goals simp only [exec, pop_n_stack_form, pop_ref_stack_form]
  all_goals split
  all_goals first
    | rfl
    | (change (setFrame _ _).real.isSome = s.real.isSome; rw [set_frame_real])

theorem table_init_instruction_keeps_backend (cfg : NearCfg) (p : Prepared)
    (s : St) (f : Frame) (pf : PFunc) (seg tab : Nat) :
    ResultKeepsBackend s (exec cfg p s f pf (.tableInit seg tab)) := by
  simp only [exec]
  apply result_keeps_backend_change_start s (popN (popN (popN s).2).2).2
  · simp only [pop_n_real]
  · apply result_bind_keeps_backend
    · exact table_init_keeps_backend _ _ _ _ _
    · intro u; exact congrArg Option.isSome (set_frame_real u _)

end NearCompression
