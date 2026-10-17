import NearCompression.BulkPersistence

/-! Real backend persistence for every instruction, step and fuel-bounded run. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem checked_real_exec_keeps_backend (cfg : NearCfg) (p : Prepared) (checked : checkRealWrapperImports p = true)
    (s : St) (real : s.real.isSome = true) (f : Frame) (pf : PFunc) (i : Instr) :
    ResultKeepsBackend s (exec cfg p s f pf i) := by
  cases i <;> solve
    | (with_reducible apply stack_control_instruction_keeps_backend cfg p s f pf; simp only [StackControlInstruction])
    | (with_reducible apply memory_table_instruction_keeps_backend cfg p s f pf; simp only [MemoryTableInstruction])
    | (with_reducible apply bulk_table_instruction_keeps_backend cfg p s f pf; simp only [BulkTableInstruction])
    | with_reducible exact checked_real_direct_call_keeps_backend cfg p checked s real f pf _
    | with_reducible exact checked_real_indirect_call_keeps_backend cfg p checked s real f pf _ _
    | with_reducible exact numeric_instruction_keeps_backend cfg p s f pf _
    | with_reducible exact load_instruction_keeps_backend cfg p s f pf _ _ _
    | with_reducible exact store_instruction_keeps_backend cfg p s f pf _ _ _
    | with_reducible exact table_init_instruction_keeps_backend cfg p s f pf _ _
    | (with_reducible apply bulk_memory_instruction_keeps_backend cfg p s f pf; exact Or.inl rfl)
    | (with_reducible apply bulk_memory_instruction_keeps_backend cfg p s f pf; exact Or.inr (Or.inl rfl))
    | (with_reducible apply bulk_memory_instruction_keeps_backend cfg p s f pf; exact Or.inr (Or.inr ⟨_, rfl⟩))


theorem result_keeps_backend_trans (s u : St) (r : Res)
    (hu : u.real.isSome = s.real.isSome) (hr : ResultKeepsBackend u r) :
    ResultKeepsBackend s r := by
  cases r <;> simp only [ResultKeepsBackend] at hr ⊢
  all_goals first | exact hr.trans hu | trivial

theorem checked_real_step_keeps_backend (cfg : NearCfg) (p : Prepared)
    (checked : checkRealWrapperImports p = true)
    (s : St) (real : s.real.isSome = true) :
    ResultKeepsBackend s (step cfg p s) := by
  unfold step
  cases s.frames with
  | nil => rfl
  | cons f fs =>
    dsimp only
    cases p.funcs[f.fn]? with
    | none => trivial
    | some pf =>
      dsimp only
      cases pf.code[f.pc]? with
      | none => trivial
      | some i =>
        dsimp only
        cases pf.gas[f.pc]? with
        | none => trivial
        | some fee =>
          cases fee with
          | none => exact checked_real_exec_keeps_backend cfg p checked s real f pf i
          | some kfee =>
            rcases kfee with ⟨kind, fee⟩
            dsimp only
            have hp := charge_keeps_backend s fee (if kind = .linear then topCount s else 0)
            cases hc : charge s fee (if kind = .linear then topCount s else 0) with
            | cont u =>
              simp only [hc] at hp
              exact result_keeps_backend_trans s u _ hp
                (checked_real_exec_keeps_backend cfg p checked u (hp.trans real) f pf i)
            | fin u => simpa only [hc] using hp
            | abort u e => simpa only [hc] using hp
            | unmodeled e => trivial

theorem checked_real_run_keeps_backend (cfg : NearCfg) (p : Prepared)
    (checked : checkRealWrapperImports p = true) (fuel : Nat)
    (s : St) (real : s.real.isSome = true) :
    ResultKeepsBackend s (run cfg p fuel s) := by
  induction fuel generalizing s with
  | zero => trivial
  | succ n ih =>
    unfold run
    have hp := checked_real_step_keeps_backend cfg p checked s real
    cases he : step cfg p s with
    | cont u =>
      simp only [he] at hp
      exact result_keeps_backend_trans s u _ hp (ih u (hp.trans real))
    | fin u => simpa only [he] using hp
    | abort u e => simpa only [he] using hp
    | unmodeled e => trivial

theorem checked_real_run_equiv (cfg : NearCfg) (p : Prepared)
    (checked : checkRealWrapperImports p = true) (fuel : Nat)
    (s t : St) (h : StateEquivalent s t) (real : s.real.isSome = true) :
    ResultEquivalent (run cfg p fuel s) (run cfg p fuel t) := by
  induction fuel generalizing s t with
  | zero => rfl
  | succ n ih =>
    change ResultEquivalent ((step cfg p s).bind (run cfg p n))
      ((step cfg p t).bind (run cfg p n))
    apply result_equiv_bind_cont _ _ (checked_real_step_equiv cfg p checked s t h real)
    intro u v hu huv
    have hp := checked_real_step_keeps_backend cfg p checked s real
    have hr := backend_invariant_cont s u (step cfg p s) hp hu
    exact ih u v huv (hr.trans real)

end NearCompression
