import NearCompression.RealHostGate

/-! Real-backed instruction simulation through direct and indirect calls. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem pop_n_real (s : St) : (popN s).2.real = s.real := by
  unfold popN popV
  cases s.stack.back?.getD (.i32 0) <;> rfl

theorem set_frame_real (s : St) (f : Frame) : (setFrame s f).real = s.real := by
  unfold setFrame
  split <;> rfl

theorem checked_real_indirect_call_equiv (cfg : NearCfg) (p : Prepared) (checked : checkRealWrapperImports p = true)
    (s t : St) (h : StateEquivalent s t) (real : s.real.isSome = true) (f : Frame) (pf : PFunc) (ty table : Nat) :
    ResultEquivalent (exec cfg p s f pf (.callIndirect ty table))
      (exec cfg p t f pf (.callIndirect ty table)) := by
  obtain ⟨hv, hs⟩ := state_equiv_pop_n s t h
  have ht : (popN s).2.table = (popN t).2.table := by
    have he := congrArg St.table hs.core
    exact he
  simp only [exec]
  rw [hv, ht]
  repeat' (split <;> (try simp_all only []))
  all_goals first
    | exact ⟨hs, rfl⟩
    | rfl
    | (apply checked_real_call_func_equiv cfg p checked _ _ (state_equiv_set_frame _ _ hs _) _ _
       simpa only [set_frame_real, pop_n_real] using real)

theorem checked_real_exec_equiv (cfg : NearCfg) (p : Prepared) (checked : checkRealWrapperImports p = true)
    (s t : St) (h : StateEquivalent s t) (real : s.real.isSome = true) (f : Frame) (pf : PFunc) (i : Instr) :
    ResultEquivalent (exec cfg p s f pf i) (exec cfg p t f pf i) := by
  cases i <;> solve
    | (with_reducible apply stack_control_instruction_equiv cfg p s t h f pf; simp only [StackControlInstruction])
    | (with_reducible apply memory_table_instruction_equiv cfg p s t h f pf; simp only [MemoryTableInstruction])
    | (with_reducible apply bulk_table_instruction_equiv cfg p s t h f pf; simp only [BulkTableInstruction])
    | with_reducible exact checked_real_direct_call_equiv cfg p checked s t h real f pf _
    | with_reducible exact checked_real_indirect_call_equiv cfg p checked s t h real f pf _ _
    | with_reducible exact exec_numeric_instruction_equiv cfg p s t h f pf _
    | with_reducible exact load_instruction_equiv cfg p s t h f pf _ _ _
    | with_reducible exact store_instruction_equiv cfg p s t h f pf _ _ _
    | with_reducible exact table_init_instruction_equiv cfg p s t h f pf _ _
    | (with_reducible apply bulk_memory_instruction_equiv cfg p s t h f pf; exact Or.inl rfl)
    | (with_reducible apply bulk_memory_instruction_equiv cfg p s t h f pf; exact Or.inr (Or.inl rfl))
    | (with_reducible apply bulk_memory_instruction_equiv cfg p s t h f pf; exact Or.inr (Or.inr ⟨_, rfl⟩))


theorem charge_cont_real (s u : St) (fee : Fee) (count : Nat)
    (hc : charge s fee count = .cont u) : u.real = s.real := by
  unfold charge at hc
  repeat' (split at hc <;> (try simp_all only []))
  all_goals cases hc <;> rfl

theorem result_equiv_bind_cont (r t : Res) (h : ResultEquivalent r t) (f g : St → Res)
    (next : ∀ s u, r = .cont s → StateEquivalent s u → ResultEquivalent (f s) (g u)) :
    ResultEquivalent (r.bind f) (t.bind g) := by
  cases r <;> cases t <;> simp only [ResultEquivalent] at h <;>
    first | exact next _ _ rfl h | exact h

theorem checked_real_step_equiv (cfg : NearCfg) (p : Prepared)
    (checked : checkRealWrapperImports p = true)
    (s t : St) (h : StateEquivalent s t) (real : s.real.isSome = true) :
    ResultEquivalent (step cfg p s) (step cfg p t) := by
  have hf : s.frames = t.frames := by have he := congrArg St.frames h.core; exact he
  have hc : topCount s = topCount t := by
    have he := congrArg topCount h.core
    exact he
  unfold step
  rw [hf, hc]
  cases t.frames with
  | nil => exact h
  | cons f fs =>
    dsimp only
    cases p.funcs[f.fn]? with
    | none => rfl
    | some pf =>
      dsimp only
      cases pf.code[f.pc]? with
      | none => rfl
      | some i =>
        dsimp only
        cases pf.gas[f.pc]? with
        | none => rfl
        | some fee =>
          cases fee with
          | none => exact checked_real_exec_equiv cfg p checked s t h real f pf i
          | some kfee =>
            apply result_equiv_bind_cont _ _ (charge_equiv s t h kfee.2
              (if kfee.1 = .linear then topCount t else 0))
              (fun s => exec cfg p s f pf i) (fun t => exec cfg p t f pf i)
            intro u v hu huv
            apply checked_real_exec_equiv cfg p checked u v huv _ f pf i
            rw [charge_cont_real s u _ _ hu]
            exact real

end NearCompression
