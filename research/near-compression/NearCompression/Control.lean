import NearCompression.Observational

/-! Actual interpreter control and bulk-memory helpers preserve logical map
representations. Gas hooks and failures are included without changing costs. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem state_equiv_set_frame (s t : St) (h : StateEquivalent s t) (f : Frame) :
    StateEquivalent (setFrame s f) (setFrame t f) := by
  have hf : s.frames = t.frames := by
    have he := congrArg St.frames h.core
    exact he
  unfold setFrame
  rw [hf]
  cases t.frames with
  | nil => exact h
  | cons x xs =>
    exact ⟨congrArg (fun s : St => { s with frames := f :: xs }) h.core, h.real⟩

theorem state_equiv_control_update (s t : St) (h : StateEquivalent s t)
    (stack : Array Val) (frames : List Frame) (stackRem : Nat) :
    StateEquivalent { s with stack, frames, stackRem } { t with stack, frames, stackRem } :=
  ⟨congrArg (fun s : St => { s with stack, frames, stackRem }) h.core, h.real⟩

theorem state_equiv_set_stack (s t : St) (h : StateEquivalent s t) (stack : Array Val) :
    StateEquivalent { s with stack } { t with stack } :=
  ⟨congrArg (fun s : St => { s with stack }) h.core, h.real⟩

theorem do_return_equiv (p : Prepared) (s t : St) (h : StateEquivalent s t) :
    ResultEquivalent (doReturn p s) (doReturn p t) := by
  have hf : s.frames = t.frames := by have he := congrArg St.frames h.core; exact he
  have hv : s.stack = t.stack := by have he := congrArg St.stack h.core; exact he
  have hr : s.stackRem = t.stackRem := by have he := congrArg St.stackRem h.core; exact he
  unfold doReturn
  rw [hf, hv, hr]
  repeat' (split <;> (try simp_all only []))
  all_goals first
    | exact h
    | rfl
    | exact state_equiv_control_update s t h _ _ _

theorem do_br_equiv (p : Prepared) (s t : St) (h : StateEquivalent s t) (f : Frame) (l : Nat) :
    ResultEquivalent (doBr p s f l) (doBr p t f l) := by
  have hv : s.stack = t.stack := by have he := congrArg St.stack h.core; exact he
  unfold doBr
  rw [hv]
  split
  · exact do_return_equiv p s t h
  · split
    · rfl
    · apply state_equiv_set_frame
      exact state_equiv_set_stack s t h _

theorem mem_copy_equiv (s t : St) (h : StateEquivalent s t) (d src n : Nat) :
    ResultEquivalent (memCopy s d src n) (memCopy t d src n) := by
  unfold memCopy
  rw [state_equiv_mem_bytes s t h, state_equiv_read_bytes s t h]
  split
  · exact ⟨h, rfl⟩
  · exact state_equiv_write_bytes s t h _ _

theorem mem_init_equiv (s t : St) (h : StateEquivalent s t) (seg d src n : Nat) :
    ResultEquivalent (memInit s seg d src n) (memInit t seg d src n) := by
  have hd : s.datas = t.datas := by have he := congrArg St.datas h.core; exact he
  unfold memInit
  rw [hd, state_equiv_mem_bytes s t h]
  dsimp only
  split
  · exact ⟨h, rfl⟩
  · exact state_equiv_write_bytes s t h _ _

def StateExceptEquivalent : Except String St → Except String St → Prop
  | .ok s, .ok t => StateEquivalent s t
  | .error e, .error f => e = f
  | _, _ => False

theorem sync_equiv (s t : St) (h : StateEquivalent s t) :
    StateExceptEquivalent (sync s) (sync t) := by
  unfold sync
  rw [state_equiv_gas s t h]
  dsimp only
  repeat' (split <;> (try simp_all only []))
  all_goals first
    | exact h
    | exact state_equiv_set_gas s t h _
    | rfl

theorem charge_equiv (s t : St) (h : StateEquivalent s t) (fee : Fee) (count : Nat) :
    ResultEquivalent (charge s fee count) (charge t fee count) := by
  have hg := state_equiv_gas s t h
  have hs := sync_equiv s t h
  unfold charge
  rw [hg]
  dsimp only
  split
  · cases he : sync s <;> cases hf : sync t <;>
      simp only [he, hf, StateExceptEquivalent] at hs
    · rw [hs]
      rfl
    · dsimp only
      rw [state_equiv_gas _ _ hs]
      repeat' (split <;> (try simp_all only []))
      all_goals exact ⟨state_equiv_set_gas _ _ hs _, rfl⟩
  · split
    · cases he : sync s <;> cases hf : sync t <;>
        simp only [he, hf, StateExceptEquivalent] at hs
      · rw [hs]
        rfl
      · dsimp only
        rw [state_equiv_gas _ _ hs]
        repeat' (split <;> (try simp_all only []))
        all_goals first | exact ⟨state_equiv_set_gas _ _ hs _, rfl⟩ | rfl
    · exact state_equiv_set_gas s t h _

/-- The gas/frame dispatcher adds no further map-equivalence obligation once
all instruction bodies preserve it. The instruction premise remains open. -/
theorem step_equiv_of_exec (cfg : NearCfg) (p : Prepared)
    (execSim : ∀ s t, StateEquivalent s t → ∀ f pf i,
      ResultEquivalent (exec cfg p s f pf i) (exec cfg p t f pf i)) :
    StepPreservesMaps cfg p := by
  intro s t h
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
          | none => exact execSim s t h f pf i
          | some kfee =>
            exact result_equiv_bind _ _ (charge_equiv s t h kfee.2
              (if kfee.1 = .linear then topCount t else 0))
              (fun s => exec cfg p s f pf i) (fun t => exec cfg p t f pf i)
              (fun s t h => execSim s t h f pf i)

theorem state_equiv_real_is_some (s t : St) (h : StateEquivalent s t) :
    s.real.isSome = t.real.isSome := by
  have hr := h.real
  cases ha : s.real <;> cases hb : t.real <;> simp only [ha, hb, OptionalRealEquivalent] at hr
  all_goals rfl

/-- Includes the real-host domain gate, CallingHost gas synchronization,
ReturningFromHost gas reset, and host-error classification. -/
theorem call_host_equiv (s t : St) (h : StateEquivalent s t) (name : String)
    (hostSim : ∀ call, hostCall name = some call → HostSim call call) :
    ResultEquivalent (callHost s name) (callHost t name) := by
  have hs := sync_equiv s t h
  unfold callHost
  rw [state_equiv_real_is_some s t h]
  split
  · rfl
  · cases he : sync s <;> cases hf : sync t <;>
      simp only [he, hf, StateExceptEquivalent] at hs
    · rw [hs]
      rfl
    · rename_i u v
      dsimp only
      cases hc : hostCall name with
      | none => rfl
      | some call =>
        have hh := hostSim call hc u v hs
        cases ha : call.run u <;> cases hb : call.run v <;>
          simp only [ha, hb, HostResultEquivalent] at hh
        · simp only [ha, hb]
          rw [state_equiv_gas _ _ hh.2]
          exact state_equiv_set_gas _ _ hh.2 _
        · simp only [ha, hb]
          rw [hh.1]
          split
          · rfl
          · exact ⟨hh.2, rfl⟩

/-- The four proved storage dispatches now include the surrounding VM gas hooks. -/
theorem core_storage_call_equiv (s t : St) (h : StateEquivalent s t) (name : String)
    (hn : name ∈ ["storage_read", "storage_write", "storage_remove", "storage_has_key"]) :
    ResultEquivalent (callHost s name) (callHost t name) := by
  apply call_host_equiv s t h name
  intro call hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with hn | hn | hn | hn
  · subst name
    exact actual_storage_read_sim call hc
  · subst name
    exact actual_storage_write_sim call hc
  · subst name
    exact actual_storage_remove_sim call hc
  · subst name
    exact actual_storage_has_key_sim call hc

end NearCompression
