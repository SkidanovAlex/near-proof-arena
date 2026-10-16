import NearCompression.WriteHost

/-! Host argument/result stack simulation, including the actual popArgs loop.
This connects call-boundary values to the memory and storage helper proofs. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem state_equiv_pop_n (s t : St) (h : StateEquivalent s t) :
    (popN s).1 = (popN t).1 ∧ StateEquivalent (popN s).2 (popN t).2 := by
  have he : s.stack = t.stack := by
    have hh := congrArg St.stack h.core
    exact hh
  unfold popN popV
  simp only [he]
  cases t.stack.back?.getD (.i32 0) <;> refine ⟨rfl, ?_⟩ <;> constructor
  all_goals first
    | exact congrArg (fun s : St => { s with stack := t.stack.pop }) h.core
    | exact h.real

theorem state_equiv_push_v (s t : St) (h : StateEquivalent s t) (v : Val) :
    StateEquivalent (pushV s v) (pushV t v) :=
  ⟨congrArg (fun s => pushV s v) h.core, h.real⟩

theorem host_sim_push_ret (v : Nat) (is64 : Bool) : HostSim (pushRet v is64) (pushRet v is64) := by
  intro s t hs
  cases is64
  · exact ⟨rfl, state_equiv_push_v s t hs _⟩
  · exact ⟨rfl, state_equiv_push_v s t hs _⟩

theorem host_sim_for_in_list {B : Type} (xs : List Nat) (b : B)
    (f : Nat → B → HM (ForInStep B)) (h : ∀ i a, HostSim (f i a) (f i a)) :
    HostSim (forIn xs b f) (forIn xs b f) := by
  induction xs generalizing b with
  | nil => exact host_sim_pure b
  | cons x xs ih =>
    simp only [List.forIn_cons]
    with_reducible apply host_sim_bind
    · exact h x b
    intro out
    cases out with
    | done b => exact host_sim_pure b
    | yield b => exact ih b

theorem host_sim_for_in {B : Type} (range : Std.Legacy.Range) (b : B)
    (f : Nat → B → HM (ForInStep B)) (h : ∀ i a, HostSim (f i a) (f i a)) :
    HostSim (forIn range b f) (forIn range b f) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  exact host_sim_for_in_list _ b f h

/-- One iteration of the existing argument loop, with exact extracted value. -/
theorem host_sim_pop_iteration (out : Array Nat) :
    HostSim (do
      let (v, s) := popN (← get)
      set s
      pure (ForInStep.yield (out.push v)))
      (do
      let (v, s) := popN (← get)
      set s
      pure (ForInStep.yield (out.push v))) := by
  apply host_sim_get_bind
  intro s t hs
  obtain ⟨hv, hst⟩ := state_equiv_pop_n s t hs
  change ForInStep.yield (out.push (popN s).1) = ForInStep.yield (out.push (popN t).1) ∧
    StateEquivalent (popN s).2 (popN t).2
  exact ⟨congrArg (fun v => ForInStep.yield (out.push v)) hv, hst⟩

theorem host_sim_pop_args (n : Nat) : HostSim (popArgs n) (popArgs n) := by
  unfold popArgs
  with_reducible apply host_sim_bind
  · with_reducible apply host_sim_for_in
    intro i out
    exact host_sim_pop_iteration out
  intro out
  dsimp only
  split
  · exact host_sim_pure _
  · intro s t hs
    exact ⟨rfl, hs⟩

end NearCompression
