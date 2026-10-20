import NearCompression.Control

/-! Function entry and import dispatch for the actual interpreter. Import
simulation remains a premise for general programs, not an assumed global axiom. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem state_equiv_set_stack_rem (s t : St) (h : StateEquivalent s t) (remaining : Nat) :
    StateEquivalent { s with stackRem := remaining } { t with stackRem := remaining } :=
  ⟨congrArg (fun s : St => { s with stackRem := remaining }) h.core, h.real⟩

theorem state_equiv_stack_frames (s t : St) (h : StateEquivalent s t)
    (stack : Array Val) (frames : List Frame) :
    StateEquivalent { s with stack, frames } { t with stack, frames } :=
  ⟨congrArg (fun s : St => { s with stack, frames }) h.core, h.real⟩

/-- Exact continuation after the entry gas charge, with shared program metadata. -/
def entryFrame (p : Prepared) (pf : PFunc) (fi : Nat) (s : St) : Res :=
  let base := s.stack.size - pf.type.params.size
  let args := s.stack.extract base s.stack.size
  let fr : Frame := {
    fn := fi - p.m.imports.size, pc := 0,
    locals := args ++ pf.locals.map Val.default,
    labels := [{ target := pf.code.size, arity := pf.type.results.size,
                 height := base, isLoop := false }], base := base }
  .cont { s with stack := s.stack.extract 0 base, frames := fr :: s.frames }

theorem entry_frame_equiv (p : Prepared) (pf : PFunc) (fi : Nat)
    (s t : St) (h : StateEquivalent s t) :
    ResultEquivalent (entryFrame p pf fi s) (entryFrame p pf fi t) := by
  have hv : s.stack = t.stack := by have he := congrArg St.stack h.core; exact he
  have hf : s.frames = t.frames := by have he := congrArg St.frames h.core; exact he
  unfold entryFrame
  rw [hv, hf]
  exact state_equiv_stack_frames s t h _ _

theorem enter_equiv (p : Prepared) (s t : St) (h : StateEquivalent s t) (fi : Nat) :
    ResultEquivalent (enter p s fi) (enter p t fi) := by
  have hr : s.stackRem = t.stackRem := by have he := congrArg St.stackRem h.core; exact he
  unfold enter
  dsimp only
  cases p.funcs[fi - p.m.imports.size]? with
  | none => rfl
  | some pf =>
    dsimp only
    rw [hr]
    split
    · have hs := sync_equiv s t h
      cases he : sync s <;> cases hf : sync t <;>
        simp only [he, hf, StateExceptEquivalent] at hs
      · rw [hs]
        rfl
      · exact ⟨hs, rfl⟩
    · have hu := state_equiv_set_stack_rem s t h (t.stackRem - pf.stackCharge)
      have hc := charge_equiv _ _ hu (Fee.const pf.prologueGas) 0
      exact result_equiv_bind _ _ hc (entryFrame p pf fi) (entryFrame p pf fi)
        (entry_frame_equiv p pf fi)

/-- Only actual imports of this prepared program need host simulation. -/
def ImportsPreserveMaps (p : Prepared) : Prop :=
  ∀ (i : Nat) (hi : i < p.m.imports.size) call,
    hostCall p.m.imports[i].name = some call → HostSim call call

theorem call_func_equiv (cfg : NearCfg) (p : Prepared) (imports : ImportsPreserveMaps p)
    (s t : St) (h : StateEquivalent s t) (fi : Nat) :
    ResultEquivalent (callFunc cfg p s fi) (callFunc cfg p t fi) := by
  unfold callFunc
  split
  · rename_i hi
    exact call_host_equiv s t h _ (imports fi hi)
  · exact enter_equiv p s t h fi

theorem exec_call_equiv (cfg : NearCfg) (p : Prepared) (imports : ImportsPreserveMaps p)
    (s t : St) (h : StateEquivalent s t) (f : Frame) (pf : PFunc) (fi : Nat) :
    ResultEquivalent (exec cfg p s f pf (.call fi)) (exec cfg p t f pf (.call fi)) := by
  exact call_func_equiv cfg p imports _ _ (state_equiv_set_frame s t h _) fi

theorem exec_call_indirect_equiv (cfg : NearCfg) (p : Prepared) (imports : ImportsPreserveMaps p)
    (s t : St) (h : StateEquivalent s t) (f : Frame) (pf : PFunc) (ty table : Nat) :
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
    | exact call_func_equiv cfg p imports _ _ (state_equiv_set_frame _ _ hs _) _

end NearCompression
