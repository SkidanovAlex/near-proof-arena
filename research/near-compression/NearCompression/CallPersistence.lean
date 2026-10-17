import NearCompression.PersistenceCoverage

/-! Persistent real backend across wrapper rejection and direct/indirect calls. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem listed_real_wrapper_keeps_backend (s : St) (real : s.real.isSome = true)
    (name : String) (listed : name ∈ realWrapperNames) :
    ResultKeepsBackend s (callHost s name) := by
  rcases List.mem_append.mp listed with proved | gated
  · exact call_host_keeps_real s real name (proved_host_keeps_real name proved)
  · rw [real_gated_call_rejects s real name gated]
    trivial

theorem checked_real_call_func_keeps_backend (cfg : NearCfg) (p : Prepared)
    (checked : checkRealWrapperImports p = true)
    (s : St) (real : s.real.isSome = true) (fi : Nat) :
    ResultKeepsBackend s (callFunc cfg p s fi) := by
  unfold callFunc
  split
  · rename_i hi
    have hall := Array.all_eq_true.mp checked
    have listed : p.m.imports[fi].name ∈ realWrapperNames :=
      List.contains_iff_mem.mp (hall fi hi)
    exact listed_real_wrapper_keeps_backend s real _ listed
  · exact enter_keeps_backend p s fi

theorem result_keeps_backend_change_start (s t : St) (r : Res)
    (h : t.real = s.real) (hr : ResultKeepsBackend t r) : ResultKeepsBackend s r := by
  cases r <;> simp_all only [ResultKeepsBackend]

theorem checked_real_direct_call_keeps_backend (cfg : NearCfg) (p : Prepared)
    (checked : checkRealWrapperImports p = true)
    (s : St) (real : s.real.isSome = true) (f : Frame) (pf : PFunc) (fi : Nat) :
    ResultKeepsBackend s (exec cfg p s f pf (.call fi)) := by
  apply result_keeps_backend_change_start s (setFrame s { f with pc := f.pc + 1 })
  · exact set_frame_real _ _
  · apply checked_real_call_func_keeps_backend cfg p checked
    simpa only [set_frame_real] using real

theorem checked_real_indirect_call_keeps_backend (cfg : NearCfg) (p : Prepared)
    (checked : checkRealWrapperImports p = true)
    (s : St) (real : s.real.isSome = true) (f : Frame) (pf : PFunc) (ty table : Nat) :
    ResultKeepsBackend s (exec cfg p s f pf (.callIndirect ty table)) := by
  simp only [exec]
  repeat' (split <;> (try simp_all only []))
  all_goals first
    | trivial
    | exact congrArg Option.isSome (pop_n_real s)
    | (apply result_keeps_backend_change_start s (setFrame (popN s).2 { f with pc := f.pc + 1 })
       · simp only [set_frame_real, pop_n_real]
       · apply checked_real_call_func_keeps_backend cfg p checked
         simpa only [set_frame_real, pop_n_real] using real)

end NearCompression
