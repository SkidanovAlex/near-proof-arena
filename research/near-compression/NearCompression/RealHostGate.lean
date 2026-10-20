import NearCompression.HostCoverage

/-! Real-backend wrapper coverage includes exact rejection of gated dispatches.
This does not extend D3 semantics or assert mock-host simulation for gated names. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem real_gated_call_rejects (s : St) (real : s.real.isSome = true)
    (name : String) (gated : name ∈ realOodHosts) :
    callHost s name = .unmodeled s!"out-of-domain host function {name} called" := by
  have hg : realOodHosts.contains name = true := List.contains_iff_mem.mpr gated
  simp only [callHost, real, hg, Bool.and_self, ite_true]

theorem real_gated_call_equiv (s t : St) (h : StateEquivalent s t)
    (real : s.real.isSome = true) (name : String) (gated : name ∈ realOodHosts) :
    ResultEquivalent (callHost s name) (callHost t name) := by
  have rt : t.real.isSome = true := (state_equiv_real_is_some s t h).symm.trans real
  rw [real_gated_call_rejects s real name gated, real_gated_call_rejects t rt name gated]
  rfl

/-- This list covers wrapper behavior on real states, not raw hostCall behavior. -/
def realWrapperNames : List String := provedHostNames ++ realOodHosts

def checkRealWrapperImports (p : Prepared) : Bool :=
  p.m.imports.all (fun imp => realWrapperNames.contains imp.name)

theorem listed_real_wrapper_equiv (s t : St) (h : StateEquivalent s t)
    (real : s.real.isSome = true) (name : String) (listed : name ∈ realWrapperNames) :
    ResultEquivalent (callHost s name) (callHost t name) := by
  rcases List.mem_append.mp listed with proved | gated
  · apply call_host_equiv s t h name
    intro call hc
    exact proved_host_sim name proved call hc
  · exact real_gated_call_equiv s t h real name gated

theorem checked_real_call_func_equiv (cfg : NearCfg) (p : Prepared)
    (checked : checkRealWrapperImports p = true)
    (s t : St) (h : StateEquivalent s t) (real : s.real.isSome = true) (fi : Nat) :
    ResultEquivalent (callFunc cfg p s fi) (callFunc cfg p t fi) := by
  unfold callFunc
  split
  · rename_i hi
    have hall := Array.all_eq_true.mp checked
    have listed : p.m.imports[fi].name ∈ realWrapperNames :=
      List.contains_iff_mem.mp (hall fi hi)
    exact listed_real_wrapper_equiv s t h real _ listed
  · exact enter_equiv p s t h fi

theorem checked_real_direct_call_equiv (cfg : NearCfg) (p : Prepared)
    (checked : checkRealWrapperImports p = true)
    (s t : St) (h : StateEquivalent s t) (real : s.real.isSome = true)
    (f : Frame) (pf : PFunc) (fi : Nat) :
    ResultEquivalent (exec cfg p s f pf (.call fi)) (exec cfg p t f pf (.call fi)) := by
  apply checked_real_call_func_equiv cfg p checked _ _ (state_equiv_set_frame s t h _) _ fi
  cases hf : s.frames <;> simpa only [setFrame, hf] using real

end NearCompression
