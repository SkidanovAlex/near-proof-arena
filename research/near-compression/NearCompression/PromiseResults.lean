import NearCompression.SignatureHost

/-! Promise observations and returning a receipt preserve all result variants
and invalid-index/joint-promise failures. -/
namespace NearCompression
open NearSpecV3.Wasm

def promiseResultBody (write : Nat → ByteArray → HM Unit) (idx reg : Nat) : HM Unit := do
  match (← get).ctx.promiseResults[idx]? with
  | none => hErr s!"InvalidPromiseResultIndex \{ result_idx: {idx} }"
  | some .notReady => pushRet 0
  | some (.ok d) => write reg d; pushRet 1
  | some .failed => pushRet 2

theorem promise_result_body_sim (write : Nat → ByteArray → HM Unit)
    (writeSim : ∀ reg bytes, HostSim (write reg bytes) (write reg bytes)) (idx reg : Nat) :
    HostSim (promiseResultBody write idx reg) (promiseResultBody write idx reg) := by
  unfold promiseResultBody
  apply host_sim_get_bind
  intro s t h
  have hc : s.ctx = t.ctx := by have he := congrArg St.ctx h.core; exact he
  rw [hc]
  repeat' (split <;> (try simp_all only []))
  all_goals first
    | exact host_sim_error _ s t h
    | exact host_sim_push_ret _ true s t h
    | (apply host_bind_equiv
       · exact writeSim _ _ s t h
       intro _ u v huv
       exact host_sim_push_ret 1 true u v huv)

def promiseResultCode (base : Cost) (write : Nat → ByteArray → HM Unit) : HM Unit := do
  let a ← popArgs 2
  payBaseH base
  promiseResultBody write a[0] a[1]

theorem promise_result_code_sim (base : Cost) (write : Nat → ByteArray → HM Unit)
    (writeSim : ∀ reg bytes, HostSim (write reg bytes) (write reg bytes)) :
    HostSim (promiseResultCode base write) (promiseResultCode base write) := by
  unfold promiseResultCode
  apply host_sim_bind
  · exact host_sim_pop_args 2
  intro a
  apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  exact promise_result_body_sim write writeSim a[0] a[1]

def promiseReturnBody (idx : Nat) : HM Unit := do
  match (← get).promises[idx]? with
  | none => hErr s!"InvalidPromiseIndex \{ promise_idx: {idx} }"
  | some (.joint _) => hErr "CannotReturnJointPromise"
  | some (.receipt r) => modify fun s => { s with ret := some (.inr r) }

theorem state_equiv_return_receipt (s t : St) (h : StateEquivalent s t) (receipt : Nat) :
    StateEquivalent { s with ret := some (.inr receipt) } { t with ret := some (.inr receipt) } :=
  ⟨congrArg (fun s : St => { s with ret := some (.inr receipt) }) h.core, h.real⟩

theorem promise_return_body_sim (idx : Nat) : HostSim (promiseReturnBody idx) (promiseReturnBody idx) := by
  unfold promiseReturnBody
  apply host_sim_get_bind
  intro s t h
  have hp : s.promises = t.promises := by have he := congrArg St.promises h.core; exact he
  rw [hp]
  repeat' (split <;> (try simp_all only []))
  all_goals first
    | exact host_sim_error _ s t h
    | exact ⟨rfl, state_equiv_return_receipt s t h _⟩

def promiseReturnCode (base ret : Cost) : HM Unit := do
  let a ← popArgs 1
  payBaseH base
  payBaseH ret
  promiseReturnBody a[0]

theorem promise_return_code_sim (base ret : Cost) : HostSim (promiseReturnCode base ret) (promiseReturnCode base ret) := by
  unfold promiseReturnCode
  apply host_sim_bind
  · exact host_sim_pop_args 1
  intro a
  apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  exact promise_return_body_sim a[0]

theorem actual_promise_result_code : hostCall "promise_result" =
    some (promiseResultCode C.base (fun reg bytes => regSetH reg bytes false)) := by rfl

theorem actual_promise_return_code : hostCall "promise_return" =
    some (promiseReturnCode C.base C.promiseReturn) := by rfl

theorem actual_promise_result_sim (call : HM Unit) (hc : hostCall "promise_result" = some call) :
    HostSim call call := by
  rw [actual_promise_result_code] at hc
  cases Option.some.inj hc
  with_reducible apply promise_result_code_sim C.base (fun reg bytes => regSetH reg bytes false)
  intro reg bytes
  with_reducible exact host_sim_reg_set reg bytes false

theorem actual_promise_return_sim (call : HM Unit) (hc : hostCall "promise_return" = some call) :
    HostSim call call := by
  rw [actual_promise_return_code] at hc
  cases Option.some.inj hc
  with_reducible exact promise_return_code_sim C.base C.promiseReturn

end NearCompression
