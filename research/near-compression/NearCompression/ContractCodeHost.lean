import NearCompression.ValidatorHosts

/-! Current contract identifier query with absent/local outcomes. -/
namespace NearCompression
open NearSpecV3.Wasm

def contractCodeBody (write : Nat → ByteArray → HM Unit) (reg : Nat) : HM Unit := do
  match (← get).ctx.accountContract with
  | none => pushRet 0
  | some hash => write reg hash; pushRet 1

theorem contract_code_body_sim (write : Nat → ByteArray → HM Unit)
    (writeSim : ∀ reg bytes, HostSim (write reg bytes) (write reg bytes)) (reg : Nat) :
    HostSim (contractCodeBody write reg) (contractCodeBody write reg) := by
  unfold contractCodeBody
  apply host_sim_get_bind
  intro s t h
  have hc : s.ctx = t.ctx := by have he := congrArg St.ctx h.core; exact he
  rw [hc]
  split
  · exact host_sim_push_ret 0 true s t h
  · apply host_bind_equiv
    · exact writeSim _ _ s t h
    intro _ u v huv
    exact host_sim_push_ret 1 true u v huv

def contractCodeCode (base : Cost) (write : Nat → ByteArray → HM Unit) : HM Unit := do
  let a ← popArgs 1
  payBaseH base
  contractCodeBody write a[0]

theorem contract_code_code_sim (base : Cost) (write : Nat → ByteArray → HM Unit)
    (writeSim : ∀ reg bytes, HostSim (write reg bytes) (write reg bytes)) :
    HostSim (contractCodeCode base write) (contractCodeCode base write) := by
  unfold contractCodeCode
  apply host_sim_bind
  · exact host_sim_pop_args 1
  intro a
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  exact contract_code_body_sim write writeSim a[0]

theorem actual_contract_code_code : hostCall "current_contract_code" =
    some (contractCodeCode C.base (fun reg bytes => regSetH reg bytes)) := by rfl

theorem actual_contract_code_sim (call : HM Unit)
    (hc : hostCall "current_contract_code" = some call) : HostSim call call := by
  rw [actual_contract_code_code] at hc
  cases Option.some.inj hc
  with_reducible exact contract_code_code_sim C.base (fun reg bytes => regSetH reg bytes) (fun reg bytes => host_sim_reg_set reg bytes true)

end NearCompression
