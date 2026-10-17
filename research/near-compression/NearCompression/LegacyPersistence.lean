import NearCompression.OutputPersistence

/-! Backend persistence for contract-code queries, gas and deprecated iterators. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem contract_code_body_keeps_real (write : Nat → ByteArray → HM Unit)
    (writeReal : ∀ reg bytes, HostKeepsReal (write reg bytes)) (reg : Nat) :
    HostKeepsReal (contractCodeBody write reg) := by
  unfold contractCodeBody
  apply host_real_get_bind
  intro s hs
  split
  · exact host_real_push_ret 0 true s hs
  · apply host_real_bind
    · exact writeReal _ _
    · intro _; exact host_real_push_ret 1 true
    · exact hs

theorem contract_code_code_keeps_real (base : Cost) (write : Nat → ByteArray → HM Unit)
    (writeSim : ∀ reg bytes, HostKeepsReal (write reg bytes)) :
    HostKeepsReal (contractCodeCode base write) := by
  unfold contractCodeCode
  apply host_real_bind
  · exact host_real_pop_args 1
  intro a
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  exact contract_code_body_keeps_real write writeSim a[0]

theorem actual_contract_code_keeps_real (call : HM Unit)
    (hc : hostCall "current_contract_code" = some call) : HostKeepsReal call := by
  rw [actual_contract_code_code] at hc
  cases Option.some.inj hc
  with_reducible exact contract_code_code_keeps_real C.base (fun reg bytes => regSetH reg bytes) (fun reg bytes => host_real_reg_set reg bytes true)

theorem gas_dispatch_keeps_real (cost : Nat) :
    HostKeepsReal (do let a ← popArgs 1; burnH (a[0] * cost)) := by
  apply host_real_bind
  · exact host_real_pop_args 1
  intro a
  unfold burnH
  exact host_real_with_gas _

theorem actual_gas_keeps_real (call : HM Unit) (hc : hostCall "gas" = some call) : HostKeepsReal call := by
  have he : hostCall "gas" = some (do let a ← popArgs 1; burnH (a[0] * 822756)) := rfl
  rw [he] at hc
  cases Option.some.inj hc
  exact gas_dispatch_keeps_real 822756

theorem deprecated_dispatch_keeps_real (n : Nat) (message : String) :
    HostKeepsReal (do let _ ← popArgs n; (hErr message : HM Unit)) := by
  apply host_real_bind
  · exact host_real_pop_args n
  intro _
  exact host_real_throw _

theorem actual_iterator_prefix_keeps_real (call : HM Unit)
    (hc : hostCall "storage_iter_prefix" = some call) : HostKeepsReal call := by
  have he : hostCall "storage_iter_prefix" = some (do
      let _ ← popArgs 2
      hErr "Deprecated { method_name: \"storage_iter_prefix\" }") := rfl
  rw [he] at hc
  cases Option.some.inj hc
  exact deprecated_dispatch_keeps_real 2 _

theorem actual_iterator_range_keeps_real (call : HM Unit)
    (hc : hostCall "storage_iter_range" = some call) : HostKeepsReal call := by
  have he : hostCall "storage_iter_range" = some (do
      let _ ← popArgs 4
      hErr "Deprecated { method_name: \"storage_iter_range\" }") := rfl
  rw [he] at hc
  cases Option.some.inj hc
  exact deprecated_dispatch_keeps_real 4 _

theorem actual_iterator_next_keeps_real (call : HM Unit)
    (hc : hostCall "storage_iter_next" = some call) : HostKeepsReal call := by
  have he : hostCall "storage_iter_next" = some (do
      let _ ← popArgs 3
      hErr "Deprecated { method_name: \"storage_iter_next\" }") := rfl
  rw [he] at hc
  cases Option.some.inj hc
  exact deprecated_dispatch_keeps_real 3 _

end NearCompression
