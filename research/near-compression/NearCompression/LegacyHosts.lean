import NearCompression.YieldId

/-! Legacy gas charging and exact deprecated-iterator rejection behavior. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem gas_dispatch_sim (cost : Nat) :
    HostSim (do let a ← popArgs 1; burnH (a[0] * cost))
      (do let a ← popArgs 1; burnH (a[0] * cost)) := by
  apply host_sim_bind
  · exact host_sim_pop_args 1
  intro a
  unfold burnH
  exact host_sim_with_gas _

theorem actual_gas_sim (call : HM Unit) (hc : hostCall "gas" = some call) : HostSim call call := by
  have he : hostCall "gas" = some (do let a ← popArgs 1; burnH (a[0] * 822756)) := rfl
  rw [he] at hc
  cases Option.some.inj hc
  exact gas_dispatch_sim 822756

theorem deprecated_dispatch_sim (n : Nat) (message : String) :
    HostSim (do let _ ← popArgs n; (hErr message : HM Unit))
      (do let _ ← popArgs n; (hErr message : HM Unit)) := by
  apply host_sim_bind
  · exact host_sim_pop_args n
  intro _
  exact host_sim_error _

theorem actual_iterator_prefix_sim (call : HM Unit)
    (hc : hostCall "storage_iter_prefix" = some call) : HostSim call call := by
  have he : hostCall "storage_iter_prefix" = some (do
      let _ ← popArgs 2
      hErr "Deprecated { method_name: \"storage_iter_prefix\" }") := rfl
  rw [he] at hc
  cases Option.some.inj hc
  exact deprecated_dispatch_sim 2 _

theorem actual_iterator_range_sim (call : HM Unit)
    (hc : hostCall "storage_iter_range" = some call) : HostSim call call := by
  have he : hostCall "storage_iter_range" = some (do
      let _ ← popArgs 4
      hErr "Deprecated { method_name: \"storage_iter_range\" }") := rfl
  rw [he] at hc
  cases Option.some.inj hc
  exact deprecated_dispatch_sim 4 _

theorem actual_iterator_next_sim (call : HM Unit)
    (hc : hostCall "storage_iter_next" = some call) : HostSim call call := by
  have he : hostCall "storage_iter_next" = some (do
      let _ ← popArgs 3
      hErr "Deprecated { method_name: \"storage_iter_next\" }") := rfl
  rw [he] at hc
  cases Option.some.inj hc
  exact deprecated_dispatch_sim 3 _

end NearCompression
