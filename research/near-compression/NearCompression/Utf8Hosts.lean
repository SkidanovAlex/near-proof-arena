import NearCompression.Utf8

namespace NearCompression
open NearSpecV3.Wasm

theorem actual_log_utf8_code : hostCall "log_utf8" =
    some (decodedLogCode C.base C.logBase C.logByte utf8H) := by rfl

theorem actual_log_utf8_sim (call : HM Unit) (hc : hostCall "log_utf8" = some call) :
    HostSim call call := by
  rw [actual_log_utf8_code] at hc
  cases Option.some.inj hc
  with_reducible exact decoded_log_code_sim C.base C.logBase C.logByte utf8H host_sim_utf8

def decodedPanicCode (base : Cost) (decode : Nat → Nat → HM String) : HM Unit := do
  let a ← popArgs 2
  payBaseH base
  guestPanic (← decode a[0] a[1])

theorem decoded_panic_code_sim (base : Cost) (decode : Nat → Nat → HM String)
    (decoderSim : ∀ len ptr, HostSim (decode len ptr) (decode len ptr)) :
    HostSim (decodedPanicCode base decode) (decodedPanicCode base decode) := by
  unfold decodedPanicCode
  apply host_sim_bind
  · exact host_sim_pop_args 2
  intro args
  apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · exact decoderSim args[0] args[1]
  intro msg
  exact host_sim_guest_panic msg

theorem actual_panic_utf8_code : hostCall "panic_utf8" = some (decodedPanicCode C.base utf8H) := by rfl

theorem actual_panic_utf8_sim (call : HM Unit) (hc : hostCall "panic_utf8" = some call) :
    HostSim call call := by
  rw [actual_panic_utf8_code] at hc
  cases Option.some.inj hc
  with_reducible exact decoded_panic_code_sim C.base utf8H host_sim_utf8

end NearCompression
