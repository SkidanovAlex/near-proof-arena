import NearCompression.Utf16

namespace NearCompression
open NearSpecV3.Wasm

def decodedLogCode (base logBase logByte : Cost) (decode : Nat → Nat → HM String) : HM Unit := do
  let a ← popArgs 2
  payBaseH base
  checkCanLogH
  let msg ← decode a[0] a[1]
  payBaseH logBase
  payPerH logByte msg.utf8ByteSize
  pushLogH msg

theorem decoded_log_code_sim (base logBase logByte : Cost) (decode : Nat → Nat → HM String)
    (decoderSim : ∀ len ptr, HostSim (decode len ptr) (decode len ptr)) :
    HostSim (decodedLogCode base logBase logByte decode) (decodedLogCode base logBase logByte decode) := by
  unfold decodedLogCode
  apply host_sim_bind
  · exact host_sim_pop_args 2
  intro args
  apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · exact host_sim_check_can_log
  intro _
  apply host_sim_bind
  · exact decoderSim args[0] args[1]
  intro msg
  apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · unfold payPerH
    exact host_sim_with_gas _
  intro _
  exact host_sim_push_log msg

theorem actual_log_utf16_code : hostCall "log_utf16" =
    some (decodedLogCode C.base C.logBase C.logByte utf16H) := by rfl

theorem actual_log_utf16_sim (call : HM Unit) (hc : hostCall "log_utf16" = some call) :
    HostSim call call := by
  rw [actual_log_utf16_code] at hc
  cases Option.some.inj hc
  with_reducible exact decoded_log_code_sim C.base C.logBase C.logByte utf16H host_sim_utf16

end NearCompression
