import NearCompression.Utf8Hosts

/-! Abort preserves pointer truncation, length-prefix reads, log charges and
terminal panic ordering. Logging may fail before the panic is reached. -/
namespace NearCompression
open NearSpecV3.Wasm

def abortFinish (logBase logByte : Cost) (msg file : String) (line col : Nat) : HM Unit := do
  let message := s!"{msg}, filename: \"{file}\" line: {line} col: {col}"
  payBaseH logBase
  payPerH logByte message.utf8ByteSize
  pushLogH s!"ABORT: {message}"
  guestPanic message

theorem abort_finish_sim (logBase logByte : Cost) (msg file : String) (line col : Nat) :
    HostSim (abortFinish logBase logByte msg file line col) (abortFinish logBase logByte msg file line col) := by
  unfold abortFinish
  apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · unfold payPerH
    exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · exact host_sim_push_log _
  intro _
  exact host_sim_guest_panic _

def abortRead (logBase logByte : Cost) (read : Nat → Nat → HM ByteArray)
    (decode : Nat → Nat → HM String) (mp fp line col : Nat) : HM Unit := do
  checkCanLogH
  let ml := leNat (← read (mp - 4) 4)
  let fl := leNat (← read (fp - 4) 4)
  let msg ← decode ml mp
  let file ← decode fl fp
  abortFinish logBase logByte msg file line col

theorem abort_read_sim (logBase logByte : Cost) (read : Nat → Nat → HM ByteArray)
    (decode : Nat → Nat → HM String)
    (readSim : ∀ ptr len, HostSim (read ptr len) (read ptr len))
    (decodeSim : ∀ len ptr, HostSim (decode len ptr) (decode len ptr)) (mp fp line col : Nat) :
    HostSim (abortRead logBase logByte read decode mp fp line col)
      (abortRead logBase logByte read decode mp fp line col) := by
  unfold abortRead
  apply host_sim_bind
  · exact host_sim_check_can_log
  intro _
  apply host_sim_bind
  · exact readSim _ 4
  intro ml
  apply host_sim_bind
  · exact readSim _ 4
  intro fl
  apply host_sim_bind
  · exact decodeSim _ mp
  intro msg
  apply host_sim_bind
  · exact decodeSim _ fp
  intro file
  exact abort_finish_sim logBase logByte msg file line col

def abortCode (base logBase logByte : Cost) (read : Nat → Nat → HM ByteArray)
    (decode : Nat → Nat → HM String) : HM Unit := do
  let a ← popArgs 4
  payBaseH base
  let (mp, fp, line, col) := (a[0] % 2 ^ 32, a[1] % 2 ^ 32, a[2] % 2 ^ 32, a[3] % 2 ^ 32)
  if mp < 4 ∨ fp < 4 then hErr "BadUTF16"
  abortRead logBase logByte read decode mp fp line col

theorem abort_code_sim (base logBase logByte : Cost) (read : Nat → Nat → HM ByteArray)
    (decode : Nat → Nat → HM String)
    (readSim : ∀ ptr len, HostSim (read ptr len) (read ptr len))
    (decodeSim : ∀ len ptr, HostSim (decode len ptr) (decode len ptr)) :
    HostSim (abortCode base logBase logByte read decode) (abortCode base logBase logByte read decode) := by
  unfold abortCode
  apply host_sim_bind
  · exact host_sim_pop_args 4
  intro a
  apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  dsimp only
  split
  · apply host_sim_bind
    · exact host_sim_error _
    intro _
    exact abort_read_sim logBase logByte read decode readSim decodeSim _ _ _ _
  · exact abort_read_sim logBase logByte read decode readSim decodeSim _ _ _ _

theorem actual_abort_code : hostCall "abort" =
    some (abortCode C.base C.logBase C.logByte readMemH utf16H) := by rfl

theorem actual_abort_sim (call : HM Unit) (hc : hostCall "abort" = some call) : HostSim call call := by
  rw [actual_abort_code] at hc
  cases Option.some.inj hc
  with_reducible exact abort_code_sim C.base C.logBase C.logByte readMemH utf16H host_sim_read_mem host_sim_utf16

end NearCompression
