import NearCompression.AbortHost

/-! Execution preservation for the actual Ed25519 host, including its early
encoding rejection. No signature-security assumption is made or proved here. -/
namespace NearCompression
open NearSpecV3.Wasm

def ed25519Code (base byte : Cost) (read : Nat → Nat → HM ByteArray) : HM Unit := do
  let a ← popArgs 6
  payBaseH base
  let sig ← read a[1] a[0]
  if h : sig.size ≠ 64 then hErr "Ed25519VerifyInvalidInput { msg: \"invalid signature length\" }" else
  if sig[63]'(by omega) &&& 0xE0 ≠ 0 then pushRet 0 else
  let msg ← read a[3] a[2]
  payPerH byte msg.size
  let pk ← read a[5] a[4]
  if pk.size ≠ 32 then hErr "Ed25519VerifyInvalidInput { msg: \"invalid public key length\" }"
  pushRet (if NearSpecV3.Ed25519.verify pk.toList sig.toList msg.toList then 1 else 0)

theorem ed25519_code_sim (base byte : Cost) (read : Nat → Nat → HM ByteArray)
    (readSim : ∀ ptr len, HostSim (read ptr len) (read ptr len)) :
    HostSim (ed25519Code base byte read) (ed25519Code base byte read) := by
  unfold ed25519Code
  apply host_sim_bind
  · exact host_sim_pop_args 6
  intro args
  apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · exact readSim args[1] args[0]
  intro sig
  dsimp only
  split
  · exact host_sim_error _
  · split
    · exact host_sim_push_ret 0 true
    · apply host_sim_bind
      · exact readSim args[3] args[2]
      intro msg
      apply host_sim_bind
      · unfold payPerH
        exact host_sim_with_gas _
      intro _
      apply host_sim_bind
      · exact readSim args[5] args[4]
      intro pk
      split
      · apply host_sim_bind
        · exact host_sim_error _
        intro _
        exact host_sim_push_ret _ true
      · exact host_sim_push_ret _ true

theorem actual_ed25519_code : hostCall "ed25519_verify" =
    some (ed25519Code C.ed25519VerifyBase C.ed25519VerifyByte memOrRegH) := by rfl

theorem actual_ed25519_sim (call : HM Unit) (hc : hostCall "ed25519_verify" = some call) :
    HostSim call call := by
  rw [actual_ed25519_code] at hc
  cases Option.some.inj hc
  with_reducible exact ed25519_code_sim C.ed25519VerifyBase C.ed25519VerifyByte memOrRegH host_sim_mem_or_reg

end NearCompression
