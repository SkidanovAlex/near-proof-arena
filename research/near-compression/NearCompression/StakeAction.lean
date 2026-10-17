import NearCompression.RestrictedKey

/-! Staking action construction, including charged invalid-key rejection. -/
namespace NearCompression
open NearSpecV3.Wasm

def stakeActionCode (base : Cost) (fee : Fee3)
    (readAmount : Nat → HM Nat) (read : Nat → Nat → HM ByteArray) : HM Unit := do
  let a ← popArgs 4
  payBaseH base
  let amount ← readAmount a[1]
  let pk ← read a[3] a[2]
  let (r, sir) ← promiseReceiptH a[0]
  payActionBaseH fee sir
  if !pkValid pk then hErr "InvalidPublicKey"
  let _ ← pushAction { text := s!"ST@{r}:{amount}:{hexStr pk}" }

theorem stake_action_code_sim (base : Cost) (fee : Fee3)
    (readAmount : Nat → HM Nat) (read : Nat → Nat → HM ByteArray)
    (amountSim : ∀ ptr, HostSim (readAmount ptr) (readAmount ptr))
    (readSim : ∀ ptr len, HostSim (read ptr len) (read ptr len)) :
    HostSim (stakeActionCode base fee readAmount read) (stakeActionCode base fee readAmount read) := by
  unfold stakeActionCode
  apply host_sim_bind
  · exact host_sim_pop_args 4
  intro a
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · exact amountSim _
  intro amount
  apply host_sim_bind
  · exact readSim _ _
  intro pk
  apply host_sim_bind
  · exact host_sim_promise_receipt _
  intro receipt
  apply host_sim_bind
  · exact host_sim_action_base _ _
  intro _
  dsimp only
  split
  · simp only [host_error_bind]; exact host_sim_error _
  · apply host_sim_bind
    · exact host_sim_push_action _
    intro _
    exact host_sim_pure ()

theorem actual_stake_action_code : hostCall "promise_batch_action_stake" =
    some (stakeActionCode C.base F.stake getU128H memOrRegH) := by rfl

theorem actual_stake_action_sim (call : HM Unit)
    (hc : hostCall "promise_batch_action_stake" = some call) : HostSim call call := by
  rw [actual_stake_action_code] at hc
  cases Option.some.inj hc
  with_reducible exact stake_action_code_sim C.base F.stake getU128H memOrRegH host_sim_get_u128 host_sim_mem_or_reg

end NearCompression
