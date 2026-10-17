import NearCompression.PromiseCallPersistence

/-! Backend persistence for deployment, account creation and staking dispatches. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem deploy_action_code_keeps_real (base : Cost) (fee byteFee : Fee3)
    (read : Nat → Nat → HM ByteArray)
    (readSim : ∀ ptr len, HostKeepsReal (read ptr len)) :
    HostKeepsReal (deployActionCode base fee byteFee read) := by
  unfold deployActionCode
  apply host_real_bind
  · exact host_real_pop_args 3
  intro a
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact readSim _ _
  intro code
  dsimp only
  split
  · simp only [host_error_bind]; exact host_real_throw _
  · apply host_real_bind
    · exact host_real_promise_receipt _
    intro receipt
    apply host_real_bind
    · exact host_real_action_base _ _
    intro _
    apply host_real_bind
    · exact host_real_action_byte _ _ _
    intro _
    apply host_real_bind
    · exact host_real_push_action _
    intro _
    exact host_real_pure ()

theorem actual_deploy_action_keeps_real (call : HM Unit)
    (hc : hostCall "promise_batch_action_deploy_contract" = some call) : HostKeepsReal call := by
  rw [actual_deploy_action_code] at hc
  cases Option.some.inj hc
  with_reducible exact deploy_action_code_keeps_real C.base F.deployContract F.deployContractByte memOrRegH host_real_mem_or_reg

theorem create_account_action_code_keeps_real (base : Cost) (fee : Fee3) :
    HostKeepsReal (createAccountActionCode base fee) := by
  unfold createAccountActionCode
  apply host_real_bind
  · exact host_real_pop_args 1
  intro a
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact host_real_promise_receipt _
  intro receipt
  apply host_real_bind
  · exact host_real_action_base _ _
  intro _
  apply host_real_bind
  · exact host_real_push_action _
  intro _
  exact host_real_pure ()

theorem actual_create_account_action_keeps_real (call : HM Unit)
    (hc : hostCall "promise_batch_action_create_account" = some call) : HostKeepsReal call := by
  rw [actual_create_account_action_code] at hc
  cases Option.some.inj hc
  with_reducible exact create_account_action_code_keeps_real C.base F.createAccount

theorem stake_action_code_keeps_real (base : Cost) (fee : Fee3)
    (readAmount : Nat → HM Nat) (read : Nat → Nat → HM ByteArray)
    (amountSim : ∀ ptr, HostKeepsReal (readAmount ptr))
    (readSim : ∀ ptr len, HostKeepsReal (read ptr len)) :
    HostKeepsReal (stakeActionCode base fee readAmount read) := by
  unfold stakeActionCode
  apply host_real_bind
  · exact host_real_pop_args 4
  intro a
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact amountSim _
  intro amount
  apply host_real_bind
  · exact readSim _ _
  intro pk
  apply host_real_bind
  · exact host_real_promise_receipt _
  intro receipt
  apply host_real_bind
  · exact host_real_action_base _ _
  intro _
  dsimp only
  split
  · simp only [host_error_bind]; exact host_real_throw _
  · apply host_real_bind
    · exact host_real_push_action _
    intro _
    exact host_real_pure ()

theorem actual_stake_action_keeps_real (call : HM Unit)
    (hc : hostCall "promise_batch_action_stake" = some call) : HostKeepsReal call := by
  rw [actual_stake_action_code] at hc
  cases Option.some.inj hc
  with_reducible exact stake_action_code_keeps_real C.base F.stake getU128H memOrRegH host_real_get_u128 host_real_mem_or_reg

theorem transfer_body_keeps_real (amount r : Nat) (sir : Bool) :
    HostKeepsReal (transferBody amount r sir) := by
  unfold transferBody
  apply host_real_get_bind
  intro s hs
  apply host_real_bind
  · unfold payActionH; exact host_real_with_gas _
  · intro _
    apply host_real_bind
    · exact host_real_deduct_balance amount
    intro _
    apply host_real_bind
    · exact host_real_push_action _
    intro _
    exact host_real_pure ()
  · exact hs

theorem transfer_code_keeps_real (base : Cost) (readAmount : Nat → HM Nat)
    (readSim : ∀ ptr, HostKeepsReal (readAmount ptr)) :
    HostKeepsReal (transferCode base readAmount) := by
  unfold transferCode
  apply host_real_bind
  · exact host_real_pop_args 2
  intro a
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact readSim _
  intro amount
  apply host_real_bind
  · exact host_real_promise_receipt _
  intro receipt
  exact transfer_body_keeps_real amount receipt.1 receipt.2

theorem actual_transfer_keeps_real (call : HM Unit)
    (hc : hostCall "promise_batch_action_transfer" = some call) : HostKeepsReal call := by
  rw [actual_transfer_code] at hc
  cases Option.some.inj hc
  with_reducible exact transfer_code_keeps_real C.base getU128H host_real_get_u128

end NearCompression
