import NearCompression.ActionPersistence

/-! Backend persistence for beneficiary and restricted-key action construction. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem refund_body_keeps_real (idx : Nat) (account : String) : HostKeepsReal (refundBody idx account) := by
  unfold refundBody
  apply host_real_get_bind
  intro s hs
  split
  · exact hs
  · exact hs
  · apply host_real_bind
    · exact host_real_push_action _
    · intro _; exact host_real_pure ()
    · exact hs

theorem restricted_key_finish_keeps_real (names : Array ByteArray) (pk : ByteArray)
    (r nonce allowance : Nat) (recv : String) :
    HostKeepsReal (restrictedKeyFinish names pk r nonce allowance recv) := by
  unfold restrictedKeyFinish
  apply host_real_get_bind
  intro s hs
  dsimp only
  split
  · simp only [host_error_bind]; exact hs
  · apply host_real_bind
    · exact host_real_push_action _
    · intro _; exact host_real_pure ()
    · exact hs

theorem delete_account_body_keeps_real (fee : Fee3) (idx : Nat) (account : String) :
    HostKeepsReal (deleteAccountBody fee idx account) := by
  unfold deleteAccountBody
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

theorem account_action_code_keeps_real (base : Cost) (readAccount : Nat → Nat → HM String)
    (body : Nat → String → HM Unit)
    (readerSim : ∀ len ptr, HostKeepsReal (readAccount len ptr))
    (bodySim : ∀ idx account, HostKeepsReal (body idx account)) :
    HostKeepsReal (accountActionCode base readAccount body) := by
  unfold accountActionCode
  apply host_real_bind
  · exact host_real_pop_args 3
  intro a
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact readerSim _ _
  intro account
  exact bodySim a[0] account

theorem actual_refund_keeps_real (call : HM Unit)
    (hc : hostCall "promise_set_refund_to" = some call) : HostKeepsReal call := by
  rw [actual_refund_code] at hc
  cases Option.some.inj hc
  with_reducible exact account_action_code_keeps_real C.base readAccountIdH refundBody host_real_read_account_id refund_body_keeps_real

theorem actual_delete_account_keeps_real (call : HM Unit)
    (hc : hostCall "promise_batch_action_delete_account" = some call) : HostKeepsReal call := by
  rw [actual_delete_account_code] at hc
  cases Option.some.inj hc
  with_reducible exact account_action_code_keeps_real C.base readAccountIdH (deleteAccountBody F.deleteAccount) host_real_read_account_id (delete_account_body_keeps_real F.deleteAccount)

theorem restricted_key_body_keeps_real (fee byteFee : Fee3) (raw pk : ByteArray)
    (idx nonce allowance : Nat) (recv : String) :
    HostKeepsReal (restrictedKeyBody fee byteFee raw pk idx nonce allowance recv) := by
  unfold restrictedKeyBody
  dsimp only
  split <;> (
    apply host_real_bind
    · first | exact host_real_pure _ | exact host_real_throw _
    intro names
    apply host_real_bind
    · exact host_real_promise_receipt _
    intro receipt
    apply host_real_bind
    · exact host_real_action_base _ _
    intro _
    apply host_real_bind
    · exact host_real_action_byte _ _ _
    intro _
    split
    · simp only [host_error_bind]; exact host_real_throw _
    · exact restricted_key_finish_keeps_real names pk receipt.1 nonce allowance recv
  )

theorem restricted_key_code_keeps_real (base : Cost) (fee byteFee : Fee3)
    (read : Nat → Nat → HM ByteArray) (readAmount : Nat → HM Nat)
    (readAccount : Nat → Nat → HM String)
    (readSim : ∀ ptr len, HostKeepsReal (read ptr len))
    (amountSim : ∀ ptr, HostKeepsReal (readAmount ptr))
    (accountSim : ∀ len ptr, HostKeepsReal (readAccount len ptr)) :
    HostKeepsReal (restrictedKeyCode base fee byteFee read readAmount readAccount) := by
  unfold restrictedKeyCode
  apply host_real_bind
  · exact host_real_pop_args 9
  intro a
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact readSim _ _
  intro pk
  apply host_real_bind
  · exact amountSim _
  intro allowance
  apply host_real_bind
  · exact accountSim _ _
  intro recv
  apply host_real_bind
  · exact readSim _ _
  intro raw
  exact restricted_key_body_keeps_real fee byteFee raw pk a[0] a[3] allowance recv

theorem actual_restricted_key_keeps_real (call : HM Unit)
    (hc : hostCall "promise_batch_action_add_key_with_function_call" = some call) : HostKeepsReal call := by
  rw [actual_restricted_key_code] at hc
  cases Option.some.inj hc
  with_reducible exact restricted_key_code_keeps_real C.base F.addFunctionCallKey F.addFunctionCallKeyByte memOrRegH getU128H readAccountIdH host_real_mem_or_reg host_real_get_u128 host_real_read_account_id

end NearCompression
