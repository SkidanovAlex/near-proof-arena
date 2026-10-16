import NearCompression.HostDataPersistence

/-! Backend persistence across ordered receipt/promise state changes. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem host_real_push_action (action : MAct) : HostKeepsReal (pushAction action) := by
  unfold pushAction
  apply host_real_get_bind
  intro s hs
  exact hs

theorem host_real_push_promise (promise : PromiseV) : HostKeepsReal (pushPromiseH promise) := by
  unfold pushPromiseH
  apply host_real_get_bind
  intro s hs
  split <;> exact hs

theorem host_real_promise_receipt (idx : Nat) : HostKeepsReal (promiseReceiptH idx) := by
  unfold promiseReceiptH
  apply host_real_get_bind
  intro s hs
  split <;> exact hs

theorem host_real_then_data_ids (n : Nat) : HostKeepsReal (thenDataIdsH n) := by
  unfold thenDataIdsH
  apply host_real_modify
  intro s hs
  split <;> exact hs

theorem host_real_deduct_balance (amount : Nat) : HostKeepsReal (deductBalanceH amount) := by
  unfold deductBalanceH
  apply host_real_get_bind
  intro s hs
  split <;> exact hs

theorem host_real_action_deposit (amount : Nat) : HostKeepsReal (actionDeposit amount) := by
  unfold actionDeposit
  apply host_real_get_bind
  intro s hs
  split
  · exact hs
  · exact host_real_deduct_balance amount s hs

theorem host_real_action_base (fee : Fee3) (sir : Bool) : HostKeepsReal (payActionBaseH fee sir) := by
  unfold payActionBaseH payActionH
  exact host_real_with_gas _

theorem host_real_action_byte (fee : Fee3) (n : Nat) (sir : Bool) :
    HostKeepsReal (payActionPerByteH fee n sir) := by
  unfold payActionPerByteH
  dsimp only
  split
  · simp only [host_error_bind]
    exact host_real_throw _
  · unfold payActionH
    exact host_real_with_gas _

theorem host_real_new_receipt (sir : Bool) (deps : Array Bool) :
    HostKeepsReal (payNewReceiptH sir deps) := by
  unfold payNewReceiptH payActionH
  exact host_real_with_gas _

theorem host_real_account_id_code (base byte : Cost) (read : Nat → Nat → HM ByteArray)
    (readReal : ∀ ptr len, HostKeepsReal (read ptr len)) (len ptr : Nat) :
    HostKeepsReal (accountIdCode base byte read len ptr) := by
  unfold accountIdCode
  apply host_real_bind
  · exact readReal _ _
  intro buf
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · unfold payPerH; exact host_real_with_gas _
  intro _
  repeat' split
  all_goals first | exact host_real_pure _ | exact host_real_throw _

theorem host_real_read_account_id (len ptr : Nat) : HostKeepsReal (readAccountIdH len ptr) := by
  change HostKeepsReal (accountIdCode C.utf8DecodingBase C.utf8DecodingByte memOrRegH len ptr)
  with_reducible exact host_real_account_id_code C.utf8DecodingBase C.utf8DecodingByte memOrRegH host_real_mem_or_reg len ptr

theorem key_action_keeps_real (n : Nat) (hn : 2 < n) (base : Cost) (fee : Fee3)
    (read : Nat → Nat → HM ByteArray) (render : Vector Nat n → Nat → ByteArray → String)
    (readReal : ∀ ptr len, HostKeepsReal (read ptr len)) :
    HostKeepsReal (keyActionCode n hn base fee read render) := by
  unfold keyActionCode
  apply host_real_bind
  · exact host_real_pop_args n
  intro a
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact readReal _ _
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

theorem actual_full_access_keeps_real (call : HM Unit)
    (hc : hostCall "promise_batch_action_add_key_with_full_access" = some call) : HostKeepsReal call := by
  rw [actual_full_access_code] at hc
  cases Option.some.inj hc
  with_reducible exact key_action_keeps_real 4 (by decide) C.base F.addFullAccessKey memOrRegH fullAccessText host_real_mem_or_reg

theorem actual_delete_key_keeps_real (call : HM Unit)
    (hc : hostCall "promise_batch_action_delete_key" = some call) : HostKeepsReal call := by
  rw [actual_delete_key_code] at hc
  cases Option.some.inj hc
  with_reducible exact key_action_keeps_real 3 (by decide) C.base F.deleteKey memOrRegH deleteKeyText host_real_mem_or_reg

end NearCompression
