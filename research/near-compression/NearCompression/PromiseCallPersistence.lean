import NearCompression.FunctionPersistence

/-! Persistent real backend through receipt creation and subsequent function calls. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem create_receipt_keeps_real (account : String) (next : Nat → HM Unit)
    (nextReal : ∀ pi, HostKeepsReal (next pi)) : HostKeepsReal (createReceiptThen account next) := by
  unfold createReceiptThen
  apply host_real_get_bind
  intro s hs
  apply host_real_bind (payNewReceiptH (account = s.ctx.currentAccount) #[])
  · exact host_real_new_receipt _ _
  · intro _
    apply host_real_bind
    · exact host_real_push_action _
    intro receipt
    apply host_real_bind
    · exact host_real_push_promise _
    intro pi
    exact nextReal pi
  · exact hs

theorem dependent_receipt_keeps_real (account : String) (idx : Nat) (next : Nat → HM Unit)
    (nextReal : ∀ pi, HostKeepsReal (next pi)) : HostKeepsReal (dependentReceiptThen account idx next) := by
  unfold dependentReceiptThen
  apply host_real_get_bind
  intro s hs
  dsimp only
  split <;> (
    apply host_real_bind
    · first | exact host_real_throw _ | exact host_real_pure _
    · intro deps
      apply host_real_bind (payNewReceiptH (account = s.ctx.currentAccount) (deps.map fun r => receiptReceiver s r = account))
      · exact host_real_new_receipt _ _
      intro _
      apply host_real_bind
      · exact host_real_push_action _
      intro receipt
      apply host_real_bind
      · exact host_real_then_data_ids _
      intro _
      apply host_real_bind
      · exact host_real_push_promise _
      intro pi
      exact nextReal pi
    · exact hs
  )

theorem call_and_return_keeps_real (mlen mptr alen aptr amount gas pi : Nat) :
    HostKeepsReal (callAndReturn mlen mptr alen aptr amount gas pi) := by
  unfold callAndReturn
  with_reducible
    exact host_real_bind (functionCallActionH pi mlen mptr alen aptr amount gas 0)
      (fun _ => pushRet pi) (host_real_function_action pi mlen mptr alen aptr amount gas 0)
      (fun _ => host_real_push_ret pi true)

theorem promise_create_keeps_real (base : Cost) (readAccount : Nat → Nat → HM String)
    (readReal : ∀ len ptr, HostKeepsReal (readAccount len ptr)) :
    HostKeepsReal (promiseCreateCode base readAccount) := by
  unfold promiseCreateCode
  apply host_real_bind
  · exact host_real_pop_args 8
  intro a
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact readReal a[0] a[1]
  intro account
  with_reducible apply create_receipt_keeps_real account
  intro pi
  with_reducible exact call_and_return_keeps_real a[2] a[3] a[4] a[5] a[6] a[7] pi

theorem actual_promise_create_keeps_real (call : HM Unit)
    (hc : hostCall "promise_create" = some call) : HostKeepsReal call := by
  rw [actual_promise_create_code] at hc
  cases Option.some.inj hc
  with_reducible exact promise_create_keeps_real C.base readAccountIdH host_real_read_account_id

theorem promise_then_keeps_real (base : Cost) (readAccount : Nat → Nat → HM String)
    (readReal : ∀ len ptr, HostKeepsReal (readAccount len ptr)) :
    HostKeepsReal (promiseThenCode base readAccount) := by
  unfold promiseThenCode
  apply host_real_bind
  · exact host_real_pop_args 9
  intro a
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact readReal a[1] a[2]
  intro account
  with_reducible apply dependent_receipt_keeps_real account a[0]
  intro pi
  with_reducible exact call_and_return_keeps_real a[3] a[4] a[5] a[6] a[7] a[8] pi

theorem actual_promise_then_keeps_real (call : HM Unit)
    (hc : hostCall "promise_then" = some call) : HostKeepsReal call := by
  rw [actual_promise_then_code] at hc
  cases Option.some.inj hc
  with_reducible exact promise_then_keeps_real C.base readAccountIdH host_real_read_account_id

theorem batch_create_keeps_real (base : Cost) (readAccount : Nat → Nat → HM String)
    (readReal : ∀ len ptr, HostKeepsReal (readAccount len ptr)) :
    HostKeepsReal (batchCreateCode base readAccount) := by
  unfold batchCreateCode
  apply host_real_bind
  · exact host_real_pop_args 2
  intro a
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact readReal a[0] a[1]
  intro account
  change HostKeepsReal (createReceiptThen account (fun pi => pushRet pi))
  exact create_receipt_keeps_real account _ (fun pi => host_real_push_ret pi true)

theorem actual_batch_create_keeps_real (call : HM Unit)
    (hc : hostCall "promise_batch_create" = some call) : HostKeepsReal call := by
  rw [actual_batch_create_code] at hc
  cases Option.some.inj hc
  with_reducible exact batch_create_keeps_real C.base readAccountIdH host_real_read_account_id

theorem batch_then_keeps_real (base : Cost) (readAccount : Nat → Nat → HM String)
    (readReal : ∀ len ptr, HostKeepsReal (readAccount len ptr)) :
    HostKeepsReal (batchThenCode base readAccount) := by
  unfold batchThenCode
  apply host_real_bind
  · exact host_real_pop_args 3
  intro a
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact readReal a[1] a[2]
  intro account
  change HostKeepsReal (dependentReceiptThen account a[0] (fun pi => pushRet pi))
  exact dependent_receipt_keeps_real account a[0] _ (fun pi => host_real_push_ret pi true)

theorem actual_batch_then_keeps_real (call : HM Unit)
    (hc : hostCall "promise_batch_then" = some call) : HostKeepsReal call := by
  rw [actual_batch_then_code] at hc
  cases Option.some.inj hc
  with_reducible exact batch_then_keeps_real C.base readAccountIdH host_real_read_account_id

end NearCompression
