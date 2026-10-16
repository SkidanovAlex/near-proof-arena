import NearCompression.PromisePersistence

/-! Real-backend persistence through deposits and function-call action dispatch. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem host_real_get_u128_code (base byte : Cost) (ptr : Nat) :
    HostKeepsReal (getU128Code base byte ptr) := by
  unfold getU128Code
  apply host_real_bind
  · exact host_real_charged_read base byte ptr 16
  intro bytes
  exact host_real_pure _

theorem host_real_get_u128 (ptr : Nat) : HostKeepsReal (getU128H ptr) := by
  change HostKeepsReal (getU128Code C.readMemoryBase C.readMemoryByte ptr)
  with_reducible exact host_real_get_u128_code C.readMemoryBase C.readMemoryByte ptr

theorem host_real_set_u128 (ptr value : Nat) : HostKeepsReal (setU128H ptr value) := by
  unfold setU128H
  with_reducible exact host_real_write_mem ptr (natLE value 16)

theorem append_function_keeps_real (m a : ByteArray) (r amount gas weight : Nat) :
    HostKeepsReal (appendFunctionAction m a r amount gas weight) := by
  unfold appendFunctionAction
  apply host_real_get_bind
  intro s hs
  split
  · simp only [host_error_bind]
    exact hs
  · apply host_real_bind
    · exact host_real_push_action _
    · intro _; exact host_real_pure ()
    · exact hs

theorem function_action_keeps_real (base : Cost) (fee byteFee : Fee3)
    (readAmount : Nat → HM Nat) (read : Nat → Nat → HM ByteArray)
    (amountSim : ∀ ptr, HostKeepsReal (readAmount ptr))
    (readSim : ∀ ptr len, HostKeepsReal (read ptr len))
    (idx mlen mptr alen aptr amountPtr gas weight : Nat) :
    HostKeepsReal (functionActionCode base fee byteFee readAmount read idx mlen mptr alen aptr amountPtr gas weight) := by
  unfold functionActionCode
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact amountSim _
  intro amount
  apply host_real_bind
  · exact readSim _ _
  intro m
  dsimp only
  split
  · simp only [host_error_bind]; exact host_real_throw _
  · apply host_real_bind
    · exact readSim _ _
    intro a
    apply host_real_bind
    · exact host_real_promise_receipt _
    intro receipt
    apply host_real_bind
    · exact host_real_action_base _ _
    intro _
    apply host_real_bind
    · exact host_real_action_byte _ _ _
    intro _
    apply host_real_bind
    · exact host_real_with_gas _
    intro _
    apply host_real_bind
    · exact host_real_action_deposit amount
    intro _
    exact append_function_keeps_real m a receipt.1 amount gas weight

theorem host_real_function_action (idx mlen mptr alen aptr amountPtr gas weight : Nat) :
    HostKeepsReal (functionCallActionH idx mlen mptr alen aptr amountPtr gas weight) := by
  rw [actual_function_action_code]
  with_reducible exact function_action_keeps_real C.base F.functionCall F.functionCallByte getU128H memOrRegH host_real_get_u128 host_real_mem_or_reg idx mlen mptr alen aptr amountPtr gas weight

theorem actual_function_call_keeps_real (call : HM Unit)
    (hc : hostCall "promise_batch_action_function_call" = some call) : HostKeepsReal call := by
  have he : hostCall "promise_batch_action_function_call" = some (do
      let a ← popArgs 7
      functionCallActionH a[0] a[1] a[2] a[3] a[4] a[5] a[6] 0) := rfl
  rw [he] at hc
  cases Option.some.inj hc
  apply host_real_bind
  · exact host_real_pop_args 7
  intro a
  with_reducible exact host_real_function_action a[0] a[1] a[2] a[3] a[4] a[5] a[6] 0

theorem actual_function_call_weight_keeps_real (call : HM Unit)
    (hc : hostCall "promise_batch_action_function_call_weight" = some call) : HostKeepsReal call := by
  have he : hostCall "promise_batch_action_function_call_weight" = some (do
      let a ← popArgs 8
      functionCallActionH a[0] a[1] a[2] a[3] a[4] a[5] a[6] a[7]) := rfl
  rw [he] at hc
  cases Option.some.inj hc
  apply host_real_bind
  · exact host_real_pop_args 8
  intro a
  with_reducible exact host_real_function_action a[0] a[1] a[2] a[3] a[4] a[5] a[6] a[7]

end NearCompression
