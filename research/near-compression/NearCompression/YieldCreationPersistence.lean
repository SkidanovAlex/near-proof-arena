import NearCompression.YieldPersistence

/-! Yield creation and explicit-ID resolution retain real storage on every exit. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem host_real_set_state (s : St) (hs : s.real.isSome = true) :
    HostKeepsReal (set s) := by
  intro _ _
  exact hs

theorem yield_receipt_then_keeps_real (next : ByteArray → Nat → HM Unit)
    (nextReal : ∀ did r, HostKeepsReal (next did r)) :
    HostKeepsReal (yieldReceiptThen next) := by
  unfold yieldReceiptThen
  apply host_real_get_bind
  intro s hs
  dsimp only
  simp only [hs, ite_true]
  apply host_real_bind
  · exact host_real_set_state _ hs
  · intro _
    apply host_real_bind
    · exact host_real_put _ _
    intro _
    apply host_real_bind
    · exact host_real_push_action _
    intro r
    exact nextReal _ r
  · exact hs

theorem append_yield_action_keeps_real (m a : ByteArray) (r gas weight : Nat) :
    HostKeepsReal (appendYieldAction m a r gas weight) := by
  unfold appendYieldAction
  apply host_real_get_bind
  intro s hs
  split
  · simp only [host_error_bind]; exact hs
  · apply host_real_bind
    · exact host_real_push_action _
    · intro _; exact host_real_pure ()
    · exact hs

theorem yield_id_receipt_then_keeps_real (yid : ByteArray) (next : Nat → HM Unit)
    (nextReal : ∀ r, HostKeepsReal (next r)) :
    HostKeepsReal (yieldIdReceiptThen yid next) := by
  unfold yieldIdReceiptThen
  apply host_real_get_bind
  intro s hs
  dsimp only
  simp only [hs, ite_true]
  apply host_real_bind
  · exact host_real_has _
  · intro dup
    split
    · exact host_real_push_ret _ true
    · apply host_real_bind
      · exact host_real_set_state _ hs
      intro _
      apply host_real_bind
      · exact host_real_put _ _
      intro _
      apply host_real_bind
      · exact host_real_put _ _
      intro _
      apply host_real_bind
      · exact host_real_put _ _
      intro _
      apply host_real_bind
      · exact host_real_push_action _
      intro r
      exact nextReal r
  · exact hs

theorem resume_resolved_id_keeps_real (acct : String) (did payload : ByteArray) :
    HostKeepsReal (resumeResolvedId acct did payload) := by
  unfold resumeResolvedId
  apply host_real_bind
  · exact host_real_has _
  intro first
  apply host_real_bind
  · exact host_real_has _
  intro second
  dsimp only
  split
  · apply host_real_bind
    · exact host_real_push_action _
    intro _
    apply host_real_bind
    · exact host_real_put _ _
    intro _
    exact host_real_push_ret _ false
  · exact host_real_push_ret _ false

theorem yield_id_resume_body_keeps_real (yid payload : ByteArray) :
    HostKeepsReal (yieldIdResumeBody yid payload) := by
  unfold yieldIdResumeBody
  apply host_real_get_bind
  intro s hs
  simp only [hs, ite_true]
  apply host_real_get_bind
  · intro u hu
    apply host_real_bind
    · exact host_real_get _
    · intro resolved
      cases resolved with
      | none => exact host_real_push_ret 0 false
      | some did => exact resume_resolved_id_keeps_real _ did payload
    · exact hu
  · exact hs

theorem yield_create_finish_keeps_real (fee byteFee : Fee3) (m args : ByteArray)
    (gas weight reg : Nat) (did : ByteArray) (r : Nat) :
    HostKeepsReal (yieldCreateFinish fee byteFee m args gas weight reg did r) := by
  unfold yieldCreateFinish
  apply host_real_bind
  · exact host_real_push_promise _
  intro pi
  apply host_real_bind
  · exact host_real_action_base _ _
  intro _
  apply host_real_bind
  · exact host_real_action_byte _ _ _
  intro _
  apply host_real_bind
  · exact append_yield_action_keeps_real _ _ _ _ _
  intro _
  with_reducible
    exact host_real_bind (regSetH reg did)
      (fun _ => pushRet pi)
      (host_real_reg_set reg did true) (fun _ => host_real_push_ret pi true)

theorem yield_create_code_keeps_real (base createBase createByte : Cost) (fee byteFee : Fee3) (newReceipt : HM Unit)
    (receiptSim : HostKeepsReal newReceipt)
    (read : Nat → Nat → HM ByteArray)
    (readSim : ∀ ptr len, HostKeepsReal (read ptr len)) :
    HostKeepsReal (yieldCreateCode base createBase createByte fee byteFee newReceipt read) := by
  unfold yieldCreateCode
  apply host_real_bind
  · exact host_real_pop_args 7
  intro a
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact readSim _ _
  intro m
  dsimp only
  split
  · simp only [host_error_bind]; exact host_real_throw _
  · apply host_real_bind
    · exact readSim _ _
    intro args
    apply host_real_bind
    · unfold payPerH; exact host_real_with_gas _
    intro _
    apply host_real_bind
    · exact host_real_with_gas _
    intro _
    apply host_real_bind
    · exact receiptSim
    intro _
    apply yield_receipt_then_keeps_real
    intro did r
    exact yield_create_finish_keeps_real fee byteFee m args a[4] a[5] a[6] did r

theorem actual_yield_create_keeps_real (call : HM Unit)
    (hc : hostCall "promise_yield_create" = some call) : HostKeepsReal call := by
  rw [actual_yield_create_code] at hc
  cases Option.some.inj hc
  with_reducible exact yield_create_code_keeps_real C.base C.yieldCreateBase C.yieldCreateByte F.functionCall F.functionCallByte (payNewReceiptH true #[true]) (host_real_new_receipt true #[true]) memOrRegH host_real_mem_or_reg

theorem yield_id_finish_keeps_real (fee byteFee : Fee3) (newReceipt : HM Unit)
    (receiptSim : HostKeepsReal newReceipt) (m args : ByteArray)
    (amount gas weight r : Nat) :
    HostKeepsReal (yieldIdFinish fee byteFee newReceipt m args amount gas weight r) := by
  unfold yieldIdFinish
  apply host_real_bind
  · exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact receiptSim
  intro _
  apply host_real_bind
  · exact host_real_push_promise _
  intro pi
  apply host_real_bind
  · exact host_real_action_base _ _
  intro _
  apply host_real_bind
  · exact host_real_action_byte _ _ _
  intro _
  apply host_real_bind
  · exact host_real_action_deposit _
  intro _
  apply host_real_bind
  · exact append_function_keeps_real _ _ _ _ _ _
  intro _
  exact host_real_push_ret pi true

theorem yield_id_code_keeps_real (base idBase byte : Cost) (fee byteFee : Fee3) (newReceipt : HM Unit)
    (readAmount : Nat → HM Nat) (read : Nat → Nat → HM ByteArray)
    (receiptSim : HostKeepsReal newReceipt)
    (amountSim : ∀ ptr, HostKeepsReal (readAmount ptr))
    (readSim : ∀ ptr len, HostKeepsReal (read ptr len)) (a : Vector Nat 9) :
    HostKeepsReal (yieldIdCode base idBase byte fee byteFee newReceipt readAmount read a) := by
  unfold yieldIdCode
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
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
    intro args
    apply host_real_bind
    · exact readSim _ _
    intro yid
    split
    · simp only [host_error_bind]; exact host_real_throw _
    · apply host_real_bind
      · unfold payPerH; exact host_real_with_gas _
      intro _
      apply yield_id_receipt_then_keeps_real
      intro r
      exact yield_id_finish_keeps_real fee byteFee newReceipt receiptSim m args amount a[5] a[6] r

theorem host_real_yield_id (a : Vector Nat 9) : HostKeepsReal (yieldCreateWithIdH a) := by
  rw [actual_yield_id_code]
  with_reducible exact yield_id_code_keeps_real C.base C.yieldCreateWithIdBase C.yieldCreateByte F.functionCall F.functionCallByte (payNewReceiptH true #[true]) getU128H memOrRegH (host_real_new_receipt true #[true]) host_real_get_u128 host_real_mem_or_reg a

theorem actual_yield_id_keeps_real (call : HM Unit)
    (hc : hostCall "promise_yield_create_with_id" = some call) : HostKeepsReal call := by
  have he : hostCall "promise_yield_create_with_id" = some (do yieldCreateWithIdH (← popArgs 9)) := rfl
  rw [he] at hc
  cases Option.some.inj hc
  apply host_real_bind
  · exact host_real_pop_args 9
  intro a
  with_reducible exact host_real_yield_id a

theorem yield_id_resume_code_keeps_real (base resumeBase resumeByte : Cost)
    (read : Nat → Nat → HM ByteArray)
    (readSim : ∀ ptr len, HostKeepsReal (read ptr len)) :
    HostKeepsReal (yieldIdResumeCode base resumeBase resumeByte read) := by
  unfold yieldIdResumeCode
  apply host_real_bind
  · exact host_real_pop_args 4
  intro a
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · unfold payPerH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact readSim _ _
  intro did
  apply host_real_bind
  · exact readSim _ _
  intro payload
  dsimp only
  split
  · simp only [host_error_bind]; exact host_real_throw _
  · split
    · simp only [host_error_bind]; exact host_real_throw _
    · exact yield_id_resume_body_keeps_real did payload

theorem actual_yield_id_resume_keeps_real (call : HM Unit)
    (hc : hostCall "promise_yield_resume_with_yield_id" = some call) : HostKeepsReal call := by
  rw [actual_yield_id_resume_code] at hc
  cases Option.some.inj hc
  with_reducible exact yield_id_resume_code_keeps_real C.base C.yieldResumeBase C.yieldResumeByte memOrRegH host_real_mem_or_reg

end NearCompression
