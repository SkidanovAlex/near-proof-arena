import NearCompression.ActionTransfer

/-! Function-call action simulation, with exact subsidy and method validation. -/
namespace NearCompression
open NearSpecV3.Wasm

def actionDeposit (amount : Nat) : HM Unit := do
  let s ← get
  if amount = 1 ∧ s.balance = 0 then modify fun s => { s with subsidized := s.subsidized + 1 }
  else deductBalanceH amount

theorem action_deposit_sim (amount : Nat) : HostSim (actionDeposit amount) (actionDeposit amount) := by
  unfold actionDeposit
  apply host_sim_get_bind
  intro s t h
  have hb : s.balance = t.balance := by have he := congrArg St.balance h.core; exact he
  rw [hb]
  split
  · have hu : s.subsidized = t.subsidized := by have he := congrArg St.subsidized h.core; exact he
    change () = () ∧ StateEquivalent { s with subsidized := s.subsidized + 1 }
      { t with subsidized := t.subsidized + 1 }
    rw [hu]
    exact ⟨rfl, congrArg (fun s : St => { s with subsidized := t.subsidized + 1 }) h.core, h.real⟩
  · exact host_sim_deduct_balance amount s t h

def appendFunctionAction (m a : ByteArray) (r amount gas weight : Nat) : HM Unit := do
  if (← get).real.isSome && (String.fromUTF8? m).isNone then hErr "InvalidMethodName"
  let _ ← pushAction { text := s!"FC@{r}:{hexStr m}:{hexStr a}:{amount}:{gas}:{weight}" }

theorem append_function_action_sim (m a : ByteArray) (r amount gas weight : Nat) :
    HostSim (appendFunctionAction m a r amount gas weight)
      (appendFunctionAction m a r amount gas weight) := by
  unfold appendFunctionAction
  apply host_sim_get_bind
  intro s t h
  rw [state_equiv_real_is_some s t h]
  split
  · simp only [host_error_bind]
    exact host_sim_error _ s t h
  · apply host_bind_equiv
    · exact host_sim_push_action _ s t h
    intro _ u v huv
    exact host_sim_pure () u v huv

def functionActionCode (base : Cost) (fee byteFee : Fee3)
    (readAmount : Nat → HM Nat) (read : Nat → Nat → HM ByteArray)
    (idx mlen mptr alen aptr amountPtr gas weight : Nat) : HM Unit := do
  payBaseH base
  let amount ← readAmount amountPtr
  let m ← read mptr mlen
  if m.size = 0 then hErr "EmptyMethodName"
  let a ← read aptr alen
  let (r, sir) ← promiseReceiptH idx
  payActionBaseH fee sir
  payActionPerByteH byteFee (m.size + a.size) sir
  withGas (deduct · 0 gas)
  actionDeposit amount
  appendFunctionAction m a r amount gas weight

theorem function_action_code_sim (base : Cost) (fee byteFee : Fee3)
    (readAmount : Nat → HM Nat) (read : Nat → Nat → HM ByteArray)
    (amountSim : ∀ ptr, HostSim (readAmount ptr) (readAmount ptr))
    (readSim : ∀ ptr len, HostSim (read ptr len) (read ptr len))
    (idx mlen mptr alen aptr amountPtr gas weight : Nat) :
    HostSim (functionActionCode base fee byteFee readAmount read idx mlen mptr alen aptr amountPtr gas weight)
      (functionActionCode base fee byteFee readAmount read idx mlen mptr alen aptr amountPtr gas weight) := by
  unfold functionActionCode
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · exact amountSim _
  intro amount
  apply host_sim_bind
  · exact readSim _ _
  intro m
  dsimp only
  split
  · simp only [host_error_bind]; exact host_sim_error _
  · apply host_sim_bind
    · exact readSim _ _
    intro a
    apply host_sim_bind
    · exact host_sim_promise_receipt _
    intro receipt
    apply host_sim_bind
    · exact host_sim_action_base _ _
    intro _
    apply host_sim_bind
    · exact host_sim_action_byte _ _ _
    intro _
    apply host_sim_bind
    · exact host_sim_with_gas _
    intro _
    apply host_sim_bind
    · exact action_deposit_sim amount
    intro _
    exact append_function_action_sim m a receipt.1 amount gas weight

theorem actual_function_action_code (idx mlen mptr alen aptr amountPtr gas weight : Nat) :
    functionCallActionH idx mlen mptr alen aptr amountPtr gas weight =
      functionActionCode C.base F.functionCall F.functionCallByte getU128H memOrRegH
        idx mlen mptr alen aptr amountPtr gas weight := by
  unfold functionCallActionH functionActionCode actionDeposit appendFunctionAction
  simp only [bind_assoc, host_bind_if, host_error_bind]

theorem host_sim_function_action (idx mlen mptr alen aptr amountPtr gas weight : Nat) :
    HostSim (functionCallActionH idx mlen mptr alen aptr amountPtr gas weight)
      (functionCallActionH idx mlen mptr alen aptr amountPtr gas weight) := by
  rw [actual_function_action_code]
  with_reducible exact function_action_code_sim C.base F.functionCall F.functionCallByte getU128H memOrRegH host_sim_get_u128 host_sim_mem_or_reg idx mlen mptr alen aptr amountPtr gas weight

theorem actual_function_call_sim (call : HM Unit)
    (hc : hostCall "promise_batch_action_function_call" = some call) : HostSim call call := by
  have he : hostCall "promise_batch_action_function_call" = some (do
      let a ← popArgs 7
      functionCallActionH a[0] a[1] a[2] a[3] a[4] a[5] a[6] 0) := rfl
  rw [he] at hc
  cases Option.some.inj hc
  apply host_sim_bind
  · exact host_sim_pop_args 7
  intro a
  with_reducible exact host_sim_function_action a[0] a[1] a[2] a[3] a[4] a[5] a[6] 0

theorem actual_function_call_weight_sim (call : HM Unit)
    (hc : hostCall "promise_batch_action_function_call_weight" = some call) : HostSim call call := by
  have he : hostCall "promise_batch_action_function_call_weight" = some (do
      let a ← popArgs 8
      functionCallActionH a[0] a[1] a[2] a[3] a[4] a[5] a[6] a[7]) := rfl
  rw [he] at hc
  cases Option.some.inj hc
  apply host_sim_bind
  · exact host_sim_pop_args 8
  intro a
  with_reducible exact host_sim_function_action a[0] a[1] a[2] a[3] a[4] a[5] a[6] a[7]

end NearCompression
