import NearCompression.PromiseAnd

/-! Receipt action prerequisites and balance-transfer dispatch. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem host_sim_promise_receipt (idx : Nat) :
    HostSim (promiseReceiptH idx) (promiseReceiptH idx) := by
  unfold promiseReceiptH
  apply host_sim_get_bind
  intro s t h
  have hp : s.promises = t.promises := by have he := congrArg St.promises h.core; exact he
  have ha : s.actions = t.actions := by have he := congrArg St.actions h.core; exact he
  have hc : s.ctx = t.ctx := by have he := congrArg St.ctx h.core; exact he
  simp only [hp, receiptReceiver, ha, hc]
  split <;> first | exact host_sim_error _ s t h | exact host_sim_pure _ s t h

theorem host_sim_action_base (fee : Fee3) (sir : Bool) :
    HostSim (payActionBaseH fee sir) (payActionBaseH fee sir) := by
  unfold payActionBaseH payActionH
  exact host_sim_with_gas _

theorem host_sim_action_byte (fee : Fee3) (n : Nat) (sir : Bool) :
    HostSim (payActionPerByteH fee n sir) (payActionPerByteH fee n sir) := by
  unfold payActionPerByteH
  dsimp only
  split
  · simp only [host_error_bind]
    exact host_sim_error _
  · unfold payActionH
    exact host_sim_with_gas _

theorem host_sim_deduct_balance (amount : Nat) :
    HostSim (deductBalanceH amount) (deductBalanceH amount) := by
  unfold deductBalanceH
  apply host_sim_get_bind
  intro s t h
  have hb : s.balance = t.balance := by have he := congrArg St.balance h.core; exact he
  rw [hb]
  split
  · simp only [host_error_bind]
    exact host_sim_error _ s t h
  · exact ⟨rfl, congrArg (fun s : St => { s with balance := t.balance - amount }) h.core, h.real⟩

def transferBody (amount r : Nat) (sir : Bool) : HM Unit := do
  let (send, exec) := transferFees sir (receiptReceiver (← get) r)
  payActionH send send (send + exec)
  deductBalanceH amount
  let _ ← pushAction { text := s!"TR@{r}:{amount}" }

theorem transfer_body_sim (amount r : Nat) (sir : Bool) :
    HostSim (transferBody amount r sir) (transferBody amount r sir) := by
  unfold transferBody
  apply host_sim_get_bind
  intro s t h
  have ha : s.actions = t.actions := by have he := congrArg St.actions h.core; exact he
  simp only [receiptReceiver, ha]
  apply host_bind_equiv
  · unfold payActionH
    exact host_sim_with_gas _ s t h
  intro _ u v huv
  apply host_bind_equiv
  · exact host_sim_deduct_balance amount u v huv
  intro _ u v huv
  apply host_bind_equiv
  · exact host_sim_push_action _ u v huv
  intro _ u v huv
  exact host_sim_pure () u v huv

def transferCode (base : Cost) (readAmount : Nat → HM Nat) : HM Unit := do
  let a ← popArgs 2
  payBaseH base
  let amount ← readAmount a[1]
  let (r, sir) ← promiseReceiptH a[0]
  transferBody amount r sir

theorem transfer_code_sim (base : Cost) (readAmount : Nat → HM Nat)
    (readSim : ∀ ptr, HostSim (readAmount ptr) (readAmount ptr)) :
    HostSim (transferCode base readAmount) (transferCode base readAmount) := by
  unfold transferCode
  apply host_sim_bind
  · exact host_sim_pop_args 2
  intro a
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · exact readSim _
  intro amount
  apply host_sim_bind
  · exact host_sim_promise_receipt _
  intro receipt
  exact transfer_body_sim amount receipt.1 receipt.2

theorem actual_transfer_code : hostCall "promise_batch_action_transfer" =
    some (transferCode C.base getU128H) := by rfl

theorem actual_transfer_sim (call : HM Unit)
    (hc : hostCall "promise_batch_action_transfer" = some call) : HostSim call call := by
  rw [actual_transfer_code] at hc
  cases Option.some.inj hc
  with_reducible exact transfer_code_sim C.base getU128H host_sim_get_u128

end NearCompression
