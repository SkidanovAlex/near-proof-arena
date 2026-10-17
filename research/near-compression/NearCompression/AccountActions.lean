import NearCompression.StakeAction

/-! Beneficiary account actions and refund routing retain distinct failure behavior. -/
namespace NearCompression
open NearSpecV3.Wasm

def refundBody (idx : Nat) (account : String) : HM Unit := do
  match (← get).promises[idx]? with
  | none => hErr s!"InvalidPromiseIndex \{ promise_idx: {idx} }"
  | some (.joint _) => hErr "CannotSetRefundToOnJointPromise"
  | some (.receipt r) => let _ ← pushAction { text := s!"RT@{r}:{account}" }

theorem refund_body_sim (idx : Nat) (account : String) :
    HostSim (refundBody idx account) (refundBody idx account) := by
  unfold refundBody
  apply host_sim_get_bind
  intro s t h
  have hp : s.promises = t.promises := by have he := congrArg St.promises h.core; exact he
  rw [hp]
  split
  · exact host_sim_error _ s t h
  · exact host_sim_error _ s t h
  · apply host_bind_equiv
    · exact host_sim_push_action _ s t h
    intro _ u v huv
    exact host_sim_pure () u v huv

def deleteAccountBody (fee : Fee3) (idx : Nat) (account : String) : HM Unit := do
  let (r, sir) ← promiseReceiptH idx
  payActionBaseH fee sir
  let _ ← pushAction { text := s!"DA@{r}:{account}" }

theorem delete_account_body_sim (fee : Fee3) (idx : Nat) (account : String) :
    HostSim (deleteAccountBody fee idx account) (deleteAccountBody fee idx account) := by
  unfold deleteAccountBody
  apply host_sim_bind
  · exact host_sim_promise_receipt _
  intro receipt
  apply host_sim_bind
  · exact host_sim_action_base _ _
  intro _
  apply host_sim_bind
  · exact host_sim_push_action _
  intro _
  exact host_sim_pure ()

def accountActionCode (base : Cost) (readAccount : Nat → Nat → HM String)
    (body : Nat → String → HM Unit) : HM Unit := do
  let a ← popArgs 3
  payBaseH base
  let account ← readAccount a[1] a[2]
  body a[0] account

theorem account_action_code_sim (base : Cost) (readAccount : Nat → Nat → HM String)
    (body : Nat → String → HM Unit)
    (readerSim : ∀ len ptr, HostSim (readAccount len ptr) (readAccount len ptr))
    (bodySim : ∀ idx account, HostSim (body idx account) (body idx account)) :
    HostSim (accountActionCode base readAccount body) (accountActionCode base readAccount body) := by
  unfold accountActionCode
  apply host_sim_bind
  · exact host_sim_pop_args 3
  intro a
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · exact readerSim _ _
  intro account
  exact bodySim a[0] account

theorem actual_refund_code : hostCall "promise_set_refund_to" =
    some (accountActionCode C.base readAccountIdH refundBody) := by rfl

theorem actual_delete_account_code : hostCall "promise_batch_action_delete_account" =
    some (accountActionCode C.base readAccountIdH (deleteAccountBody F.deleteAccount)) := by rfl

theorem actual_refund_sim (call : HM Unit)
    (hc : hostCall "promise_set_refund_to" = some call) : HostSim call call := by
  rw [actual_refund_code] at hc
  cases Option.some.inj hc
  with_reducible exact account_action_code_sim C.base readAccountIdH refundBody host_sim_read_account_id refund_body_sim

theorem actual_delete_account_sim (call : HM Unit)
    (hc : hostCall "promise_batch_action_delete_account" = some call) : HostSim call call := by
  rw [actual_delete_account_code] at hc
  cases Option.some.inj hc
  with_reducible exact account_action_code_sim C.base readAccountIdH (deleteAccountBody F.deleteAccount) host_sim_read_account_id (delete_account_body_sim F.deleteAccount)

end NearCompression
