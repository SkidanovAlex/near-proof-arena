import NearCompression.PromiseResults

/-! Receipt creation prerequisites and actual promise_batch_create dispatch.
Promise-limit failures retain the newly appended promise, as in the interpreter. -/
namespace NearCompression
open NearSpecV3.Wasm

def accountIdCode (base byte : Cost) (read : Nat → Nat → HM ByteArray) (len ptr : Nat) : HM String := do
  let buf ← read ptr len
  payBaseH base
  payPerH byte buf.size
  match String.fromUTF8? buf with
  | none => hErr "BadUTF8"
  | some str => if validAccountId str then pure str else hErr "InvalidAccountId"

theorem account_id_code_sim (base byte : Cost) (read : Nat → Nat → HM ByteArray)
    (readSim : ∀ ptr len, HostSim (read ptr len) (read ptr len)) (len ptr : Nat) :
    HostSim (accountIdCode base byte read len ptr) (accountIdCode base byte read len ptr) := by
  unfold accountIdCode
  apply host_sim_bind
  · exact readSim ptr len
  intro buf
  apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · unfold payPerH
    exact host_sim_with_gas _
  intro _
  repeat' (split <;> (try simp_all only []))
  all_goals first | exact host_sim_error _ | exact host_sim_pure _

theorem host_sim_read_account_id (len ptr : Nat) : HostSim (readAccountIdH len ptr) (readAccountIdH len ptr) := by
  change HostSim (accountIdCode C.utf8DecodingBase C.utf8DecodingByte memOrRegH len ptr)
    (accountIdCode C.utf8DecodingBase C.utf8DecodingByte memOrRegH len ptr)
  with_reducible exact account_id_code_sim C.utf8DecodingBase C.utf8DecodingByte memOrRegH host_sim_mem_or_reg len ptr

theorem host_sim_push_action (action : MAct) : HostSim (pushAction action) (pushAction action) := by
  intro s t h
  unfold pushAction
  rw [host_get_bind_run, host_get_bind_run]
  have ha : s.actions = t.actions := by have he := congrArg St.actions h.core; exact he
  rw [ha]
  exact ⟨rfl, congrArg (fun s : St => { s with actions := t.actions.push action }) h.core, h.real⟩

theorem state_equiv_set_promises (s t : St) (h : StateEquivalent s t) (promises : Array PromiseV) :
    StateEquivalent { s with promises } { t with promises } :=
  ⟨congrArg (fun s : St => { s with promises }) h.core, h.real⟩

theorem host_sim_push_promise (promise : PromiseV) : HostSim (pushPromiseH promise) (pushPromiseH promise) := by
  intro s t h
  unfold pushPromiseH
  rw [host_get_bind_run, host_get_bind_run]
  have hp : s.promises = t.promises := by have he := congrArg St.promises h.core; exact he
  rw [hp]
  apply host_set_then_equiv s t _ _ (state_equiv_set_promises s t h (t.promises.push promise))
  split
  · apply host_sim_bind
    · exact host_sim_error _
    intro _
    exact host_sim_pure _
  · exact host_sim_pure _

theorem host_sim_new_receipt (sir : Bool) (deps : Array Bool) :
    HostSim (payNewReceiptH sir deps) (payNewReceiptH sir deps) := by
  unfold payNewReceiptH payActionH
  exact host_sim_with_gas _

def createReceiptCode (account : String) : HM Unit := do
  payNewReceiptH (account = (← get).ctx.currentAccount) #[]
  let r ← pushAction { text := s!"CR()>{account}", receiver := some account }
  pushRet (← pushPromiseH (.receipt r))

theorem create_receipt_code_sim (account : String) :
    HostSim (createReceiptCode account) (createReceiptCode account) := by
  unfold createReceiptCode
  apply host_sim_get_bind
  intro s t h
  have hc : s.ctx = t.ctx := by have he := congrArg St.ctx h.core; exact he
  rw [hc]
  apply host_bind_equiv
  · exact host_sim_new_receipt _ #[] s t h
  intro _ u v huv
  apply host_bind_equiv
  · exact host_sim_push_action _ u v huv
  intro receipt u v huv
  apply host_bind_equiv
  · exact host_sim_push_promise (.receipt receipt) u v huv
  intro promise u v huv
  exact host_sim_push_ret promise true u v huv

def batchCreateCode (base : Cost) (readAccount : Nat → Nat → HM String) : HM Unit := do
  let a ← popArgs 2
  payBaseH base
  let account ← readAccount a[0] a[1]
  createReceiptCode account

theorem batch_create_code_sim (base : Cost) (readAccount : Nat → Nat → HM String)
    (readerSim : ∀ len ptr, HostSim (readAccount len ptr) (readAccount len ptr)) :
    HostSim (batchCreateCode base readAccount) (batchCreateCode base readAccount) := by
  unfold batchCreateCode
  apply host_sim_bind
  · exact host_sim_pop_args 2
  intro a
  apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · exact readerSim a[0] a[1]
  intro account
  exact create_receipt_code_sim account

theorem actual_batch_create_code : hostCall "promise_batch_create" =
    some (batchCreateCode C.base readAccountIdH) := by rfl

theorem actual_batch_create_sim (call : HM Unit) (hc : hostCall "promise_batch_create" = some call) :
    HostSim call call := by
  rw [actual_batch_create_code] at hc
  cases Option.some.inj hc
  with_reducible exact batch_create_code_sim C.base readAccountIdH host_sim_read_account_id

end NearCompression
