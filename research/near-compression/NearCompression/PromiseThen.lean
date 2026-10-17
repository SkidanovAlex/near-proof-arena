import NearCompression.PromiseCreate

/-! Dependent receipt creation with real-backend data-id accounting. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem host_sim_then_data_ids (n : Nat) : HostSim (thenDataIdsH n) (thenDataIdsH n) := by
  intro s t h
  have hc : s.dataCount = t.dataCount := by have he := congrArg St.dataCount h.core; exact he
  unfold thenDataIdsH
  change (() = () ∧ StateEquivalent
    (if s.real.isSome then { s with dataCount := s.dataCount + n } else s)
    (if t.real.isSome then { t with dataCount := t.dataCount + n } else t))
  rw [state_equiv_real_is_some s t h, hc]
  split
  · exact ⟨rfl, congrArg (fun s : St => { s with dataCount := t.dataCount + n }) h.core, h.real⟩
  · exact ⟨rfl, h⟩

def batchThenBody (account : String) (idx : Nat) : HM Unit := do
  let s ← get
  let deps ← match s.promises[idx]? with
    | none => hErr s!"InvalidPromiseIndex \{ promise_idx: {idx} }"
    | some (.receipt r) => pure #[r]
    | some (.joint rs) => pure rs
  payNewReceiptH (account = s.ctx.currentAccount) (deps.map fun r => receiptReceiver s r = account)
  let r ← pushAction { text := s!"CR({",".intercalate (deps.toList.map toString)})>{account}",
                       receiver := some account }
  thenDataIdsH deps.size
  pushRet (← pushPromiseH (.receipt r))

theorem batch_then_body_sim (account : String) (idx : Nat) :
    HostSim (batchThenBody account idx) (batchThenBody account idx) := by
  unfold batchThenBody
  apply host_sim_get_bind
  intro s t h
  have hp : s.promises = t.promises := by have he := congrArg St.promises h.core; exact he
  have hc : s.ctx = t.ctx := by have he := congrArg St.ctx h.core; exact he
  have ha : s.actions = t.actions := by have he := congrArg St.actions h.core; exact he
  simp only [hp, hc, receiptReceiver, ha]
  split <;> (
    apply host_bind_equiv
    · first | exact host_sim_error _ s t h | exact host_sim_pure _ s t h
    intro deps u v huv
    apply host_bind_equiv
    · exact host_sim_new_receipt _ _ u v huv
    intro _ u v huv
    apply host_bind_equiv
    · exact host_sim_push_action _ u v huv
    intro receipt u v huv
    apply host_bind_equiv
    · exact host_sim_then_data_ids deps.size u v huv
    intro _ u v huv
    apply host_bind_equiv
    · exact host_sim_push_promise (.receipt receipt) u v huv
    intro promise u v huv
    exact host_sim_push_ret promise true u v huv
  )

def batchThenCode (base : Cost) (readAccount : Nat → Nat → HM String) : HM Unit := do
  let a ← popArgs 3
  payBaseH base
  let account ← readAccount a[1] a[2]
  batchThenBody account a[0]

theorem batch_then_code_sim (base : Cost) (readAccount : Nat → Nat → HM String)
    (readerSim : ∀ len ptr, HostSim (readAccount len ptr) (readAccount len ptr)) :
    HostSim (batchThenCode base readAccount) (batchThenCode base readAccount) := by
  unfold batchThenCode
  apply host_sim_bind
  · exact host_sim_pop_args 3
  intro a
  apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · exact readerSim a[1] a[2]
  intro account
  exact batch_then_body_sim account a[0]

theorem actual_batch_then_code : hostCall "promise_batch_then" =
    some (batchThenCode C.base readAccountIdH) := by rfl

theorem actual_batch_then_sim (call : HM Unit) (hc : hostCall "promise_batch_then" = some call) :
    HostSim call call := by
  rw [actual_batch_then_code] at hc
  cases Option.some.inj hc
  with_reducible exact batch_then_code_sim C.base readAccountIdH host_sim_read_account_id

end NearCompression
