import NearCompression.FunctionAction

/-! Receipt creation followed by a function-call action, preserving intermediate failures. -/
namespace NearCompression
open NearSpecV3.Wasm

def createReceiptThen (account : String) (next : Nat → HM Unit) : HM Unit := do
  payNewReceiptH (account = (← get).ctx.currentAccount) #[]
  let r ← pushAction { text := s!"CR()>{account}", receiver := some account }
  let pi ← pushPromiseH (.receipt r)
  next pi

theorem create_receipt_then_sim (account : String) (next : Nat → HM Unit)
    (nextSim : ∀ pi, HostSim (next pi) (next pi)) :
    HostSim (createReceiptThen account next) (createReceiptThen account next) := by
  unfold createReceiptThen
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
  exact nextSim promise u v huv

def dependentReceiptThen (account : String) (idx : Nat) (next : Nat → HM Unit) : HM Unit := do
  let s ← get
  let deps ← match s.promises[idx]? with
    | none => hErr s!"InvalidPromiseIndex \{ promise_idx: {idx} }"
    | some (.receipt r) => pure #[r]
    | some (.joint rs) => pure rs
  payNewReceiptH (account = s.ctx.currentAccount) (deps.map fun r => receiptReceiver s r = account)
  let r ← pushAction { text := s!"CR({",".intercalate (deps.toList.map toString)})>{account}",
                       receiver := some account }
  thenDataIdsH deps.size
  let pi ← pushPromiseH (.receipt r)
  next pi

theorem dependent_receipt_then_sim (account : String) (idx : Nat) (next : Nat → HM Unit)
    (nextSim : ∀ pi, HostSim (next pi) (next pi)) :
    HostSim (dependentReceiptThen account idx next) (dependentReceiptThen account idx next) := by
  unfold dependentReceiptThen
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
    exact nextSim promise u v huv
  )

def callAndReturn (mlen mptr alen aptr amount gas pi : Nat) : HM Unit := do
  functionCallActionH pi mlen mptr alen aptr amount gas 0
  pushRet pi

theorem call_and_return_sim (mlen mptr alen aptr amount gas pi : Nat) :
    HostSim (callAndReturn mlen mptr alen aptr amount gas pi)
      (callAndReturn mlen mptr alen aptr amount gas pi) := by
  unfold callAndReturn
  with_reducible
    exact host_sim_bind
      (functionCallActionH pi mlen mptr alen aptr amount gas 0)
      (functionCallActionH pi mlen mptr alen aptr amount gas 0)
      (fun _ => pushRet pi) (fun _ => pushRet pi)
      (host_sim_function_action pi mlen mptr alen aptr amount gas 0)
      (fun _ => host_sim_push_ret pi true)


def promiseCreateCode (base : Cost) (readAccount : Nat → Nat → HM String) : HM Unit := do
  let a ← popArgs 8
  payBaseH base
  let account ← readAccount a[0] a[1]
  createReceiptThen account (callAndReturn a[2] a[3] a[4] a[5] a[6] a[7])

theorem promise_create_code_sim (base : Cost) (readAccount : Nat → Nat → HM String)
    (readerSim : ∀ len ptr, HostSim (readAccount len ptr) (readAccount len ptr)) :
    HostSim (promiseCreateCode base readAccount) (promiseCreateCode base readAccount) := by
  unfold promiseCreateCode
  apply host_sim_bind
  · exact host_sim_pop_args 8
  intro a
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · exact readerSim _ _
  intro account
  with_reducible apply create_receipt_then_sim account
  intro pi
  with_reducible exact call_and_return_sim a[2] a[3] a[4] a[5] a[6] a[7] pi

theorem actual_promise_create_code : hostCall "promise_create" =
    some (promiseCreateCode C.base readAccountIdH) := by rfl

theorem actual_promise_create_sim (call : HM Unit)
    (hc : hostCall "promise_create" = some call) : HostSim call call := by
  rw [actual_promise_create_code] at hc
  cases Option.some.inj hc
  with_reducible exact promise_create_code_sim C.base readAccountIdH host_sim_read_account_id

def promiseThenCode (base : Cost) (readAccount : Nat → Nat → HM String) : HM Unit := do
  let a ← popArgs 9
  payBaseH base
  let account ← readAccount a[1] a[2]
  dependentReceiptThen account a[0] (callAndReturn a[3] a[4] a[5] a[6] a[7] a[8])

theorem promise_then_code_sim (base : Cost) (readAccount : Nat → Nat → HM String)
    (readerSim : ∀ len ptr, HostSim (readAccount len ptr) (readAccount len ptr)) :
    HostSim (promiseThenCode base readAccount) (promiseThenCode base readAccount) := by
  unfold promiseThenCode
  apply host_sim_bind
  · exact host_sim_pop_args 9
  intro a
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · exact readerSim _ _
  intro account
  with_reducible apply dependent_receipt_then_sim account a[0]
  intro pi
  with_reducible exact call_and_return_sim a[3] a[4] a[5] a[6] a[7] a[8] pi

theorem actual_promise_then_code : hostCall "promise_then" =
    some (promiseThenCode C.base readAccountIdH) := by rfl

theorem actual_promise_then_sim (call : HM Unit)
    (hc : hostCall "promise_then" = some call) : HostSim call call := by
  rw [actual_promise_then_code] at hc
  cases Option.some.inj hc
  with_reducible exact promise_then_code_sim C.base readAccountIdH host_sim_read_account_id

end NearCompression
