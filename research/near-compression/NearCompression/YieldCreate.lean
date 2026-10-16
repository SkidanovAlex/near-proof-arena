import NearCompression.YieldResume

/-! Yield creation binds the data-id context, counter and real-store status. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem state_equiv_data_id (s t : St) (h : StateEquivalent s t) (n : Nat) :
    dataIdOf s n = dataIdOf t n := by
  have hc : s.ctx = t.ctx := by have he := congrArg St.ctx h.core; exact he
  simp only [dataIdOf, hc]

def yieldReceiptThen (next : ByteArray → Nat → HM Unit) : HM Unit := do
  let s ← get
  let did := dataIdOf s s.dataCount
  set { s with dataCount := s.dataCount + 1 }
  if s.real.isSome then
    realPutH (yieldKey 20 s.ctx.currentAccount did) (some (ByteArray.mk #[0]))
  let r ← pushAction { text := s!"YC:{hexStr did}>{s.ctx.currentAccount}:-",
                       receiver := some s.ctx.currentAccount, yieldCreate := some (did, none) }
  next did r

theorem yield_receipt_then_sim (next : ByteArray → Nat → HM Unit)
    (nextSim : ∀ did r, HostSim (next did r) (next did r)) :
    HostSim (yieldReceiptThen next) (yieldReceiptThen next) := by
  unfold yieldReceiptThen
  apply host_sim_get_bind
  intro s t h
  have hc : s.ctx = t.ctx := by have he := congrArg St.ctx h.core; exact he
  have hn : s.dataCount = t.dataCount := by have he := congrArg St.dataCount h.core; exact he
  have hd := state_equiv_data_id s t h t.dataCount
  dsimp only
  rw [hn, hd, state_equiv_real_is_some s t h, hc]
  apply host_set_then_equiv s t
    { s with ctx := t.ctx, dataCount := t.dataCount + 1 }
    { t with dataCount := t.dataCount + 1 }
    ⟨congrArg (fun s : St => { s with ctx := t.ctx, dataCount := t.dataCount + 1 }) h.core, h.real⟩
  split
  · apply host_sim_bind
    · intro u v huv
      exact real_put_host_equiv u v huv _ _
    intro _
    apply host_sim_bind
    · exact host_sim_push_action _
    intro receipt
    exact nextSim _ receipt
  · apply host_sim_bind
    · exact host_sim_push_action _
    intro receipt
    exact nextSim _ receipt

def appendYieldAction (m a : ByteArray) (r gas weight : Nat) : HM Unit := do
  if (← get).real.isSome && (String.fromUTF8? m).isNone then hErr "InvalidMethodName"
  let _ ← pushAction { text := s!"FC@{r}:{hexStr m}:{hexStr a}:0:{gas}:{weight}" }

theorem append_yield_action_sim (m a : ByteArray) (r gas weight : Nat) :
    HostSim (appendYieldAction m a r gas weight)
      (appendYieldAction m a r gas weight) := by
  unfold appendYieldAction
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

def yieldCreateFinish (fee byteFee : Fee3) (m args : ByteArray)
    (gas weight reg : Nat) (did : ByteArray) (r : Nat) : HM Unit := do
  let pi ← pushPromiseH (.receipt r)
  payActionBaseH fee true
  payActionPerByteH byteFee (m.size + args.size) true
  appendYieldAction m args r gas weight
  regSetH reg did
  pushRet pi

theorem yield_create_finish_sim (fee byteFee : Fee3) (m args : ByteArray)
    (gas weight reg : Nat) (did : ByteArray) (r : Nat) :
    HostSim (yieldCreateFinish fee byteFee m args gas weight reg did r)
      (yieldCreateFinish fee byteFee m args gas weight reg did r) := by
  unfold yieldCreateFinish
  apply host_sim_bind
  · exact host_sim_push_promise _
  intro pi
  apply host_sim_bind
  · exact host_sim_action_base _ _
  intro _
  apply host_sim_bind
  · exact host_sim_action_byte _ _ _
  intro _
  apply host_sim_bind
  · exact append_yield_action_sim _ _ _ _ _
  intro _
  with_reducible
    exact host_sim_bind (regSetH reg did) (regSetH reg did)
      (fun _ => pushRet pi) (fun _ => pushRet pi)
      (host_sim_reg_set reg did true) (fun _ => host_sim_push_ret pi true)

def yieldCreateCode (base createBase createByte : Cost) (fee byteFee : Fee3) (newReceipt : HM Unit)
    (read : Nat → Nat → HM ByteArray) : HM Unit := do
  let a ← popArgs 7
  payBaseH base
  payBaseH createBase
  let m ← read a[1] a[0]
  if m.size = 0 then hErr "EmptyMethodName"
  let args ← read a[3] a[2]
  payPerH createByte (m.size + args.size)
  withGas (deduct · 0 a[4])
  newReceipt
  yieldReceiptThen (yieldCreateFinish fee byteFee m args a[4] a[5] a[6])

theorem yield_create_code_sim (base createBase createByte : Cost) (fee byteFee : Fee3) (newReceipt : HM Unit)
    (receiptSim : HostSim newReceipt newReceipt)
    (read : Nat → Nat → HM ByteArray)
    (readSim : ∀ ptr len, HostSim (read ptr len) (read ptr len)) :
    HostSim (yieldCreateCode base createBase createByte fee byteFee newReceipt read)
      (yieldCreateCode base createBase createByte fee byteFee newReceipt read) := by
  unfold yieldCreateCode
  apply host_sim_bind
  · exact host_sim_pop_args 7
  intro a
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · exact readSim _ _
  intro m
  dsimp only
  split
  · simp only [host_error_bind]; exact host_sim_error _
  · apply host_sim_bind
    · exact readSim _ _
    intro args
    apply host_sim_bind
    · unfold payPerH; exact host_sim_with_gas _
    intro _
    apply host_sim_bind
    · exact host_sim_with_gas _
    intro _
    apply host_sim_bind
    · exact receiptSim
    intro _
    apply yield_receipt_then_sim
    intro did r
    exact yield_create_finish_sim fee byteFee m args a[4] a[5] a[6] did r

theorem actual_yield_create_code : hostCall "promise_yield_create" =
    some (yieldCreateCode C.base C.yieldCreateBase C.yieldCreateByte
      F.functionCall F.functionCallByte (payNewReceiptH true #[true]) memOrRegH) := by
  unfold hostCall yieldCreateCode yieldReceiptThen yieldCreateFinish appendYieldAction
  simp only [bind_assoc, pure_bind, host_bind_if, host_error_bind]

theorem actual_yield_create_sim (call : HM Unit)
    (hc : hostCall "promise_yield_create" = some call) : HostSim call call := by
  rw [actual_yield_create_code] at hc
  cases Option.some.inj hc
  with_reducible exact yield_create_code_sim C.base C.yieldCreateBase C.yieldCreateByte F.functionCall F.functionCallByte (payNewReceiptH true #[true]) (host_sim_new_receipt true #[true]) memOrRegH host_sim_mem_or_reg

end NearCompression
