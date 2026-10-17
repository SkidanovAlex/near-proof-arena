import NearCompression.YieldCreate

/-! Explicit yield IDs: duplicate short circuit and three ordered storage mappings. -/
namespace NearCompression
open NearSpecV3.Wasm

def yieldIdReceiptThen (yid : ByteArray) (next : Nat → HM Unit) : HM Unit := do
  let s ← get
  let dup ← if s.real.isSome then
      realHasH (yieldKey 22 s.ctx.currentAccount yid)
    else pure (s.actions.any fun x => match x.yieldCreate with
      | some (_, some y) => y == yid
      | _ => false)
  if dup then pushRet (u64Bound - 1) else
  let did := dataIdOf s s.dataCount
  set { s with dataCount := s.dataCount + 1 }
  if s.real.isSome then
    realPutH (yieldKey 20 s.ctx.currentAccount did) (some (ByteArray.mk #[0]))
    realPutH (yieldKey 22 s.ctx.currentAccount yid) (some did)
    realPutH (yieldKey 23 s.ctx.currentAccount did) (some yid)
  let r ← pushAction { text := s!"YC:{hexStr did}>{s.ctx.currentAccount}:{hexStr yid}",
                       receiver := some s.ctx.currentAccount, yieldCreate := some (did, some yid) }
  next r

theorem yield_id_receipt_then_sim (yid : ByteArray) (next : Nat → HM Unit)
    (nextSim : ∀ r, HostSim (next r) (next r)) :
    HostSim (yieldIdReceiptThen yid next) (yieldIdReceiptThen yid next) := by
  unfold yieldIdReceiptThen
  apply host_sim_get_bind
  intro s t h
  have hc : s.ctx = t.ctx := by have he := congrArg St.ctx h.core; exact he
  have hn : s.dataCount = t.dataCount := by have he := congrArg St.dataCount h.core; exact he
  have ha : s.actions = t.actions := by have he := congrArg St.actions h.core; exact he
  have hd := state_equiv_data_id s t h t.dataCount
  dsimp only
  rw [hn, hd, state_equiv_real_is_some s t h, hc, ha]
  split <;> (
    apply host_bind_equiv
    · first | exact real_has_host_equiv s t h _ | exact host_sim_pure _ s t h
    intro dup u v huv
    split
    · exact host_sim_push_ret _ true u v huv
    · apply host_set_then_equiv u v
        { s with ctx := t.ctx, actions := t.actions, dataCount := t.dataCount + 1 }
        { t with dataCount := t.dataCount + 1 }
        ⟨congrArg (fun s : St => { s with ctx := t.ctx, actions := t.actions, dataCount := t.dataCount + 1 }) h.core, h.real⟩
      try split
      all_goals
        repeat' first
          | exact nextSim _
          | exact host_sim_push_action _
          | exact fun u v huv => real_put_host_equiv u v huv _ _
          | apply host_sim_bind
          | intro _
  )

def yieldIdFinish (fee byteFee : Fee3) (newReceipt : HM Unit) (m args : ByteArray)
    (amount gas weight r : Nat) : HM Unit := do
  withGas (deduct · 0 gas)
  newReceipt
  let pi ← pushPromiseH (.receipt r)
  payActionBaseH fee true
  payActionPerByteH byteFee (m.size + args.size) true
  actionDeposit amount
  appendFunctionAction m args r amount gas weight
  pushRet pi

theorem yield_id_finish_sim (fee byteFee : Fee3) (newReceipt : HM Unit)
    (receiptSim : HostSim newReceipt newReceipt) (m args : ByteArray)
    (amount gas weight r : Nat) :
    HostSim (yieldIdFinish fee byteFee newReceipt m args amount gas weight r)
      (yieldIdFinish fee byteFee newReceipt m args amount gas weight r) := by
  unfold yieldIdFinish
  apply host_sim_bind
  · exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · exact receiptSim
  intro _
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
  · exact action_deposit_sim _
  intro _
  apply host_sim_bind
  · exact append_function_action_sim _ _ _ _ _ _
  intro _
  exact host_sim_push_ret pi true

def yieldIdCode (base idBase byte : Cost) (fee byteFee : Fee3) (newReceipt : HM Unit)
    (readAmount : Nat → HM Nat) (read : Nat → Nat → HM ByteArray) (a : Vector Nat 9) : HM Unit := do
  payBaseH base
  payBaseH idBase
  let amount ← readAmount a[4]
  let m ← read a[1] a[0]
  if m.size = 0 then hErr "EmptyMethodName"
  let args ← read a[3] a[2]
  let yid ← read a[8] a[7]
  if yid.size ≠ 32 then hErr "YieldIdMalformed"
  payPerH byte (m.size + args.size)
  yieldIdReceiptThen yid (yieldIdFinish fee byteFee newReceipt m args amount a[5] a[6])

theorem yield_id_code_sim (base idBase byte : Cost) (fee byteFee : Fee3) (newReceipt : HM Unit)
    (readAmount : Nat → HM Nat) (read : Nat → Nat → HM ByteArray)
    (receiptSim : HostSim newReceipt newReceipt)
    (amountSim : ∀ ptr, HostSim (readAmount ptr) (readAmount ptr))
    (readSim : ∀ ptr len, HostSim (read ptr len) (read ptr len)) (a : Vector Nat 9) :
    HostSim (yieldIdCode base idBase byte fee byteFee newReceipt readAmount read a)
      (yieldIdCode base idBase byte fee byteFee newReceipt readAmount read a) := by
  unfold yieldIdCode
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
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
    intro args
    apply host_sim_bind
    · exact readSim _ _
    intro yid
    split
    · simp only [host_error_bind]; exact host_sim_error _
    · apply host_sim_bind
      · unfold payPerH; exact host_sim_with_gas _
      intro _
      apply yield_id_receipt_then_sim
      intro r
      exact yield_id_finish_sim fee byteFee newReceipt receiptSim m args amount a[5] a[6] r

theorem actual_yield_id_code (a : Vector Nat 9) : yieldCreateWithIdH a =
    yieldIdCode C.base C.yieldCreateWithIdBase C.yieldCreateByte F.functionCall F.functionCallByte
      (payNewReceiptH true #[true]) getU128H memOrRegH a := by
  unfold yieldCreateWithIdH yieldIdCode yieldIdReceiptThen yieldIdFinish actionDeposit appendFunctionAction
  simp only [bind_assoc, pure_bind, host_bind_if, host_error_bind]
  rfl

theorem host_sim_yield_id (a : Vector Nat 9) : HostSim (yieldCreateWithIdH a) (yieldCreateWithIdH a) := by
  rw [actual_yield_id_code]
  with_reducible exact yield_id_code_sim C.base C.yieldCreateWithIdBase C.yieldCreateByte F.functionCall F.functionCallByte (payNewReceiptH true #[true]) getU128H memOrRegH (host_sim_new_receipt true #[true]) host_sim_get_u128 host_sim_mem_or_reg a

theorem actual_yield_id_sim (call : HM Unit)
    (hc : hostCall "promise_yield_create_with_id" = some call) : HostSim call call := by
  have he : hostCall "promise_yield_create_with_id" = some (do yieldCreateWithIdH (← popArgs 9)) := rfl
  rw [he] at hc
  cases Option.some.inj hc
  apply host_sim_bind
  · exact host_sim_pop_args 9
  intro a
  with_reducible exact host_sim_yield_id a

end NearCompression
