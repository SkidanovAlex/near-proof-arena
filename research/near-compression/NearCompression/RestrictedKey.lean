import NearCompression.KeyActions

/-! Function-call access keys with allowance and method-list validation. -/
namespace NearCompression
open NearSpecV3.Wasm

def restrictedKeyFinish (names : Array ByteArray) (pk : ByteArray)
    (r nonce allowance : Nat) (recv : String) : HM Unit := do
  if (← get).real.isSome && names.any (fun n => (String.fromUTF8? n).isNone) then
    hErr "InvalidMethodName"
  let al := if allowance > 0 then toString allowance else "-"
  let _ ← pushAction { text := s!"AC@{r}:{hexStr pk}:{nonce}:{al}:{recv}:{"/".intercalate (names.toList.map hexStr)}" }

theorem restricted_key_finish_sim (names : Array ByteArray) (pk : ByteArray)
    (r nonce allowance : Nat) (recv : String) :
    HostSim (restrictedKeyFinish names pk r nonce allowance recv)
      (restrictedKeyFinish names pk r nonce allowance recv) := by
  unfold restrictedKeyFinish
  apply host_sim_get_bind
  intro s t h
  rw [state_equiv_real_is_some s t h]
  dsimp only
  split
  · simp only [host_error_bind]; exact host_sim_error _ s t h
  · apply host_bind_equiv
    · exact host_sim_push_action _ s t h
    intro _ u v huv
    exact host_sim_pure () u v huv

def restrictedKeyBody (fee byteFee : Fee3) (raw pk : ByteArray)
    (idx nonce allowance : Nat) (recv : String) : HM Unit := do
  let names ← match splitMethodNames raw with
    | some n => pure n
    | none => hErr "EmptyMethodName"
  let (r, sir) ← promiseReceiptH idx
  let nb := names.foldl (fun acc n => acc + n.size + 1) 0
  payActionBaseH fee sir
  payActionPerByteH byteFee nb sir
  if !pkValid pk then hErr "InvalidPublicKey"
  restrictedKeyFinish names pk r nonce allowance recv

theorem restricted_key_body_sim (fee byteFee : Fee3) (raw pk : ByteArray)
    (idx nonce allowance : Nat) (recv : String) :
    HostSim (restrictedKeyBody fee byteFee raw pk idx nonce allowance recv)
      (restrictedKeyBody fee byteFee raw pk idx nonce allowance recv) := by
  unfold restrictedKeyBody
  dsimp only
  split <;> (
    apply host_sim_bind
    · first | exact host_sim_pure _ | exact host_sim_error _
    intro names
    apply host_sim_bind
    · exact host_sim_promise_receipt _
    intro receipt
    apply host_sim_bind
    · exact host_sim_action_base _ _
    intro _
    apply host_sim_bind
    · exact host_sim_action_byte _ _ _
    intro _
    split
    · simp only [host_error_bind]; exact host_sim_error _
    · exact restricted_key_finish_sim names pk receipt.1 nonce allowance recv
  )

def restrictedKeyCode (base : Cost) (fee byteFee : Fee3)
    (read : Nat → Nat → HM ByteArray) (readAmount : Nat → HM Nat)
    (readAccount : Nat → Nat → HM String) : HM Unit := do
  let a ← popArgs 9
  payBaseH base
  let pk ← read a[2] a[1]
  let allowance ← readAmount a[4]
  let recv ← readAccount a[5] a[6]
  let raw ← read a[8] a[7]
  restrictedKeyBody fee byteFee raw pk a[0] a[3] allowance recv

theorem restricted_key_code_sim (base : Cost) (fee byteFee : Fee3)
    (read : Nat → Nat → HM ByteArray) (readAmount : Nat → HM Nat)
    (readAccount : Nat → Nat → HM String)
    (readSim : ∀ ptr len, HostSim (read ptr len) (read ptr len))
    (amountSim : ∀ ptr, HostSim (readAmount ptr) (readAmount ptr))
    (accountSim : ∀ len ptr, HostSim (readAccount len ptr) (readAccount len ptr)) :
    HostSim (restrictedKeyCode base fee byteFee read readAmount readAccount)
      (restrictedKeyCode base fee byteFee read readAmount readAccount) := by
  unfold restrictedKeyCode
  apply host_sim_bind
  · exact host_sim_pop_args 9
  intro a
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · exact readSim _ _
  intro pk
  apply host_sim_bind
  · exact amountSim _
  intro allowance
  apply host_sim_bind
  · exact accountSim _ _
  intro recv
  apply host_sim_bind
  · exact readSim _ _
  intro raw
  exact restricted_key_body_sim fee byteFee raw pk a[0] a[3] allowance recv

theorem actual_restricted_key_code : hostCall "promise_batch_action_add_key_with_function_call" =
    some (restrictedKeyCode C.base F.addFunctionCallKey F.addFunctionCallKeyByte
      memOrRegH getU128H readAccountIdH) := by rfl

theorem actual_restricted_key_sim (call : HM Unit)
    (hc : hostCall "promise_batch_action_add_key_with_function_call" = some call) : HostSim call call := by
  rw [actual_restricted_key_code] at hc
  cases Option.some.inj hc
  with_reducible exact restricted_key_code_sim C.base F.addFunctionCallKey F.addFunctionCallKeyByte memOrRegH getU128H readAccountIdH host_sim_mem_or_reg host_sim_get_u128 host_sim_read_account_id

end NearCompression
