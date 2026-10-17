import NearCompression.ContractCodeHost

/-! Explicit-ID resumption binds ID resolution to ordered action/status updates. -/
namespace NearCompression
open NearSpecV3.Wasm

def resumeResolvedId (acct : String) (did payload : ByteArray) : HM Unit := do
  let found := (← realHasH (yieldKey 12 acct did)) || (← realHasH (yieldKey 20 acct did))
  if found then
    let _ ← pushAction { text := s!"YR:{hexStr did}:{hexStr payload}" }
    realPutH (yieldKey 20 acct did) (some (ByteArray.mk #[1]))
  pushRet (if found then 1 else 0) (is64 := false)

theorem resume_resolved_id_sim (acct : String) (did payload : ByteArray) :
    HostSim (resumeResolvedId acct did payload) (resumeResolvedId acct did payload) := by
  unfold resumeResolvedId
  apply host_sim_bind
  · exact fun s t h => real_has_host_equiv s t h _
  intro first
  apply host_sim_bind
  · exact fun s t h => real_has_host_equiv s t h _
  intro second
  dsimp only
  split
  · apply host_sim_bind
    · exact host_sim_push_action _
    intro _
    apply host_sim_bind
    · exact fun s t h => real_put_host_equiv s t h _ _
    intro _
    exact host_sim_push_ret _ false
  · exact host_sim_push_ret _ false

def yieldIdResumeBody (yid payload : ByteArray) : HM Unit := do
  if (← get).real.isSome then
    let acct := (← get).ctx.currentAccount
    match ← realGetH (yieldKey 22 acct yid) with
    | none => pushRet 0 (is64 := false)
    | some did => resumeResolvedId acct did payload
  else
    let found := (← get).actions.findSome? fun x => match x.yieldCreate with
      | some (d, some y) => if y == yid then some d else none
      | _ => none
    match found with
    | some did =>
      let _ ← pushAction { text := s!"YR:{hexStr did}:{hexStr payload}" }
      pushRet 1 (is64 := false)
    | none => pushRet 0 (is64 := false)

theorem yield_id_resume_body_sim (yid payload : ByteArray) :
    HostSim (yieldIdResumeBody yid payload) (yieldIdResumeBody yid payload) := by
  unfold yieldIdResumeBody
  apply host_sim_get_bind
  intro s t h
  rw [state_equiv_real_is_some s t h]
  split
  · rw [host_get_bind_run, host_get_bind_run]
    have hc : s.ctx = t.ctx := by have he := congrArg St.ctx h.core; exact he
    rw [hc]
    apply host_bind_equiv
    · exact real_get_host_equiv s t h _
    intro resolved u v huv
    cases resolved with
    | none => exact host_sim_push_ret 0 false u v huv
    | some did => exact resume_resolved_id_sim _ did payload u v huv
  · rw [host_get_bind_run, host_get_bind_run]
    have ha : s.actions = t.actions := by have he := congrArg St.actions h.core; exact he
    rw [ha]
    dsimp only
    split
    · apply host_bind_equiv
      · exact host_sim_push_action _ s t h
      intro _ u v huv
      exact host_sim_push_ret 1 false u v huv
    · exact host_sim_push_ret 0 false s t h

def yieldIdResumeCode (base resumeBase resumeByte : Cost)
    (read : Nat → Nat → HM ByteArray) : HM Unit := do
  let a ← popArgs 4
  payBaseH base
  payBaseH resumeBase
  payPerH resumeByte a[2]
  let did ← read a[1] a[0]
  let payload ← read a[3] a[2]
  if payload.size > maxYieldPayloadSize then
    hErr s!"YieldPayloadLength \{ length: {payload.size}, limit: {maxYieldPayloadSize} }"
  if did.size ≠ 32 then hErr "YieldIdMalformed"
  yieldIdResumeBody did payload

theorem yield_id_resume_code_sim (base resumeBase resumeByte : Cost)
    (read : Nat → Nat → HM ByteArray)
    (readSim : ∀ ptr len, HostSim (read ptr len) (read ptr len)) :
    HostSim (yieldIdResumeCode base resumeBase resumeByte read)
      (yieldIdResumeCode base resumeBase resumeByte read) := by
  unfold yieldIdResumeCode
  apply host_sim_bind
  · exact host_sim_pop_args 4
  intro a
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · unfold payPerH; exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · exact readSim _ _
  intro did
  apply host_sim_bind
  · exact readSim _ _
  intro payload
  dsimp only
  split
  · simp only [host_error_bind]; exact host_sim_error _
  · split
    · simp only [host_error_bind]; exact host_sim_error _
    · exact yield_id_resume_body_sim did payload

theorem actual_yield_id_resume_code : hostCall "promise_yield_resume_with_yield_id" =
    some (yieldIdResumeCode C.base C.yieldResumeBase C.yieldResumeByte memOrRegH) := by rfl

theorem actual_yield_id_resume_sim (call : HM Unit)
    (hc : hostCall "promise_yield_resume_with_yield_id" = some call) : HostSim call call := by
  rw [actual_yield_id_resume_code] at hc
  cases Option.some.inj hc
  with_reducible exact yield_id_resume_code_sim C.base C.yieldResumeBase C.yieldResumeByte memOrRegH host_sim_mem_or_reg

end NearCompression
