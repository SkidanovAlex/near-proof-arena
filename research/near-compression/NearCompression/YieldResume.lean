import NearCompression.AccountActions

/-! Yield resumption preserves real-store and mock action-list behavior. -/
namespace NearCompression
open NearSpecV3.Wasm

def yieldResumeBody (did payload : ByteArray) : HM Unit := do
  if (← get).real.isSome then
    let acct := (← get).ctx.currentAccount
    let found := (← realHasH (yieldKey 12 acct did)) || (← realHasH (yieldKey 20 acct did))
    if found then
      let _ ← pushAction { text := s!"YR:{hexStr did}:{hexStr payload}" }
      realPutH (yieldKey 20 acct did) (some (ByteArray.mk #[1]))
    pushRet (if found then 1 else 0) (is64 := false)
  else
    let _ ← pushAction { text := s!"YR:{hexStr did}:{hexStr payload}" }
    let found := (← get).actions.any fun x => match x.yieldCreate with
      | some (d, _) => d == did
      | none => false
    pushRet (if found then 1 else 0) (is64 := false)

theorem yield_resume_body_sim (did payload : ByteArray) :
    HostSim (yieldResumeBody did payload) (yieldResumeBody did payload) := by
  unfold yieldResumeBody
  apply host_sim_get_bind
  intro s t h
  rw [state_equiv_real_is_some s t h]
  split
  · rw [host_get_bind_run, host_get_bind_run]
    have hc : s.ctx = t.ctx := by have he := congrArg St.ctx h.core; exact he
    rw [hc]
    apply host_bind_equiv
    · exact real_has_host_equiv s t h _
    intro first u v huv
    apply host_bind_equiv
    · exact real_has_host_equiv u v huv _
    intro second u v huv
    dsimp only
    split
    · apply host_bind_equiv
      · exact host_sim_push_action _ u v huv
      intro _ u v huv
      apply host_bind_equiv
      · exact real_put_host_equiv u v huv _ _
      intro _ u v huv
      exact host_sim_push_ret _ false u v huv
    · exact host_sim_push_ret _ false u v huv
  · apply host_bind_equiv
    · exact host_sim_push_action _ s t h
    intro _ u v huv
    rw [host_get_bind_run, host_get_bind_run]
    have ha : u.actions = v.actions := by have he := congrArg St.actions huv.core; exact he
    rw [ha]
    exact host_sim_push_ret _ false u v huv

def yieldResumeCode (base resumeBase resumeByte : Cost)
    (read : Nat → Nat → HM ByteArray) : HM Unit := do
  let a ← popArgs 4
  payBaseH base
  payBaseH resumeBase
  payPerH resumeByte a[2]
  let did ← read a[1] a[0]
  let payload ← read a[3] a[2]
  if payload.size > maxYieldPayloadSize then
    hErr s!"YieldPayloadLength \{ length: {payload.size}, limit: {maxYieldPayloadSize} }"
  if did.size ≠ 32 then hErr "DataIdMalformed"
  yieldResumeBody did payload

theorem yield_resume_code_sim (base resumeBase resumeByte : Cost)
    (read : Nat → Nat → HM ByteArray)
    (readSim : ∀ ptr len, HostSim (read ptr len) (read ptr len)) :
    HostSim (yieldResumeCode base resumeBase resumeByte read)
      (yieldResumeCode base resumeBase resumeByte read) := by
  unfold yieldResumeCode
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
    · exact yield_resume_body_sim did payload

theorem actual_yield_resume_code : hostCall "promise_yield_resume" =
    some (yieldResumeCode C.base C.yieldResumeBase C.yieldResumeByte memOrRegH) := by rfl

theorem actual_yield_resume_sim (call : HM Unit)
    (hc : hostCall "promise_yield_resume" = some call) : HostSim call call := by
  rw [actual_yield_resume_code] at hc
  cases Option.some.inj hc
  with_reducible exact yield_resume_code_sim C.base C.yieldResumeBase C.yieldResumeByte memOrRegH host_sim_mem_or_reg

end NearCompression
