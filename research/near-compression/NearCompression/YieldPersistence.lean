import NearCompression.LegacyPersistence

/-! Yield resumption retains the real backend across lookup and state writes. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem yield_resume_body_keeps_real (did payload : ByteArray) :
    HostKeepsReal (yieldResumeBody did payload) := by
  unfold yieldResumeBody
  apply host_real_get_bind
  intro s hs
  simp only [hs, ite_true]
  apply host_real_get_bind
  intro u hu
  apply host_real_bind
  · exact host_real_has _
  · intro first
    apply host_real_bind
    · exact host_real_has _
    intro second
    split
    · apply host_real_bind
      · exact host_real_push_action _
      intro _
      apply host_real_bind
      · exact host_real_put _ _
      intro _
      exact host_real_push_ret _ false
    · exact host_real_push_ret _ false
  · exact hu
  · exact hs

theorem yield_resume_code_keeps_real (base resumeBase resumeByte : Cost)
    (read : Nat → Nat → HM ByteArray)
    (readSim : ∀ ptr len, HostKeepsReal (read ptr len)) :
    HostKeepsReal (yieldResumeCode base resumeBase resumeByte read) := by
  unfold yieldResumeCode
  apply host_real_bind
  · exact host_real_pop_args 4
  intro a
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · unfold payPerH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact readSim _ _
  intro did
  apply host_real_bind
  · exact readSim _ _
  intro payload
  dsimp only
  split
  · simp only [host_error_bind]; exact host_real_throw _
  · split
    · simp only [host_error_bind]; exact host_real_throw _
    · exact yield_resume_body_keeps_real did payload

theorem actual_yield_resume_keeps_real (call : HM Unit)
    (hc : hostCall "promise_yield_resume" = some call) : HostKeepsReal call := by
  rw [actual_yield_resume_code] at hc
  cases Option.some.inj hc
  with_reducible exact yield_resume_code_keeps_real C.base C.yieldResumeBase C.yieldResumeByte memOrRegH host_real_mem_or_reg

end NearCompression
