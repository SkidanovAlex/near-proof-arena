import NearCompression.AccountPersistence

/-! Real backend persistence for promise observations, returns and dependency joins,
including invalid indices, joint-return rejection and dependency limits. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem promise_result_body_keeps_real (write : Nat → ByteArray → HM Unit)
    (writeReal : ∀ reg bytes, HostKeepsReal (write reg bytes)) (idx reg : Nat) :
    HostKeepsReal (promiseResultBody write idx reg) := by
  unfold promiseResultBody
  apply host_real_get_bind
  intro s hs
  repeat' (split <;> (try simp_all only []))
  all_goals first
    | exact host_real_throw _ s hs
    | exact host_real_push_ret _ true s hs
    | (apply host_real_bind
       · exact writeReal _ _
       · intro _; exact host_real_push_ret 1 true
       · exact hs)

theorem promise_return_body_keeps_real (idx : Nat) :
    HostKeepsReal (promiseReturnBody idx) := by
  unfold promiseReturnBody
  apply host_real_get_bind
  intro s hs
  repeat' (split <;> (try simp_all only []))
  all_goals exact hs

theorem promise_and_finish_keeps_real (d : ByteArray) (count : Nat) :
    HostKeepsReal (promiseAndFinish d count) := by
  unfold promiseAndFinish
  apply host_real_bind
  · apply host_real_for_in
    intro i deps
    apply host_real_get_bind
    intro s hs
    split
    · exact hs
    · dsimp only
      split <;> exact hs
    · dsimp only
      split <;> exact hs
  intro deps
  apply host_real_bind
  · exact host_real_push_promise (.joint deps)
  intro promise
  exact host_real_push_ret promise true

theorem promise_result_code_keeps_real (base : Cost) (write : Nat → ByteArray → HM Unit)
    (writeSim : ∀ reg bytes, HostKeepsReal (write reg bytes)) :
    HostKeepsReal (promiseResultCode base write) := by
  unfold promiseResultCode
  apply host_real_bind
  · exact host_real_pop_args 2
  intro a
  apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  exact promise_result_body_keeps_real write writeSim a[0] a[1]

theorem promise_return_code_keeps_real (base ret : Cost) : HostKeepsReal (promiseReturnCode base ret) := by
  unfold promiseReturnCode
  apply host_real_bind
  · exact host_real_pop_args 1
  intro a
  apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  exact promise_return_body_keeps_real a[0]

theorem actual_promise_result_keeps_real (call : HM Unit) (hc : hostCall "promise_result" = some call) :
    HostKeepsReal call := by
  rw [actual_promise_result_code] at hc
  cases Option.some.inj hc
  with_reducible apply promise_result_code_keeps_real C.base (fun reg bytes => regSetH reg bytes false)
  intro reg bytes
  with_reducible exact host_real_reg_set reg bytes false

theorem actual_promise_return_keeps_real (call : HM Unit) (hc : hostCall "promise_return" = some call) :
    HostKeepsReal call := by
  rw [actual_promise_return_code] at hc
  cases Option.some.inj hc
  with_reducible exact promise_return_code_keeps_real C.base C.promiseReturn

theorem promise_and_code_keeps_real (base andBase perPromise : Cost)
    (readMemory : Nat → Nat → HM ByteArray)
    (readerSim : ∀ ptr len, HostKeepsReal (readMemory ptr len)) :
    HostKeepsReal (promiseAndCode base andBase perPromise readMemory) := by
  unfold promiseAndCode
  apply host_real_bind
  · exact host_real_pop_args 2
  intro a
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  dsimp only
  split
  · simp only [host_error_bind]
    exact host_real_throw _
  · apply host_real_bind
    · unfold payPerH; exact host_real_with_gas _
    intro _
    apply host_real_bind
    · exact readerSim _ _
    intro d
    exact promise_and_finish_keeps_real d a[1]

theorem actual_promise_and_keeps_real (call : HM Unit)
    (hc : hostCall "promise_and" = some call) : HostKeepsReal call := by
  rw [actual_promise_and_code] at hc
  cases Option.some.inj hc
  with_reducible exact promise_and_code_keeps_real C.base C.promiseAndBase C.promiseAndPerPromise readMemH host_real_read_mem

end NearCompression
