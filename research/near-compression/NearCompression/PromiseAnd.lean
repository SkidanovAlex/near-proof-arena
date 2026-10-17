import NearCompression.PromiseThen

/-! Ordered promise dependency expansion, including limit and index failures. -/
namespace NearCompression
open NearSpecV3.Wasm

def promiseAndFinish (d : ByteArray) (count : Nat) : HM Unit := do
  let mut deps : Array Nat := #[]
  for i in [0:count] do
    let pi := leNat (d.extract (8 * i) (8 * i + 8))
    match (← get).promises[pi]? with
    | none => hErr s!"InvalidPromiseIndex \{ promise_idx: {pi} }"
    | some (.receipt r) => deps := deps.push r
    | some (.joint rs) => deps := deps ++ rs
    if deps.size > maxInputDataDependencies then
      hErr s!"NumberInputDataDependenciesExceeded \{ number_of_input_data_dependencies: {deps.size}, limit: {maxInputDataDependencies} }"
  pushRet (← pushPromiseH (.joint deps))

theorem promise_and_finish_sim (d : ByteArray) (count : Nat) :
    HostSim (promiseAndFinish d count) (promiseAndFinish d count) := by
  unfold promiseAndFinish
  apply host_sim_bind
  · apply host_sim_for_in
    intro i deps
    apply host_sim_get_bind
    intro s t h
    have hp : s.promises = t.promises := by
      have he := congrArg St.promises h.core
      exact he
    simp only [hp]
    split <;> (repeat' (split <;> (try simp_all only []))) <;>
      first | exact host_sim_error _ s t h | exact host_sim_pure _ s t h
  intro deps
  apply host_sim_bind
  · exact host_sim_push_promise (.joint deps)
  intro promise
  exact host_sim_push_ret promise true

def promiseAndCode (base andBase perPromise : Cost)
    (readMemory : Nat → Nat → HM ByteArray) : HM Unit := do
  let a ← popArgs 2
  payBaseH base
  payBaseH andBase
  let ml := a[1] * 8
  if ml ≥ u64Bound then hErr "IntegerOverflow"
  payPerH perPromise ml
  let d ← readMemory a[0] ml
  promiseAndFinish d a[1]

theorem promise_and_code_sim (base andBase perPromise : Cost)
    (readMemory : Nat → Nat → HM ByteArray)
    (readerSim : ∀ ptr len, HostSim (readMemory ptr len) (readMemory ptr len)) :
    HostSim (promiseAndCode base andBase perPromise readMemory)
      (promiseAndCode base andBase perPromise readMemory) := by
  unfold promiseAndCode
  apply host_sim_bind
  · exact host_sim_pop_args 2
  intro a
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  apply host_sim_bind
  · unfold payBaseH; exact host_sim_with_gas _
  intro _
  dsimp only
  split
  · simp only [host_error_bind]
    exact host_sim_error _
  · apply host_sim_bind
    · unfold payPerH; exact host_sim_with_gas _
    intro _
    apply host_sim_bind
    · exact readerSim _ _
    intro d
    exact promise_and_finish_sim d a[1]

theorem actual_promise_and_code : hostCall "promise_and" =
    some (promiseAndCode C.base C.promiseAndBase C.promiseAndPerPromise readMemH) := by rfl

theorem actual_promise_and_sim (call : HM Unit)
    (hc : hostCall "promise_and" = some call) : HostSim call call := by
  rw [actual_promise_and_code] at hc
  cases Option.some.inj hc
  with_reducible exact promise_and_code_sim C.base C.promiseAndBase C.promiseAndPerPromise readMemH host_sim_read_mem

end NearCompression
