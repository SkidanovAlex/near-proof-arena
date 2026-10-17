import NearCompression.StackHost

/-! Complete storage host-call simulation. The final correspondence theorem
binds the composed code to the actual hostCall dispatch branch. -/
namespace NearCompression
open NearSpecV3.Wasm

def storageHasKeyFinish (key : ByteArray) : HM Unit := do
  match (← get).real with
  | some r =>
    let v ← realOpH r TTN.storageHasKey key
    observeH
    pushRet (if v.isSome then 1 else 0)
  | none => pushRet (if (trieGet (← get) key).isSome then 1 else 0)

theorem host_sim_has_key_finish (key : ByteArray) :
    HostSim (storageHasKeyFinish key) (storageHasKeyFinish key) := by
  intro s t hs
  unfold storageHasKeyFinish
  rw [host_get_bind_run, host_get_bind_run]
  have hr := hs.real
  cases ha : s.real <;> cases hb : t.real <;>
    simp only [ha, hb, OptionalRealEquivalent] at hr
  · rw [host_get_bind_run, host_get_bind_run]
    have he : trieGet s key = trieGet t key := by
      have hh := congrArg (fun s => trieGet s key) hs.core
      exact hh
    rw [he]
    exact host_sim_push_ret _ true s t hs
  · rename_i a b
    simp only
    apply host_bind_equiv
    · exact storage_has_key_host_equiv s t hs a b hr key
    · intro value u v huv
      apply host_bind_equiv
      · exact observe_host_equiv u v huv
      · intro _ u' v' hs'
        exact host_sim_push_ret _ true u' v' hs'

/-- Actual storage_has_key code with costs kept as parameters for elaboration.
Argument count, key limit, error text and ordering are unchanged. -/
def storageHasKeyCode (base hasKey keyByte : Cost) : HM Unit := do
  let a ← popArgs 2
  payBaseH base
  payBaseH hasKey
  let k ← memOrRegH a[1] a[0]
  if k.size > maxLengthStorageKey then
    hErr s!"KeyLengthExceeded \{ length: {k.size}, limit: {maxLengthStorageKey} }"
  payPerH keyByte k.size
  storageHasKeyFinish k

theorem host_sim_has_key_code (base hasKey keyByte : Cost) :
    HostSim (storageHasKeyCode base hasKey keyByte) (storageHasKeyCode base hasKey keyByte) := by
  unfold storageHasKeyCode
  with_reducible apply host_sim_bind
  · with_reducible exact host_sim_pop_args 2
  intro args
  with_reducible apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  with_reducible apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  with_reducible apply host_sim_bind
  · with_reducible exact host_sim_mem_or_reg _ _
  intro key
  dsimp only
  split
  · with_reducible apply host_sim_bind
    · exact host_sim_error _
    intro _
    with_reducible apply host_sim_bind
    · unfold payPerH
      exact host_sim_with_gas _
    intro _
    exact host_sim_has_key_finish key
  · with_reducible apply host_sim_bind
    · unfold payPerH
      exact host_sim_with_gas _
    intro _
    exact host_sim_has_key_finish key

/-- Definitional correspondence to the actual dispatch, not a replacement VM. -/
theorem actual_storage_has_key_code :
    hostCall "storage_has_key" =
      some (storageHasKeyCode C.base C.storageHasKeyBase C.storageHasKeyByte) := by rfl

/-- Every actual storage_has_key computation preserves equivalence, including
argument popping, gas, key reads/limits, both stores, recording and return stack. -/
theorem actual_storage_has_key_sim (call : HM Unit)
    (hcall : hostCall "storage_has_key" = some call) : HostSim call call := by
  rw [actual_storage_has_key_code] at hcall
  cases Option.some.inj hcall
  with_reducible exact host_sim_has_key_code C.base C.storageHasKeyBase C.storageHasKeyByte

/-- Exact register/stack result sequence used by storage_read. -/
def storageReadResult (reg : Nat) : Option ByteArray → HM Unit
  | some value => do regSetH reg value; pushRet 1
  | none => pushRet 0

theorem host_sim_read_result (reg : Nat) (value : Option ByteArray) :
    HostSim (storageReadResult reg value) (storageReadResult reg value) := by
  cases value with
  | none => exact host_sim_push_ret 0 true
  | some bytes =>
    unfold storageReadResult
    have hr : HostSim (regSetH reg bytes true) (regSetH reg bytes true) := by
      with_reducible exact host_sim_reg_set reg bytes true
    with_reducible exact host_sim_bind (regSetH reg bytes true) (regSetH reg bytes true) (fun _ => pushRet 1) (fun _ => pushRet 1) hr (fun _ => host_sim_push_ret 1 true)

def mockReadValue (valueByte largeBase largeByte : Cost) (reg : Nat) (value : ByteArray) : HM Unit := do
  payPerH valueByte value.size
  if value.size > 4000 then
    payBaseH largeBase
    payPerH largeByte value.size
  regSetH reg value
  pushRet 1

theorem host_sim_mock_read_value (valueByte largeBase largeByte : Cost)
    (reg : Nat) (value : ByteArray) :
    HostSim (mockReadValue valueByte largeBase largeByte reg value)
      (mockReadValue valueByte largeBase largeByte reg value) := by
  unfold mockReadValue
  with_reducible apply host_sim_bind
  · unfold payPerH
    exact host_sim_with_gas _
  intro _
  dsimp only
  split
  · with_reducible apply host_sim_bind
    · unfold payBaseH
      exact host_sim_with_gas _
    intro _
    with_reducible apply host_sim_bind
    · unfold payPerH
      exact host_sim_with_gas _
    intro _
    change HostSim (storageReadResult reg (some value)) (storageReadResult reg (some value))
    with_reducible exact host_sim_read_result reg (some value)
  · change HostSim (storageReadResult reg (some value)) (storageReadResult reg (some value))
    with_reducible exact host_sim_read_result reg (some value)

def storageReadFinish (valueByte largeBase largeByte : Cost) (key : ByteArray) (reg : Nat) : HM Unit := do
  match (← get).real with
  | some r =>
    let value ← realOpH r TTN.storageRead key
    observeH
    storageReadResult reg value
  | none =>
    match trieGet (← get) key with
    | some value => mockReadValue valueByte largeBase largeByte reg value
    | none => pushRet 0

theorem host_sim_read_finish (valueByte largeBase largeByte : Cost) (key : ByteArray) (reg : Nat) :
    HostSim (storageReadFinish valueByte largeBase largeByte key reg)
      (storageReadFinish valueByte largeBase largeByte key reg) := by
  intro s t hs
  unfold storageReadFinish
  rw [host_get_bind_run, host_get_bind_run]
  have hr := hs.real
  cases ha : s.real <;> cases hb : t.real <;>
    simp only [ha, hb, OptionalRealEquivalent] at hr
  · rw [host_get_bind_run, host_get_bind_run]
    have he : trieGet s key = trieGet t key := by
      have hh := congrArg (fun s => trieGet s key) hs.core
      exact hh
    rw [he]
    split
    · rename_i value found
      have hh := host_sim_mock_read_value valueByte largeBase largeByte reg value
      unfold HostSim at hh
      with_reducible exact hh s t hs
    · exact host_sim_push_ret 0 true s t hs
  · rename_i a b
    simp only
    apply host_bind_equiv
    · exact storage_read_host_equiv s t hs a b hr key
    · intro value u v huv
      apply host_bind_equiv
      · exact observe_host_equiv u v huv
      · intro _ u' v' hs'
        have hh : HostSim (storageReadResult reg value) (storageReadResult reg value) := by
          with_reducible exact host_sim_read_result reg value
        unfold HostSim at hh
        with_reducible exact hh u' v' hs'

def storageReadCode (base readBase keyByte valueByte largeBase largeByte : Cost) : HM Unit := do
  let a ← popArgs 3
  payBaseH base
  payBaseH readBase
  let k ← memOrRegH a[1] a[0]
  if k.size > maxLengthStorageKey then
    hErr s!"KeyLengthExceeded \{ length: {k.size}, limit: {maxLengthStorageKey} }"
  payPerH keyByte k.size
  storageReadFinish valueByte largeBase largeByte k a[2]

theorem host_sim_read_code (base readBase keyByte valueByte largeBase largeByte : Cost) :
    HostSim (storageReadCode base readBase keyByte valueByte largeBase largeByte)
      (storageReadCode base readBase keyByte valueByte largeBase largeByte) := by
  unfold storageReadCode
  with_reducible apply host_sim_bind
  · with_reducible exact host_sim_pop_args 3
  intro args
  with_reducible apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  with_reducible apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  with_reducible apply host_sim_bind
  · with_reducible exact host_sim_mem_or_reg _ _
  intro key
  dsimp only
  split
  · with_reducible apply host_sim_bind
    · exact host_sim_error _
    intro _
    with_reducible apply host_sim_bind
    · unfold payPerH
      exact host_sim_with_gas _
    intro _
    exact host_sim_read_finish valueByte largeBase largeByte key args[2]
  · with_reducible apply host_sim_bind
    · unfold payPerH
      exact host_sim_with_gas _
    intro _
    exact host_sim_read_finish valueByte largeBase largeByte key args[2]

theorem actual_storage_read_code : hostCall "storage_read" =
    some (storageReadCode C.base C.storageReadBase C.storageReadKeyByte C.storageReadValueByte
      C.storageLargeReadOverheadBase C.storageLargeReadOverheadByte) := by rfl

theorem actual_storage_read_sim (call : HM Unit)
    (hcall : hostCall "storage_read" = some call) : HostSim call call := by
  rw [actual_storage_read_code] at hcall
  cases Option.some.inj hcall
  with_reducible exact host_sim_read_code C.base C.storageReadBase C.storageReadKeyByte C.storageReadValueByte C.storageLargeReadOverheadBase C.storageLargeReadOverheadByte

end NearCompression
