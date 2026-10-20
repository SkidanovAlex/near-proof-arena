import NearCompression.LogPersistence

/-! Real storage persistence through charged operations, recording and returned values. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem host_real_observe : HostKeepsReal observeH := by
  unfold observeH
  apply host_real_get_bind
  intro s hs
  split
  · split <;> exact hs
  · exact hs

theorem host_real_storage_usage (f : Nat → Nat) : HostKeepsReal (modifyStorageUsage f) := by
  intro s hs
  exact hs

theorem host_real_record_removal : HostKeepsReal recordStorageRemoval := by
  intro s hs
  change (s.real.map TTN.removeRecord).isSome = true
  simpa only [Option.isSome_map] using hs

theorem host_real_read_result (reg : Nat) (value : Option ByteArray) :
    HostKeepsReal (storageReadResult reg value) := by
  cases value with
  | none => exact host_real_push_ret 0 true
  | some bytes =>
    unfold storageReadResult
    with_reducible
      exact host_real_bind (regSetH reg bytes true) (fun _ => pushRet 1)
        (host_real_reg_set reg bytes true) (fun _ => host_real_push_ret 1 true)

theorem host_real_remove_result (key : ByteArray) (reg : Nat) (value : Option ByteArray) :
    HostKeepsReal (storageRemoveResult key reg value) := by
  cases value with
  | none => exact host_real_push_ret 0 true
  | some bytes =>
    unfold storageRemoveResult
    apply host_real_bind
    · exact host_real_storage_usage _
    intro _
    exact host_real_read_result reg (some bytes)

theorem host_real_write_result (key value : ByteArray) (reg : Nat) (old : Option ByteArray) :
    HostKeepsReal (storageWriteResult key value reg old) := by
  cases old with
  | none =>
    unfold storageWriteResult
    apply host_real_bind
    · exact host_real_storage_usage _
    intro _
    exact host_real_push_ret 0 true
  | some bytes =>
    unfold storageWriteResult
    apply host_real_bind
    · exact host_real_storage_usage _
    intro _
    exact host_real_read_result reg (some bytes)

theorem host_real_has_key_finish (key : ByteArray) :
    HostKeepsReal (storageHasKeyFinish key) := by
  unfold storageHasKeyFinish
  apply host_real_get_bind
  intro s hs
  cases he : s.real with
  | none => simp [he] at hs
  | some r =>
    simp only [pure_bind]
    apply host_real_bind
    · exact host_real_op r TTN.storageHasKey key
    · intro old
      apply host_real_bind
      · exact host_real_observe
      intro _
      exact host_real_push_ret _ true
    · exact hs

theorem host_real_read_finish (valueByte largeBase largeByte : Cost) (key : ByteArray) (reg : Nat) :
    HostKeepsReal (storageReadFinish valueByte largeBase largeByte key reg) := by
  unfold storageReadFinish
  apply host_real_get_bind
  intro s hs
  cases he : s.real with
  | none => simp [he] at hs
  | some r =>
    simp only [pure_bind]
    apply host_real_bind
    · exact host_real_op r TTN.storageRead key
    · intro old
      apply host_real_bind
      · exact host_real_observe
      intro _
      exact host_real_read_result reg old
    · exact hs

theorem host_real_remove_finish (key : ByteArray) (reg : Nat) :
    HostKeepsReal (storageRemoveFinish key reg) := by
  unfold storageRemoveFinish
  apply host_real_get_bind
  intro s hs
  cases he : s.real with
  | none => simp [he] at hs
  | some r =>
    simp only [pure_bind]
    apply host_real_bind
    · exact host_real_op r TTN.storageRemove key
    · intro old
      apply host_real_bind
      · exact host_real_set r key none
      intro _
      apply host_real_bind
      · exact host_real_record_removal
      intro _
      apply host_real_bind
      · exact host_real_observe
      intro _
      exact host_real_remove_result key reg old
    · exact hs

theorem host_real_write_finish (key value : ByteArray) (reg : Nat) :
    HostKeepsReal (storageWriteFinish key value reg) := by
  unfold storageWriteFinish
  apply host_real_get_bind
  intro s hs
  cases he : s.real with
  | none => simp [he] at hs
  | some r =>
    simp only [pure_bind]
    apply host_real_bind
    · exact host_real_op r TTN.storageWrite key
    · intro old
      apply host_real_bind
      · exact host_real_set r key (some value)
      intro _
      apply host_real_bind
      · exact host_real_observe
      intro _
      exact host_real_write_result key value reg old
    · exact hs

theorem host_real_has_key_code (base hasKey keyByte : Cost) :
    HostKeepsReal (storageHasKeyCode base hasKey keyByte) := by
  unfold storageHasKeyCode
  with_reducible apply host_real_bind
  · with_reducible exact host_real_pop_args 2
  intro args
  with_reducible apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  with_reducible apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  with_reducible apply host_real_bind
  · with_reducible exact host_real_mem_or_reg _ _
  intro key
  dsimp only
  split
  · with_reducible apply host_real_bind
    · exact host_real_throw _
    intro _
    with_reducible apply host_real_bind
    · unfold payPerH
      exact host_real_with_gas _
    intro _
    exact host_real_has_key_finish key
  · with_reducible apply host_real_bind
    · unfold payPerH
      exact host_real_with_gas _
    intro _
    exact host_real_has_key_finish key

/-- Definitional correspondence to the actual dispatch, not a replacement VM. -/
theorem actual_storage_has_key_keeps_real (call : HM Unit)
    (hcall : hostCall "storage_has_key" = some call) : HostKeepsReal call := by
  rw [actual_storage_has_key_code] at hcall
  cases Option.some.inj hcall
  with_reducible exact host_real_has_key_code C.base C.storageHasKeyBase C.storageHasKeyByte

/-- Exact register/stack result sequence used by storage_read. -/
theorem host_real_read_code (base readBase keyByte valueByte largeBase largeByte : Cost) :
    HostKeepsReal (storageReadCode base readBase keyByte valueByte largeBase largeByte) := by
  unfold storageReadCode
  with_reducible apply host_real_bind
  · with_reducible exact host_real_pop_args 3
  intro args
  with_reducible apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  with_reducible apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  with_reducible apply host_real_bind
  · with_reducible exact host_real_mem_or_reg _ _
  intro key
  dsimp only
  split
  · with_reducible apply host_real_bind
    · exact host_real_throw _
    intro _
    with_reducible apply host_real_bind
    · unfold payPerH
      exact host_real_with_gas _
    intro _
    exact host_real_read_finish valueByte largeBase largeByte key args[2]
  · with_reducible apply host_real_bind
    · unfold payPerH
      exact host_real_with_gas _
    intro _
    exact host_real_read_finish valueByte largeBase largeByte key args[2]

theorem actual_storage_read_keeps_real (call : HM Unit)
    (hcall : hostCall "storage_read" = some call) : HostKeepsReal call := by
  rw [actual_storage_read_code] at hcall
  cases Option.some.inj hcall
  with_reducible exact host_real_read_code C.base C.storageReadBase C.storageReadKeyByte C.storageReadValueByte C.storageLargeReadOverheadBase C.storageLargeReadOverheadByte

theorem host_real_remove_code (base removeBase keyByte : Cost) :
    HostKeepsReal (storageRemoveCode base removeBase keyByte) := by
  unfold storageRemoveCode
  with_reducible apply host_real_bind
  · with_reducible exact host_real_pop_args 3
  intro args
  with_reducible apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  with_reducible apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  with_reducible apply host_real_bind
  · with_reducible exact host_real_mem_or_reg _ _
  intro key
  dsimp only
  split
  · with_reducible apply host_real_bind
    · exact host_real_throw _
    intro _
    with_reducible apply host_real_bind
    · unfold payPerH
      exact host_real_with_gas _
    intro _
    exact host_real_remove_finish key args[2]
  · with_reducible apply host_real_bind
    · unfold payPerH
      exact host_real_with_gas _
    intro _
    exact host_real_remove_finish key args[2]

theorem actual_storage_remove_keeps_real (call : HM Unit)
    (hcall : hostCall "storage_remove" = some call) : HostKeepsReal call := by
  rw [actual_storage_remove_code] at hcall
  cases Option.some.inj hcall
  with_reducible exact host_real_remove_code C.base C.storageRemoveBase C.storageRemoveKeyByte

theorem host_real_write_charged_finish (keyByte valueByte : Cost) (key value : ByteArray) (reg : Nat) :
    HostKeepsReal (storageWriteChargedFinish keyByte valueByte key value reg) := by
  unfold storageWriteChargedFinish
  with_reducible apply host_real_bind
  · unfold payPerH
    exact host_real_with_gas _
  intro _
  with_reducible apply host_real_bind
  · unfold payPerH
    exact host_real_with_gas _
  intro _
  exact host_real_write_finish key value reg

theorem host_real_write_value_code (keyByte valueByte : Cost) (key : ByteArray) (args : Vector Nat 5) :
    HostKeepsReal (storageWriteValueCode keyByte valueByte key args) := by
  unfold storageWriteValueCode
  with_reducible apply host_real_bind
  · with_reducible exact host_real_mem_or_reg _ _
  intro value
  dsimp only
  split
  · with_reducible apply host_real_bind
    · exact host_real_throw _
    intro _
    exact host_real_write_charged_finish keyByte valueByte key value args[4]
  · exact host_real_write_charged_finish keyByte valueByte key value args[4]

theorem host_real_write_code (base writeBase keyByte valueByte : Cost) :
    HostKeepsReal (storageWriteCode base writeBase keyByte valueByte) := by
  unfold storageWriteCode
  with_reducible apply host_real_bind
  · with_reducible exact host_real_pop_args 5
  intro args
  with_reducible apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  with_reducible apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  with_reducible apply host_real_bind
  · with_reducible exact host_real_mem_or_reg _ _
  intro key
  dsimp only
  split
  · with_reducible apply host_real_bind
    · exact host_real_throw _
    intro _
    exact host_real_write_value_code keyByte valueByte key args
  · exact host_real_write_value_code keyByte valueByte key args

theorem actual_storage_write_keeps_real (call : HM Unit)
    (hcall : hostCall "storage_write" = some call) : HostKeepsReal call := by
  rw [actual_storage_write_code] at hcall
  cases Option.some.inj hcall
  with_reducible exact host_real_write_code C.base C.storageWriteBase C.storageWriteKeyByte C.storageWriteValueByte

end NearCompression
