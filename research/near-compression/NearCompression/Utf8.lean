import NearCompression.LogHost

/-! UTF-8 host simulation including the exact null-terminated byte scan. -/
namespace NearCompression
open NearSpecV3.Wasm

def utf8Accumulate (maxLen i : Nat) (b : ByteArray) (done : Bool) (el : UInt8) :
    HM (ForInStep (ByteArray × Bool)) := do
  if el = 0 then pure (.yield (b, true))
  else
    if i = maxLen then logLenExceeded (maxLen + 1)
    pure (.yield (b.push el, done))

theorem utf8_accumulate_sim (maxLen i : Nat) (b : ByteArray) (done : Bool) (el : UInt8) :
    HostSim (utf8Accumulate maxLen i b done el) (utf8Accumulate maxLen i b done el) := by
  unfold utf8Accumulate
  split
  · exact host_sim_pure _
  · split
    · apply host_sim_bind
      · exact host_sim_log_len_exceeded _
      intro _
      exact host_sim_pure _
    · exact host_sim_pure _

def utf8ScanStep (base byte : Cost) (maxLen ptr i : Nat) (acc : ByteArray × Bool) :
    HM (ForInStep (ByteArray × Bool)) := do
  if acc.2 then pure (.done acc)
  else
    payBaseH base
    payPerH byte 1
    let s ← get
    if ptr + i ≥ memBytes s then hErr "MemoryAccessViolation"
    utf8Accumulate maxLen i acc.1 acc.2 (readByte s (ptr + i))

theorem utf8_scan_step_sim (base byte : Cost) (maxLen ptr i : Nat) (acc : ByteArray × Bool) :
    HostSim (utf8ScanStep base byte maxLen ptr i acc) (utf8ScanStep base byte maxLen ptr i acc) := by
  unfold utf8ScanStep
  split
  · exact host_sim_pure _
  · apply host_sim_bind
    · unfold payBaseH
      exact host_sim_with_gas _
    intro _
    apply host_sim_bind
    · unfold payPerH
      exact host_sim_with_gas _
    intro _
    apply host_sim_get_bind
    intro s t h
    rw [state_equiv_mem_bytes s t h, state_equiv_read_byte s t h]
    split
    · apply host_bind_equiv
      · exact host_sim_error _ s t h
      intro _ u v huv
      exact utf8_accumulate_sim maxLen i acc.1 acc.2 _ u v huv
    · exact utf8_accumulate_sim maxLen i acc.1 acc.2 _ s t h

def utf8Buffer (base byte : Cost) (maxLen len ptr : Nat) : HM ByteArray := do
  if len ≠ u64Bound - 1 then
    if len > maxLen then logLenExceeded len
    chargedRead base byte ptr len
  else
    let acc ← forIn [0:maxLen + 1] (ByteArray.empty, false) (utf8ScanStep base byte maxLen ptr)
    pure acc.1

theorem utf8_buffer_sim (base byte : Cost) (maxLen len ptr : Nat) :
    HostSim (utf8Buffer base byte maxLen len ptr) (utf8Buffer base byte maxLen len ptr) := by
  unfold utf8Buffer
  split
  · split
    · apply host_sim_bind
      · exact host_sim_log_len_exceeded len
      intro _
      exact host_sim_charged_read base byte ptr len
    · exact host_sim_charged_read base byte ptr len
  · apply host_sim_bind
    · apply host_sim_for_in
      intro i acc
      exact utf8_scan_step_sim base byte maxLen ptr i acc
    intro acc
    exact host_sim_pure acc.1

def utf8Finish (byte : Cost) (buf : ByteArray) : HM String := do
  payPerH byte buf.size
  match String.fromUTF8? buf with
  | some str => pure str
  | none => hErr "BadUTF8"

theorem utf8_finish_sim (byte : Cost) (buf : ByteArray) :
    HostSim (utf8Finish byte buf) (utf8Finish byte buf) := by
  unfold utf8Finish
  apply host_sim_bind
  · unfold payPerH
    exact host_sim_with_gas _
  intro _
  split
  · exact host_sim_pure _
  · exact host_sim_error _

def utf8Code (base byte memoryBase memoryByte : Cost) (len ptr : Nat) : HM String := do
  payBaseH base
  let maxLen := maxTotalLogLength - (← get).totalLogLen
  let buf ← utf8Buffer memoryBase memoryByte maxLen len ptr
  utf8Finish byte buf

theorem utf8_code_sim (base byte memoryBase memoryByte : Cost) (len ptr : Nat) :
    HostSim (utf8Code base byte memoryBase memoryByte len ptr)
      (utf8Code base byte memoryBase memoryByte len ptr) := by
  unfold utf8Code
  apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  apply host_sim_get_bind
  intro s t h
  have hl : s.totalLogLen = t.totalLogLen := by have he := congrArg St.totalLogLen h.core; exact he
  rw [hl]
  apply host_bind_equiv
  · exact utf8_buffer_sim memoryBase memoryByte _ len ptr s t h
  intro buf u v huv
  exact utf8_finish_sim byte buf u v huv

theorem actual_utf8_code (len ptr : Nat) : utf8H len ptr =
    utf8Code C.utf8DecodingBase C.utf8DecodingByte C.readMemoryBase C.readMemoryByte len ptr := by
  unfold utf8H utf8Code utf8Buffer utf8ScanStep utf8Accumulate utf8Finish
  simp only [readMemH, chargedRead, logLenExceeded, bind_assoc, pure_bind, host_bind_if, host_error_bind]
  rfl

theorem host_sim_utf8 (len ptr : Nat) : HostSim (utf8H len ptr) (utf8H len ptr) := by
  rw [actual_utf8_code]
  with_reducible exact utf8_code_sim C.utf8DecodingBase C.utf8DecodingByte C.readMemoryBase C.readMemoryByte len ptr

end NearCompression
