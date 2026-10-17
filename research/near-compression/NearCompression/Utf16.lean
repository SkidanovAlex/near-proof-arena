import NearCompression.LogHelpers

/-! UTF-16 host simulation, retaining the actual bounded scan and decoder. -/
namespace NearCompression
open NearSpecV3.Wasm

def utf16Buffer (base byte : Cost) (maxLen len ptr : Nat) : HM (Nat × ByteArray) := do
  if len = u64Bound - 1 then do
    let mut l := 0
    let mut fin := false
    for _ in [0:maxLen / 2 + 2] do
      if fin then break
      let w ← chargedRead base byte (ptr + l) 2
      if w.toList.all (· = 0) then fin := true
      else
        l := l + 2
        if l > maxLen then logLenExceeded l
    let s ← get
    if ptr + l > memBytes s then hErr "MemoryAccessViolation"
    pure (l, readBytes s ptr l)
  else do
    let d ← chargedRead base byte ptr len
    pure (len, d)

theorem utf16_buffer_sim (base byte : Cost) (maxLen len ptr : Nat) :
    HostSim (utf16Buffer base byte maxLen len ptr) (utf16Buffer base byte maxLen len ptr) := by
  unfold utf16Buffer
  split
  · with_reducible apply host_sim_bind
    · apply host_sim_for_in
      intro i acc
      rcases acc with ⟨fin, l⟩
      dsimp only
      split
      · exact host_sim_pure _
      · with_reducible apply host_sim_bind
        · exact host_sim_charged_read base byte _ 2
        intro word
        split
        · exact host_sim_pure _
        · split
          · apply host_sim_bind
            · exact host_sim_log_len_exceeded _
            intro _
            exact host_sim_pure _
          · exact host_sim_pure _
    intro acc
    apply host_sim_get_bind
    intro s t h
    rw [state_equiv_mem_bytes s t h, state_equiv_read_bytes s t h]
    split
    · apply host_bind_equiv
      · exact host_sim_error _ s t h
      intro _ u v huv
      exact ⟨rfl, huv⟩
    · exact ⟨rfl, h⟩
  · with_reducible apply host_sim_bind
    · exact host_sim_charged_read base byte ptr len
    intro bytes
    exact host_sim_pure _

def utf16Decoded (byte : Cost) (len : Nat) (d : ByteArray) : HM String := do
  payPerH byte len
  match decodeUtf16 d with
  | some str => pure str
  | none => hErr "BadUTF16"

theorem utf16_decoded_sim (byte : Cost) (len : Nat) (d : ByteArray) :
    HostSim (utf16Decoded byte len d) (utf16Decoded byte len d) := by
  unfold utf16Decoded
  apply host_sim_bind
  · unfold payPerH
    exact host_sim_with_gas _
  intro _
  split
  · exact host_sim_pure _
  · exact host_sim_error _

def utf16LengthChecked (byte : Cost) (maxLen len : Nat) (d : ByteArray) : HM String := do
  if len > maxLen then logLenExceeded len
  utf16Decoded byte len d

theorem utf16_length_checked_sim (byte : Cost) (maxLen len : Nat) (d : ByteArray) :
    HostSim (utf16LengthChecked byte maxLen len d) (utf16LengthChecked byte maxLen len d) := by
  unfold utf16LengthChecked
  split
  · apply host_sim_bind
    · exact host_sim_log_len_exceeded len
    intro _
    exact utf16_decoded_sim byte len d
  · exact utf16_decoded_sim byte len d

def utf16Finish (byte : Cost) (maxLen len : Nat) (d : ByteArray) : HM String := do
  if d.size % 2 ≠ 0 then hErr "BadUTF16"
  utf16LengthChecked byte maxLen len d

theorem utf16_finish_sim (byte : Cost) (maxLen len : Nat) (d : ByteArray) :
    HostSim (utf16Finish byte maxLen len d) (utf16Finish byte maxLen len d) := by
  unfold utf16Finish
  split
  · apply host_sim_bind
    · exact host_sim_error _
    intro _
    exact utf16_length_checked_sim byte maxLen len d
  · exact utf16_length_checked_sim byte maxLen len d

def utf16Code (base byte memoryBase memoryByte : Cost) (len ptr : Nat) : HM String := do
  payBaseH base
  let maxLen := maxTotalLogLength - (← get).totalLogLen
  let (len, d) ← utf16Buffer memoryBase memoryByte maxLen len ptr
  utf16Finish byte maxLen len d

theorem utf16_code_sim (base byte memoryBase memoryByte : Cost) (len ptr : Nat) :
    HostSim (utf16Code base byte memoryBase memoryByte len ptr)
      (utf16Code base byte memoryBase memoryByte len ptr) := by
  unfold utf16Code
  apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  apply host_sim_get_bind
  intro s t h
  have hl : s.totalLogLen = t.totalLogLen := by have he := congrArg St.totalLogLen h.core; exact he
  rw [hl]
  apply host_bind_equiv
  · exact utf16_buffer_sim memoryBase memoryByte _ len ptr s t h
  intro pair u v huv
  exact utf16_finish_sim byte _ pair.1 pair.2 u v huv

theorem host_bind_if {A B : Type} (condition : Prop) [Decidable condition]
    (yes no : HM A) (next : A → HM B) :
    ((if condition then yes else no) >>= next) =
      (if condition then yes >>= next else no >>= next) := by
  split <;> rfl

theorem host_error_bind {A B : Type} (message : String) (next : A → HM B) :
    (hErr message >>= next) = hErr message := by rfl

theorem actual_utf16_code (len ptr : Nat) : utf16H len ptr =
    utf16Code C.utf16DecodingBase C.utf16DecodingByte C.readMemoryBase C.readMemoryByte len ptr := by
  unfold utf16H utf16Code utf16Buffer utf16Finish utf16LengthChecked utf16Decoded
  simp only [readMemH, chargedRead]
  simp only [logLenExceeded, bind_assoc, pure_bind, host_bind_if, host_error_bind]
  rfl

theorem host_sim_utf16 (len ptr : Nat) : HostSim (utf16H len ptr) (utf16H len ptr) := by
  rw [actual_utf16_code]
  with_reducible exact utf16_code_sim C.utf16DecodingBase C.utf16DecodingByte C.readMemoryBase C.readMemoryByte len ptr

end NearCompression
