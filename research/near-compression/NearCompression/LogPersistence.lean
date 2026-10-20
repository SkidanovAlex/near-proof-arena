import NearCompression.YieldCreationPersistence

/-! Logging and panic persistence, including bounded decoders and charged failures. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem host_real_log_len_exceeded {A : Type} (add : Nat) :
    HostKeepsReal (logLenExceeded (α := A) add) := by
  unfold logLenExceeded
  apply host_real_get_bind
  intro s hs
  exact hs

theorem host_real_check_can_log : HostKeepsReal checkCanLogH := by
  unfold checkCanLogH
  apply host_real_get_bind
  intro s hs
  split <;> exact hs

theorem host_real_append_log (bytes : ByteArray) : HostKeepsReal (appendLog bytes) := by
  intro s hs
  exact hs

theorem host_real_checked_append_log (bytes : ByteArray) (total : Nat) :
    HostKeepsReal (checkedAppendLog bytes total) := by
  unfold checkedAppendLog
  split
  · apply host_real_bind
    · exact host_real_log_len_exceeded bytes.size
    intro _
    exact host_real_append_log bytes
  · exact host_real_append_log bytes

theorem host_real_push_log (msg : String) : HostKeepsReal (pushLogH msg) := by
  unfold pushLogH
  apply host_real_get_bind
  intro s hs
  apply host_real_bind
  · exact host_real_set_state _ hs
  · intro _
    exact host_real_checked_append_log msg.toUTF8 _
  · exact hs

theorem host_real_guest_panic {A : Type} (msg : String) :
    HostKeepsReal (guestPanic (α := A) msg) := by
  unfold guestPanic
  exact host_real_throw _

theorem panic_code_keeps_real (base : Cost) : HostKeepsReal (panicCode base) := by
  unfold panicCode
  apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  exact host_real_guest_panic _

theorem actual_panic_keeps_real (call : HM Unit) (hc : hostCall "panic" = some call) : HostKeepsReal call := by
  rw [actual_panic_code] at hc
  cases Option.some.inj hc
  with_reducible exact panic_code_keeps_real C.base

theorem utf16_buffer_keeps_real (base byte : Cost) (maxLen len ptr : Nat) :
    HostKeepsReal (utf16Buffer base byte maxLen len ptr) := by
  unfold utf16Buffer
  split
  · with_reducible apply host_real_bind
    · apply host_real_for_in
      intro i acc
      rcases acc with ⟨fin, l⟩
      dsimp only
      split
      · exact host_real_pure _
      · with_reducible apply host_real_bind
        · exact host_real_charged_read base byte _ 2
        intro word
        split
        · exact host_real_pure _
        · split
          · apply host_real_bind
            · exact host_real_log_len_exceeded _
            intro _
            exact host_real_pure _
          · exact host_real_pure _
    intro acc
    apply host_real_get_bind
    intro s hs
    split <;> exact hs
  · with_reducible apply host_real_bind
    · exact host_real_charged_read base byte ptr len
    intro bytes
    exact host_real_pure _

theorem utf16_decoded_keeps_real (byte : Cost) (len : Nat) (d : ByteArray) :
    HostKeepsReal (utf16Decoded byte len d) := by
  unfold utf16Decoded
  apply host_real_bind
  · unfold payPerH
    exact host_real_with_gas _
  intro _
  split
  · exact host_real_pure _
  · exact host_real_throw _

theorem utf16_length_checked_keeps_real (byte : Cost) (maxLen len : Nat) (d : ByteArray) :
    HostKeepsReal (utf16LengthChecked byte maxLen len d) := by
  unfold utf16LengthChecked
  split
  · apply host_real_bind
    · exact host_real_log_len_exceeded len
    intro _
    exact utf16_decoded_keeps_real byte len d
  · exact utf16_decoded_keeps_real byte len d

theorem utf16_finish_keeps_real (byte : Cost) (maxLen len : Nat) (d : ByteArray) :
    HostKeepsReal (utf16Finish byte maxLen len d) := by
  unfold utf16Finish
  split
  · apply host_real_bind
    · exact host_real_throw _
    intro _
    exact utf16_length_checked_keeps_real byte maxLen len d
  · exact utf16_length_checked_keeps_real byte maxLen len d

theorem utf16_code_keeps_real (base byte memoryBase memoryByte : Cost) (len ptr : Nat) :
    HostKeepsReal (utf16Code base byte memoryBase memoryByte len ptr) := by
  unfold utf16Code
  apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  apply host_real_get_bind
  intro s hs
  apply host_real_bind
  · exact utf16_buffer_keeps_real memoryBase memoryByte _ len ptr
  · intro buf
    exact utf16_finish_keeps_real byte _ buf.1 buf.2
  · exact hs

theorem host_real_utf16 (len ptr : Nat) : HostKeepsReal (utf16H len ptr) := by
  rw [actual_utf16_code]
  with_reducible exact utf16_code_keeps_real C.utf16DecodingBase C.utf16DecodingByte C.readMemoryBase C.readMemoryByte len ptr

theorem decoded_log_code_keeps_real (base logBase logByte : Cost) (decode : Nat → Nat → HM String)
    (decoderSim : ∀ len ptr, HostKeepsReal (decode len ptr)) :
    HostKeepsReal (decodedLogCode base logBase logByte decode) := by
  unfold decodedLogCode
  apply host_real_bind
  · exact host_real_pop_args 2
  intro args
  apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact host_real_check_can_log
  intro _
  apply host_real_bind
  · exact decoderSim args[0] args[1]
  intro msg
  apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  apply host_real_bind
  · unfold payPerH
    exact host_real_with_gas _
  intro _
  exact host_real_push_log msg

theorem actual_log_utf16_keeps_real (call : HM Unit) (hc : hostCall "log_utf16" = some call) :
    HostKeepsReal call := by
  rw [actual_log_utf16_code] at hc
  cases Option.some.inj hc
  with_reducible exact decoded_log_code_keeps_real C.base C.logBase C.logByte utf16H host_real_utf16

theorem utf8_accumulate_keeps_real (maxLen i : Nat) (b : ByteArray) (done : Bool) (el : UInt8) :
    HostKeepsReal (utf8Accumulate maxLen i b done el) := by
  unfold utf8Accumulate
  split
  · exact host_real_pure _
  · split
    · apply host_real_bind
      · exact host_real_log_len_exceeded _
      intro _
      exact host_real_pure _
    · exact host_real_pure _

theorem utf8_scan_step_keeps_real (base byte : Cost) (maxLen ptr i : Nat) (acc : ByteArray × Bool) :
    HostKeepsReal (utf8ScanStep base byte maxLen ptr i acc) := by
  unfold utf8ScanStep
  split
  · exact host_real_pure _
  · apply host_real_bind
    · unfold payBaseH
      exact host_real_with_gas _
    intro _
    apply host_real_bind
    · unfold payPerH
      exact host_real_with_gas _
    intro _
    apply host_real_get_bind
    intro s hs
    split
    · simp only [host_error_bind]; exact hs
    · exact utf8_accumulate_keeps_real maxLen i acc.1 acc.2 _ s hs

theorem utf8_buffer_keeps_real (base byte : Cost) (maxLen len ptr : Nat) :
    HostKeepsReal (utf8Buffer base byte maxLen len ptr) := by
  unfold utf8Buffer
  split
  · split
    · apply host_real_bind
      · exact host_real_log_len_exceeded len
      intro _
      exact host_real_charged_read base byte ptr len
    · exact host_real_charged_read base byte ptr len
  · apply host_real_bind
    · apply host_real_for_in
      intro i acc
      exact utf8_scan_step_keeps_real base byte maxLen ptr i acc
    intro acc
    exact host_real_pure acc.1

theorem utf8_finish_keeps_real (byte : Cost) (buf : ByteArray) :
    HostKeepsReal (utf8Finish byte buf) := by
  unfold utf8Finish
  apply host_real_bind
  · unfold payPerH
    exact host_real_with_gas _
  intro _
  split
  · exact host_real_pure _
  · exact host_real_throw _

theorem utf8_code_keeps_real (base byte memoryBase memoryByte : Cost) (len ptr : Nat) :
    HostKeepsReal (utf8Code base byte memoryBase memoryByte len ptr) := by
  unfold utf8Code
  apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  apply host_real_get_bind
  intro s hs
  apply host_real_bind
  · exact utf8_buffer_keeps_real memoryBase memoryByte _ len ptr
  · intro buf
    exact utf8_finish_keeps_real byte buf
  · exact hs

theorem host_real_utf8 (len ptr : Nat) : HostKeepsReal (utf8H len ptr) := by
  rw [actual_utf8_code]
  with_reducible exact utf8_code_keeps_real C.utf8DecodingBase C.utf8DecodingByte C.readMemoryBase C.readMemoryByte len ptr

theorem actual_log_utf8_keeps_real (call : HM Unit) (hc : hostCall "log_utf8" = some call) :
    HostKeepsReal call := by
  rw [actual_log_utf8_code] at hc
  cases Option.some.inj hc
  with_reducible exact decoded_log_code_keeps_real C.base C.logBase C.logByte utf8H host_real_utf8

theorem decoded_panic_code_keeps_real (base : Cost) (decode : Nat → Nat → HM String)
    (decoderSim : ∀ len ptr, HostKeepsReal (decode len ptr)) :
    HostKeepsReal (decodedPanicCode base decode) := by
  unfold decodedPanicCode
  apply host_real_bind
  · exact host_real_pop_args 2
  intro args
  apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact decoderSim args[0] args[1]
  intro msg
  exact host_real_guest_panic msg

theorem actual_panic_utf8_keeps_real (call : HM Unit) (hc : hostCall "panic_utf8" = some call) :
    HostKeepsReal call := by
  rw [actual_panic_utf8_code] at hc
  cases Option.some.inj hc
  with_reducible exact decoded_panic_code_keeps_real C.base utf8H host_real_utf8

theorem abort_finish_keeps_real (logBase logByte : Cost) (msg file : String) (line col : Nat) :
    HostKeepsReal (abortFinish logBase logByte msg file line col) := by
  unfold abortFinish
  apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  apply host_real_bind
  · unfold payPerH
    exact host_real_with_gas _
  intro _
  apply host_real_bind
  · exact host_real_push_log _
  intro _
  exact host_real_guest_panic _

theorem abort_read_keeps_real (logBase logByte : Cost) (read : Nat → Nat → HM ByteArray)
    (decode : Nat → Nat → HM String)
    (readSim : ∀ ptr len, HostKeepsReal (read ptr len))
    (decodeSim : ∀ len ptr, HostKeepsReal (decode len ptr)) (mp fp line col : Nat) :
    HostKeepsReal (abortRead logBase logByte read decode mp fp line col) := by
  unfold abortRead
  apply host_real_bind
  · exact host_real_check_can_log
  intro _
  apply host_real_bind
  · exact readSim _ 4
  intro ml
  apply host_real_bind
  · exact readSim _ 4
  intro fl
  apply host_real_bind
  · exact decodeSim _ mp
  intro msg
  apply host_real_bind
  · exact decodeSim _ fp
  intro file
  exact abort_finish_keeps_real logBase logByte msg file line col

theorem abort_code_keeps_real (base logBase logByte : Cost) (read : Nat → Nat → HM ByteArray)
    (decode : Nat → Nat → HM String)
    (readSim : ∀ ptr len, HostKeepsReal (read ptr len))
    (decodeSim : ∀ len ptr, HostKeepsReal (decode len ptr)) :
    HostKeepsReal (abortCode base logBase logByte read decode) := by
  unfold abortCode
  apply host_real_bind
  · exact host_real_pop_args 4
  intro a
  apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  dsimp only
  split
  · apply host_real_bind
    · exact host_real_throw _
    intro _
    exact abort_read_keeps_real logBase logByte read decode readSim decodeSim _ _ _ _
  · exact abort_read_keeps_real logBase logByte read decode readSim decodeSim _ _ _ _

theorem actual_abort_keeps_real (call : HM Unit) (hc : hostCall "abort" = some call) : HostKeepsReal call := by
  rw [actual_abort_code] at hc
  cases Option.some.inj hc
  with_reducible exact abort_code_keeps_real C.base C.logBase C.logByte readMemH utf16H host_real_read_mem host_real_utf16

end NearCompression
