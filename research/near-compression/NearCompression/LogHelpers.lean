import NearCompression.ReturnHost

/-! Logging helpers preserve counters even when the post-increment limit check
fails. These lemmas are prerequisites for the UTF logging and abort hosts. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem host_sim_log_len_exceeded {A : Type} (add : Nat) :
    HostSim (logLenExceeded (α := A) add) (logLenExceeded add) := by
  unfold logLenExceeded
  apply host_sim_get_bind
  intro s t h
  have hl : s.totalLogLen = t.totalLogLen := by
    have he := congrArg St.totalLogLen h.core
    exact he
  rw [hl]
  exact host_sim_error _ s t h

theorem host_sim_check_can_log : HostSim checkCanLogH checkCanLogH := by
  unfold checkCanLogH
  apply host_sim_get_bind
  intro s t h
  have hl : s.logs = t.logs := by have he := congrArg St.logs h.core; exact he
  rw [hl]
  split
  · exact host_sim_error _ s t h
  · exact ⟨rfl, h⟩

def appendLog (bytes : ByteArray) : HM Unit := modify fun s => { s with logs := s.logs.push bytes }

theorem host_sim_append_log (bytes : ByteArray) : HostSim (appendLog bytes) (appendLog bytes) := by
  intro s t h
  exact ⟨rfl, congrArg (fun s : St => { s with logs := s.logs.push bytes }) h.core, h.real⟩

def checkedAppendLog (bytes : ByteArray) (total : Nat) : HM Unit := do
  if total > maxTotalLogLength then logLenExceeded bytes.size
  appendLog bytes

theorem host_sim_checked_append_log (bytes : ByteArray) (total : Nat) :
    HostSim (checkedAppendLog bytes total) (checkedAppendLog bytes total) := by
  unfold checkedAppendLog
  split
  · apply host_sim_bind
    · exact host_sim_log_len_exceeded bytes.size
    intro _
    exact host_sim_append_log bytes
  · exact host_sim_append_log bytes

theorem host_sim_push_log (msg : String) : HostSim (pushLogH msg) (pushLogH msg) := by
  intro s t h
  unfold pushLogH
  rw [host_get_bind_run, host_get_bind_run]
  have hl : s.totalLogLen = t.totalLogLen := by
    have he := congrArg St.totalLogLen h.core
    exact he
  rw [hl]
  apply host_set_then_equiv s t
    { s with totalLogLen := t.totalLogLen + msg.toUTF8.size }
    { t with totalLogLen := t.totalLogLen + msg.toUTF8.size }
  · exact ⟨congrArg (fun s : St => { s with totalLogLen := t.totalLogLen + msg.toUTF8.size }) h.core, h.real⟩
  · exact host_sim_checked_append_log msg.toUTF8 _

theorem host_sim_guest_panic {A : Type} (msg : String) :
    HostSim (guestPanic (α := A) msg) (guestPanic msg) := by
  unfold guestPanic
  exact host_sim_error _

def panicCode (base : Cost) : HM Unit := do
  payBaseH base
  guestPanic "explicit guest panic"

theorem panic_code_sim (base : Cost) : HostSim (panicCode base) (panicCode base) := by
  unfold panicCode
  apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  exact host_sim_guest_panic _

theorem actual_panic_code : hostCall "panic" = some (panicCode C.base) := by rfl

theorem actual_panic_sim (call : HM Unit) (hc : hostCall "panic" = some call) : HostSim call call := by
  rw [actual_panic_code] at hc
  cases Option.some.inj hc
  with_reducible exact panic_code_sim C.base

end NearCompression
