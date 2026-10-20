import NearCompression.RealStoreWire

/-! UTF-8 strings and promise outcomes used by the actual call context. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def stringWireWf (s : String) : Prop := bytesWireWf s.toUTF8
def encodeStringWire (s : String) : Bytes := encodeBytesWire s.toUTF8

def parseStringWire : NearSpecV3.P String := fun bs => do
  let (bytes, bs) ← parseBytesWire bs
  match String.fromUTF8? bytes with
  | some s => pure (s, bs)
  | none => throw "invalid boundary UTF-8"

theorem string_utf8_roundtrip (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  unfold String.fromUTF8?
  split
  · rfl
  · rename_i hn
    exact False.elim (hn s.isValidUTF8)

theorem string_wire_roundtrip (s : String) (wf : stringWireWf s) (rest : Bytes) :
    parseStringWire (encodeStringWire s ++ rest) = .ok (s, rest) := by
  simp only [parseStringWire, encodeStringWire]
  rw [bytes_wire_roundtrip _ wf]
  simp only [bind, Except.bind, string_utf8_roundtrip]
  rfl

def promiseResultWireWf : PRes → Prop
  | .notReady | .failed => True
  | .ok bytes => bytesWireWf bytes

def encodePromiseResultWire : PRes → Bytes
  | .notReady => u8 0
  | .ok bytes => u8 1 ++ encodeBytesWire bytes
  | .failed => u8 2

def parsePromiseResultWire : NearSpecV3.P PRes := fun bs => do
  let (tag, bs) ← pU8 "promise result" bs
  match tag with
  | 0 => pure (.notReady, bs)
  | 1 => let (bytes, bs) ← parseBytesWire bs; pure (.ok bytes, bs)
  | 2 => pure (.failed, bs)
  | _ => throw "invalid promise result tag"

theorem promise_result_wire_roundtrip (r : PRes) (wf : promiseResultWireWf r) (rest : Bytes) :
    parsePromiseResultWire (encodePromiseResultWire r ++ rest) = .ok (r, rest) := by
  cases r <;> simp only [parsePromiseResultWire, encodePromiseResultWire, List.append_assoc]
  all_goals rw [pU8_ok _ _ _ (by decide)]
  all_goals first
    | rfl
    | (simp only [bind, Except.bind]; rw [bytes_wire_roundtrip _ wf]; rfl)

theorem promise_result_wire_injective (a b : PRes) (ha : promiseResultWireWf a) (hb : promiseResultWireWf b)
    (same : encodePromiseResultWire a = encodePromiseResultWire b) : a = b := by
  have h := congrArg (fun bs => parsePromiseResultWire (bs ++ [])) same
  rw [promise_result_wire_roundtrip a ha [], promise_result_wire_roundtrip b hb []] at h
  exact congrArg Prod.fst (Except.ok.inj h)

end NearCompression
