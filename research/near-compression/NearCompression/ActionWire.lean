import NearCompression.ContextWire

/-! Action metadata and return data preserve optional and variant distinctions. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def stateInitWireWf := pairWireWf nat128WireWf byteArraysWireWf
def encodeStateInitWire := encodePairWire u128 encodeByteArraysWire
def parseStateInitWire := parsePairWire (pU128 "counter") parseByteArraysWire

theorem state_init_wire_roundtrip (v : Nat × Array ByteArray) (wf : stateInitWireWf v) (rest : Bytes) :
    parseStateInitWire (encodeStateInitWire v ++ rest) = .ok (v, rest) :=
  pair_wire_roundtrip _ _ _ _ _ _ nat128_wire_roundtrip byte_arrays_wire_roundtrip v wf rest

def actionWireWf (a : MAct) : Prop :=
  stringWireWf a.text ∧ optionWireWf stringWireWf a.receiver ∧
  optionWireWf writeEntryWireWf a.yieldCreate ∧ optionWireWf stateInitWireWf a.stateInit

def encodeActionWire (a : MAct) : Bytes :=
  encodeStringWire a.text ++ encodeOptionWire encodeStringWire a.receiver ++
  encodeOptionWire encodeWriteEntryWire a.yieldCreate ++ encodeOptionWire encodeStateInitWire a.stateInit

def parseActionWire : NearSpecV3.P MAct := fun bs => do
  let (text, bs) ← parseStringWire bs
  let (receiver, bs) ← parseOptionWire parseStringWire bs
  let (yieldCreate, bs) ← parseOptionWire parseWriteEntryWire bs
  let (stateInit, bs) ← parseOptionWire parseStateInitWire bs
  pure ({ text, receiver, yieldCreate, stateInit }, bs)

theorem action_wire_roundtrip (a : MAct) (wf : actionWireWf a) (rest : Bytes) :
    parseActionWire (encodeActionWire a ++ rest) = .ok (a, rest) := by
  obtain ⟨ht, hr, hy, hs⟩ := wf
  simp only [parseActionWire, encodeActionWire, List.append_assoc]
  rw [string_wire_roundtrip _ ht]
  simp only [bind, Except.bind]
  rw [option_wire_roundtrip _ _ _ string_wire_roundtrip _ hr]
  simp only [bind, Except.bind]
  rw [option_wire_roundtrip _ _ _ write_entry_wire_roundtrip _ hy]
  simp only [bind, Except.bind]
  rw [option_wire_roundtrip _ _ _ state_init_wire_roundtrip _ hs]
  rfl

def actionsWireWf := arrayWireWf actionWireWf
def encodeActionsWire := encodeArrayWire encodeActionWire
def parseActionsWire := parseArrayWire parseActionWire

theorem actions_wire_roundtrip (xs : Array MAct) (wf : actionsWireWf xs) (rest : Bytes) :
    parseActionsWire (encodeActionsWire xs ++ rest) = .ok (xs, rest) :=
  array_wire_roundtrip _ _ _ action_wire_roundtrip xs wf rest

def returnValueWireWf : ByteArray ⊕ Nat → Prop
  | .inl b => bytesWireWf b
  | .inr n => nat128WireWf n

def encodeReturnValueWire : ByteArray ⊕ Nat → Bytes
  | .inl b => u8 0 ++ encodeBytesWire b
  | .inr n => u8 1 ++ u128 n

def parseReturnValueWire : NearSpecV3.P (ByteArray ⊕ Nat) := fun bs => do
  let (tag, bs) ← pU8 "return value" bs
  match tag with
  | 0 => let (b, bs) ← parseBytesWire bs; pure (.inl b, bs)
  | 1 => let (n, bs) ← pU128 "counter" bs; pure (.inr n, bs)
  | _ => throw "invalid return value tag"

theorem return_value_wire_roundtrip (v : ByteArray ⊕ Nat) (wf : returnValueWireWf v) (rest : Bytes) :
    parseReturnValueWire (encodeReturnValueWire v ++ rest) = .ok (v, rest) := by
  cases v with
  | inl b =>
    simp only [parseReturnValueWire, encodeReturnValueWire, List.append_assoc]
    rw [pU8_ok _ _ _ (by decide)]
    simp only [bind, Except.bind]
    rw [bytes_wire_roundtrip _ wf]
    rfl
  | inr n =>
    simp only [parseReturnValueWire, encodeReturnValueWire, List.append_assoc]
    rw [pU8_ok _ _ _ (by decide)]
    simp only [bind, Except.bind]
    rw [nat128_wire_roundtrip _ wf]
    rfl

def returnWireWf := optionWireWf returnValueWireWf
def encodeReturnWire := encodeOptionWire encodeReturnValueWire
def parseReturnWire := parseOptionWire parseReturnValueWire

theorem return_wire_roundtrip (v : Option (ByteArray ⊕ Nat)) (wf : returnWireWf v) (rest : Bytes) :
    parseReturnWire (encodeReturnWire v ++ rest) = .ok (v, rest) :=
  option_wire_roundtrip _ _ _ return_value_wire_roundtrip v wf rest

theorem return_wire_injective (a b : Option (ByteArray ⊕ Nat)) (ha : returnWireWf a) (hb : returnWireWf b)
    (same : encodeReturnWire a = encodeReturnWire b) : a = b := by
  have h := congrArg (fun bs => parseReturnWire (bs ++ [])) same
  rw [return_wire_roundtrip a ha [], return_wire_roundtrip b hb []] at h
  exact congrArg Prod.fst (Except.ok.inj h)

end NearCompression
