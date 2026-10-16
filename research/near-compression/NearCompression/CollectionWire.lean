import NearCompression.GasWire

/-! Ordered byte, table and register collections. No sorting or deduplication
is performed: these fields have exact observable order and multiplicity. -/
namespace NearCompression
open NearSpec NearSpecV3

def arrayWireWf {A : Type} (wf : A → Prop) (xs : Array A) : Prop :=
  xs.toList.length < 4294967296 ∧ ∀ x ∈ xs.toList, wf x

def encodeArrayWire {A : Type} (encode : A → Bytes) (xs : Array A) : Bytes :=
  encList encode xs.toList

def parseArrayWire {A : Type} (parse : P A) : P (Array A) := fun bs => do
  let (xs, bs) ← pVec "array" parse bs
  pure (xs.toArray, bs)

theorem array_wire_roundtrip {A : Type} (encode : A → Bytes) (parse : P A) (wf : A → Prop)
    (roundtrip : ∀ x, wf x → ∀ rest, parse (encode x ++ rest) = .ok (x, rest))
    (xs : Array A) (hx : arrayWireWf wf xs) (rest : Bytes) :
    parseArrayWire parse (encodeArrayWire encode xs ++ rest) = .ok (xs, rest) := by
  simp only [parseArrayWire, encodeArrayWire]
  rw [pVec_ok _ _ _ _ _ hx.1 (fun x hm tail => roundtrip x (hx.2 x hm) tail)]
  simp [bind, Except.bind, pure, Except.pure]

def bytesWireWf (b : ByteArray) : Prop := b.data.toList.length < 4294967296

def encodeBytesWire (b : ByteArray) : Bytes := borshBytes b.data.toList

def parseBytesWire : P ByteArray := fun bs => do
  let (xs, bs) ← pBytes "bytes" bs
  pure (ByteArray.mk xs.toArray, bs)

theorem bytes_wire_roundtrip (b : ByteArray) (wf : bytesWireWf b) (rest : Bytes) :
    parseBytesWire (encodeBytesWire b ++ rest) = .ok (b, rest) := by
  simp only [parseBytesWire, encodeBytesWire]
  rw [pBytes_ok _ _ _ wf]
  cases b
  simp [bind, Except.bind, pure, Except.pure]

def byteArraysWireWf := arrayWireWf bytesWireWf
def encodeByteArraysWire := encodeArrayWire encodeBytesWire
def parseByteArraysWire := parseArrayWire parseBytesWire

theorem byte_arrays_wire_roundtrip (xs : Array ByteArray) (wf : byteArraysWireWf xs) (rest : Bytes) :
    parseByteArraysWire (encodeByteArraysWire xs ++ rest) = .ok (xs, rest) :=
  array_wire_roundtrip _ _ _ bytes_wire_roundtrip xs wf rest

def refWireWf (r : Option Nat) : Prop := ∀ n, r = some n → n < 18446744073709551616

def encodeRefWire (r : Option Nat) : Bytes := encOpt u64 r
def parseRefWire : P (Option Nat) := pOption "reference" (pU64 "index")

theorem ref_wire_roundtrip (r : Option Nat) (wf : refWireWf r) (rest : Bytes) :
    parseRefWire (encodeRefWire r ++ rest) = .ok (r, rest) :=
  pOption_ok _ _ _ r rest (fun n hn tail => pU64_ok _ n tail (wf n hn))

def tableWireWf := arrayWireWf refWireWf
def encodeTableWire := encodeArrayWire encodeRefWire
def parseTableWire := parseArrayWire parseRefWire

theorem table_wire_roundtrip (xs : Array (Option Nat)) (wf : tableWireWf xs) (rest : Bytes) :
    parseTableWire (encodeTableWire xs ++ rest) = .ok (xs, rest) :=
  array_wire_roundtrip _ _ _ ref_wire_roundtrip xs wf rest

def elementsWireWf := arrayWireWf tableWireWf
def encodeElementsWire := encodeArrayWire encodeTableWire
def parseElementsWire := parseArrayWire parseTableWire

theorem elements_wire_roundtrip (xs : Array (Array (Option Nat)))
    (wf : elementsWireWf xs) (rest : Bytes) :
    parseElementsWire (encodeElementsWire xs ++ rest) = .ok (xs, rest) :=
  array_wire_roundtrip _ _ _ table_wire_roundtrip xs wf rest

def registerWireWf (r : Nat × ByteArray) : Prop :=
  r.1 < 18446744073709551616 ∧ bytesWireWf r.2

def encodeRegisterWire (r : Nat × ByteArray) : Bytes := u64 r.1 ++ encodeBytesWire r.2

def parseRegisterWire : P (Nat × ByteArray) := fun bs => do
  let (id, bs) ← pU64 "register id" bs
  let (bytes, bs) ← parseBytesWire bs
  pure ((id, bytes), bs)

theorem register_wire_roundtrip (r : Nat × ByteArray) (wf : registerWireWf r) (rest : Bytes) :
    parseRegisterWire (encodeRegisterWire r ++ rest) = .ok (r, rest) := by
  simp only [parseRegisterWire, encodeRegisterWire, List.append_assoc]
  rw [pU64_ok _ _ _ wf.1]
  simp only [bind, Except.bind]
  rw [bytes_wire_roundtrip _ wf.2]
  rfl

def registersWireWf := arrayWireWf registerWireWf
def encodeRegistersWire := encodeArrayWire encodeRegisterWire
def parseRegistersWire := parseArrayWire parseRegisterWire

theorem registers_wire_roundtrip (xs : Array (Nat × ByteArray))
    (wf : registersWireWf xs) (rest : Bytes) :
    parseRegistersWire (encodeRegistersWire xs ++ rest) = .ok (xs, rest) :=
  array_wire_roundtrip _ _ _ register_wire_roundtrip xs wf rest

end NearCompression
