import NearCompression.CollectionWire

/-! Storage bytes distinguish deletion from empty values and retain write order.
Logical-map reconstruction and backing-context authentication remain separate. -/
namespace NearCompression
open NearSpec NearSpecV3

def optionWireWf {A : Type} (wf : A → Prop) (o : Option A) : Prop :=
  ∀ a, o = some a → wf a

def encodeOptionWire {A : Type} (encode : A → Bytes) (o : Option A) : Bytes := encOpt encode o

def parseOptionWire {A : Type} (parse : P A) : P (Option A) := pOption "optional" parse

theorem option_wire_roundtrip {A : Type} (encode : A → Bytes) (parse : P A) (wf : A → Prop)
    (roundtrip : ∀ a, wf a → ∀ rest, parse (encode a ++ rest) = .ok (a, rest))
    (o : Option A) (ho : optionWireWf wf o) (rest : Bytes) :
    parseOptionWire parse (encodeOptionWire encode o ++ rest) = .ok (o, rest) :=
  pOption_ok _ _ _ o rest (fun a ha tail => roundtrip a (ho a ha) tail)

def pairWireWf {A B : Type} (wa : A → Prop) (wb : B → Prop) (p : A × B) : Prop :=
  wa p.1 ∧ wb p.2

def encodePairWire {A B : Type} (ea : A → Bytes) (eb : B → Bytes) (p : A × B) : Bytes :=
  ea p.1 ++ eb p.2

def parsePairWire {A B : Type} (pa : P A) (pb : P B) : P (A × B) := fun bs => do
  let (a, bs) ← pa bs
  let (b, bs) ← pb bs
  pure ((a, b), bs)

theorem pair_wire_roundtrip {A B : Type} (ea : A → Bytes) (eb : B → Bytes)
    (pa : P A) (pb : P B) (wa : A → Prop) (wb : B → Prop)
    (ra : ∀ a, wa a → ∀ rest, pa (ea a ++ rest) = .ok (a, rest))
    (rb : ∀ b, wb b → ∀ rest, pb (eb b ++ rest) = .ok (b, rest))
    (p : A × B) (hp : pairWireWf wa wb p) (rest : Bytes) :
    parsePairWire pa pb (encodePairWire ea eb p ++ rest) = .ok (p, rest) := by
  simp only [parsePairWire, encodePairWire, List.append_assoc]
  rw [ra _ hp.1]
  simp only [bind, Except.bind]
  rw [rb _ hp.2]
  rfl

def optionalBytesWireWf := optionWireWf bytesWireWf
def encodeOptionalBytesWire := encodeOptionWire encodeBytesWire
def parseOptionalBytesWire := parseOptionWire parseBytesWire

theorem optional_bytes_wire_roundtrip (o : Option ByteArray)
    (wf : optionalBytesWireWf o) (rest : Bytes) :
    parseOptionalBytesWire (encodeOptionalBytesWire o ++ rest) = .ok (o, rest) :=
  option_wire_roundtrip _ _ _ bytes_wire_roundtrip o wf rest

def storageEntryWireWf := pairWireWf bytesWireWf bytesWireWf
def encodeStorageEntryWire := encodePairWire encodeBytesWire encodeBytesWire
def parseStorageEntryWire := parsePairWire parseBytesWire parseBytesWire

theorem storage_entry_wire_roundtrip (p : ByteArray × ByteArray)
    (wf : storageEntryWireWf p) (rest : Bytes) :
    parseStorageEntryWire (encodeStorageEntryWire p ++ rest) = .ok (p, rest) :=
  pair_wire_roundtrip _ _ _ _ _ _ bytes_wire_roundtrip bytes_wire_roundtrip p wf rest

def trieWireWf := arrayWireWf storageEntryWireWf
def encodeTrieWire := encodeArrayWire encodeStorageEntryWire
def parseTrieWire := parseArrayWire parseStorageEntryWire

theorem trie_wire_roundtrip (xs : Array (ByteArray × ByteArray))
    (wf : trieWireWf xs) (rest : Bytes) :
    parseTrieWire (encodeTrieWire xs ++ rest) = .ok (xs, rest) :=
  array_wire_roundtrip _ _ _ storage_entry_wire_roundtrip xs wf rest

def writeEntryWireWf := pairWireWf bytesWireWf optionalBytesWireWf
def encodeWriteEntryWire := encodePairWire encodeBytesWire encodeOptionalBytesWire
def parseWriteEntryWire := parsePairWire parseBytesWire parseOptionalBytesWire

theorem write_entry_wire_roundtrip (p : ByteArray × Option ByteArray)
    (wf : writeEntryWireWf p) (rest : Bytes) :
    parseWriteEntryWire (encodeWriteEntryWire p ++ rest) = .ok (p, rest) :=
  pair_wire_roundtrip _ _ _ _ _ _ bytes_wire_roundtrip optional_bytes_wire_roundtrip p wf rest

def writesWireWf := arrayWireWf writeEntryWireWf
def encodeWritesWire := encodeArrayWire encodeWriteEntryWire
def parseWritesWire := parseArrayWire parseWriteEntryWire

theorem writes_wire_roundtrip (xs : Array (ByteArray × Option ByteArray))
    (wf : writesWireWf xs) (rest : Bytes) :
    parseWritesWire (encodeWritesWire xs ++ rest) = .ok (xs, rest) :=
  array_wire_roundtrip _ _ _ write_entry_wire_roundtrip xs wf rest

theorem deletion_empty_value_distinct :
    encodeOptionalBytesWire none ≠ encodeOptionalBytesWire (some ByteArray.empty) := by
  decide +kernel

theorem writes_wire_injective (a b : Array (ByteArray × Option ByteArray))
    (ha : writesWireWf a) (hb : writesWireWf b)
    (same : encodeWritesWire a = encodeWritesWire b) : a = b := by
  have h := congrArg (fun bs => parseWritesWire (bs ++ [])) same
  rw [writes_wire_roundtrip a ha [], writes_wire_roundtrip b hb []] at h
  exact congrArg Prod.fst (Except.ok.inj h)

end NearCompression
