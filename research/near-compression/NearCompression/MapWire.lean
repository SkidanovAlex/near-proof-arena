import NearCompression.StorageWire

/-! Map byte decoding reconstructs logical entries, not physical hash buckets.
The encoding is not claimed canonical across equivalent bucket layouts. -/
namespace NearCompression
open NearSpec NearSpecV3

local instance : LawfulBEq ByteArray where
  eq_of_beq := byte_array_beq_eq _ _
  rfl := by intro a; change (a.data == a.data) = true; exact BEq.rfl

def mapWireWf {V : Type} (wv : V → Prop) (m : Std.HashMap ByteArray V) : Prop :=
  m.toList.length < 4294967296 ∧ ∀ p ∈ m.toList, pairWireWf bytesWireWf wv p

def encodeMapWire {V : Type} (ev : V → Bytes) (m : Std.HashMap ByteArray V) : Bytes :=
  encList (encodePairWire encodeBytesWire ev) m.toList

def parseMapWire {V : Type} (pv : P V) : P (Std.HashMap ByteArray V) := fun bs => do
  let (pairs, bs) ← pVec "map" (parsePairWire parseBytesWire pv) bs
  pure (Std.HashMap.ofList pairs, bs)

theorem map_wire_roundtrip {V : Type} (ev : V → Bytes) (pv : P V) (wv : V → Prop)
    (rv : ∀ v, wv v → ∀ rest, pv (ev v ++ rest) = .ok (v, rest))
    (m : Std.HashMap ByteArray V) (wf : mapWireWf wv m) (rest : Bytes) :
    parseMapWire pv (encodeMapWire ev m ++ rest) = .ok (rebuildMap m, rest) := by
  simp only [parseMapWire, encodeMapWire]
  rw [pVec_ok _ _ _ _ _ wf.1 (fun p hp tail =>
    pair_wire_roundtrip _ _ _ _ _ _ bytes_wire_roundtrip rv p (wf.2 p hp) tail)]
  rfl

theorem map_wire_observed_roundtrip {V : Type} (ev : V → Bytes) (pv : P V) (wv : V → Prop)
    (rv : ∀ v, wv v → ∀ rest, pv (ev v ++ rest) = .ok (v, rest))
    (m : Std.HashMap ByteArray V) (wf : mapWireWf wv m) (rest : Bytes) :
    ∃ decoded, parseMapWire pv (encodeMapWire ev m ++ rest) = .ok (decoded, rest) ∧ decoded.Equiv m :=
  ⟨rebuildMap m, map_wire_roundtrip ev pv wv rv m wf rest, rebuild_map_equiv m⟩

theorem map_wire_alias_equiv {V : Type} (ev : V → Bytes) (pv : P V) (wv : V → Prop)
    (rv : ∀ v, wv v → ∀ rest, pv (ev v ++ rest) = .ok (v, rest))
    (a b : Std.HashMap ByteArray V) (ha : mapWireWf wv a) (hb : mapWireWf wv b)
    (same : encodeMapWire ev a = encodeMapWire ev b) : a.Equiv b := by
  have h := congrArg (fun bs => parseMapWire pv (bs ++ [])) same
  rw [map_wire_roundtrip ev pv wv rv a ha [], map_wire_roundtrip ev pv wv rv b hb []] at h
  have eqMaps : rebuildMap a = rebuildMap b := congrArg Prod.fst (Except.ok.inj h)
  apply Std.HashMap.Equiv.of_forall_getElem?_eq
  intro k
  have h1 := (rebuild_map_equiv a).getElem?_eq (k := k)
  have h2 := (rebuild_map_equiv b).getElem?_eq (k := k)
  rw [eqMaps] at h1
  exact h1.symm.trans h2

def overlayWireWf := mapWireWf optionalBytesWireWf
def encodeOverlayWire := encodeMapWire encodeOptionalBytesWire
def parseOverlayWire := parseMapWire parseOptionalBytesWire

theorem overlay_wire_roundtrip (m : Std.HashMap ByteArray (Option ByteArray))
    (wf : overlayWireWf m) (rest : Bytes) :
    parseOverlayWire (encodeOverlayWire m ++ rest) = .ok (rebuildMap m, rest) :=
  map_wire_roundtrip _ _ _ optional_bytes_wire_roundtrip m wf rest

def unitWireWf (_ : Unit) : Prop := True
def encodeUnitWire (_ : Unit) : Bytes := []
def parseUnitWire : P Unit := fun bs => .ok ((), bs)

theorem unit_wire_roundtrip (v : Unit) (_ : unitWireWf v) (rest : Bytes) :
    parseUnitWire (encodeUnitWire v ++ rest) = .ok (v, rest) := by cases v; rfl

def keySetWireWf := mapWireWf unitWireWf
def encodeKeySetWire := encodeMapWire encodeUnitWire
def parseKeySetWire := parseMapWire parseUnitWire

theorem key_set_wire_roundtrip (m : Std.HashMap ByteArray Unit)
    (wf : keySetWireWf m) (rest : Bytes) :
    parseKeySetWire (encodeKeySetWire m ++ rest) = .ok (rebuildMap m, rest) :=
  map_wire_roundtrip _ _ _ unit_wire_roundtrip m wf rest

end NearCompression
