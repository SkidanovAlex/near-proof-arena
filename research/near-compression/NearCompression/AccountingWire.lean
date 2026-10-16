import NearCompression.MapWire

/-! Accounting caches and recorder sets round-trip up to logical map equivalence. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def acctWireWf (a : TTN.Acct) : Prop :=
  keySetWireWf a.cache ∧ a.db < 340282366920938463463374607431768211456 ∧ a.mem < 340282366920938463463374607431768211456

def encodeAcctWire (a : TTN.Acct) : Bytes :=
  encodeKeySetWire a.cache ++ u128 a.db ++ u128 a.mem

def parseAcctWire : NearSpecV3.P TTN.Acct := fun bs => do
  let (cache, bs) ← parseKeySetWire bs
  let (db, bs) ← pU128 "acct db" bs
  let (mem, bs) ← pU128 "acct mem" bs
  pure ({ cache, db, mem }, bs)

theorem acct_wire_roundtrip (a : TTN.Acct) (wf : acctWireWf a) (rest : Bytes) :
    parseAcctWire (encodeAcctWire a ++ rest) = .ok (normalizeAcct a, rest) := by
  obtain ⟨hkeys, hdb, hmem⟩ := wf
  simp only [parseAcctWire, encodeAcctWire, List.append_assoc]
  rw [key_set_wire_roundtrip _ hkeys]
  simp only [bind, Except.bind]
  rw [pU128_ok _ _ _ hdb]
  simp only [bind, Except.bind]
  rw [pU128_ok _ _ _ hmem]
  simp only [bind, Except.bind]
  rfl

theorem acct_wire_observed_roundtrip (a : TTN.Acct) (wf : acctWireWf a) (rest : Bytes) :
    ∃ decoded, parseAcctWire (encodeAcctWire a ++ rest) = .ok (decoded, rest) ∧ AcctEquivalent decoded a :=
  ⟨normalizeAcct a, acct_wire_roundtrip a wf rest, normalize_acct_equiv a⟩

def recorderWireWf (a : TTN.Recorder) : Prop :=
  keySetWireWf a.set ∧ a.size < 340282366920938463463374607431768211456

def encodeRecorderWire (a : TTN.Recorder) : Bytes :=
  encodeKeySetWire a.set ++ u128 a.size

def parseRecorderWire : NearSpecV3.P TTN.Recorder := fun bs => do
  let (set, bs) ← parseKeySetWire bs
  let (size, bs) ← pU128 "recorder size" bs
  pure ({ set, size }, bs)

theorem recorder_wire_roundtrip (a : TTN.Recorder) (wf : recorderWireWf a) (rest : Bytes) :
    parseRecorderWire (encodeRecorderWire a ++ rest) = .ok (normalizeRecorder a, rest) := by
  obtain ⟨hkeys, hsize⟩ := wf
  simp only [parseRecorderWire, encodeRecorderWire, List.append_assoc]
  rw [key_set_wire_roundtrip _ hkeys]
  simp only [bind, Except.bind]
  rw [pU128_ok _ _ _ hsize]
  simp only [bind, Except.bind]
  rfl

theorem recorder_wire_observed_roundtrip (a : TTN.Recorder) (wf : recorderWireWf a) (rest : Bytes) :
    ∃ decoded, parseRecorderWire (encodeRecorderWire a ++ rest) = .ok (decoded, rest) ∧ RecorderEquivalent decoded a :=
  ⟨normalizeRecorder a, recorder_wire_roundtrip a wf rest, normalize_recorder_equiv a⟩

end NearCompression
