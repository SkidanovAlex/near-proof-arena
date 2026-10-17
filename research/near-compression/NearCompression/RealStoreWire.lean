import NearCompression.AccountingWire

/-! All finite real-store fields serialized. The function-valued immutable store
is supplied by a fixed context and is not authenticated by this codec alone. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def normalizeRealBoundary (r : RealBoundary) : RealBoundary :=
  { r with overlay := rebuildMap r.overlay, acct := normalizeAcct r.acct, recd := normalizeRecorder r.recd }

def realBoundaryWireWf (r : RealBoundary) : Prop :=
  bytesWireWf r.root ∧ overlayWireWf r.overlay ∧ acctWireWf r.acct ∧
  bytesWireWf r.pfx ∧ recorderWireWf r.recd ∧
  r.recBefore < 340282366920938463463374607431768211456 ∧ writesWireWf r.writes

def encodeRealBoundaryWire (r : RealBoundary) : Bytes :=
  encodeBytesWire r.root ++ encodeOverlayWire r.overlay ++ encodeAcctWire r.acct ++
  encodeBytesWire r.pfx ++ encodeRecorderWire r.recd ++ u128 r.recBefore ++ encodeWritesWire r.writes

def parseRealBoundaryWire : NearSpecV3.P RealBoundary := fun bs => do
  let (root, bs) ← parseBytesWire bs
  let (overlay, bs) ← parseOverlayWire bs
  let (acct, bs) ← parseAcctWire bs
  let (pfx, bs) ← parseBytesWire bs
  let (recd, bs) ← parseRecorderWire bs
  let (recBefore, bs) ← pU128 "recording snapshot" bs
  let (writes, bs) ← parseWritesWire bs
  pure ({ root, overlay, acct, pfx, recd, recBefore, writes }, bs)

theorem real_boundary_wire_roundtrip (r : RealBoundary) (wf : realBoundaryWireWf r) (rest : Bytes) :
    parseRealBoundaryWire (encodeRealBoundaryWire r ++ rest) = .ok (normalizeRealBoundary r, rest) := by
  obtain ⟨hroot, hoverlay, hacct, hpfx, hrecd, hbefore, hwrites⟩ := wf
  simp only [parseRealBoundaryWire, encodeRealBoundaryWire, List.append_assoc]
  rw [bytes_wire_roundtrip _ hroot]
  simp only [bind, Except.bind]
  rw [overlay_wire_roundtrip _ hoverlay]
  simp only [bind, Except.bind]
  rw [acct_wire_roundtrip _ hacct]
  simp only [bind, Except.bind]
  rw [bytes_wire_roundtrip _ hpfx]
  simp only [bind, Except.bind]
  rw [recorder_wire_roundtrip _ hrecd]
  simp only [bind, Except.bind]
  rw [pU128_ok _ _ _ hbefore]
  simp only [bind, Except.bind]
  rw [writes_wire_roundtrip _ hwrites]
  rfl

theorem restore_normalized_real_boundary (store : TTN.Store) (r : RealBoundary) :
    restoreReal store (normalizeRealBoundary r) = normalizeReal (restoreReal store r) := rfl

theorem real_boundary_wire_observed_roundtrip (store : TTN.Store)
    (r : RealBoundary) (wf : realBoundaryWireWf r) (rest : Bytes) :
    ∃ decoded, parseRealBoundaryWire (encodeRealBoundaryWire r ++ rest) = .ok (decoded, rest) ∧
      RealEquivalent (restoreReal store decoded) (restoreReal store r) := by
  refine ⟨normalizeRealBoundary r, real_boundary_wire_roundtrip r wf rest, ?_⟩
  rw [restore_normalized_real_boundary]
  exact normalized_real_equiv _

theorem real_boundary_wire_alias_equiv (store : TTN.Store) (a b : RealBoundary)
    (ha : realBoundaryWireWf a) (hb : realBoundaryWireWf b)
    (same : encodeRealBoundaryWire a = encodeRealBoundaryWire b) :
    RealEquivalent (restoreReal store a) (restoreReal store b) := by
  have h := congrArg (fun bs => parseRealBoundaryWire (bs ++ [])) same
  rw [real_boundary_wire_roundtrip a ha [], real_boundary_wire_roundtrip b hb []] at h
  have eqBounds : normalizeRealBoundary a = normalizeRealBoundary b := congrArg Prod.fst (Except.ok.inj h)
  have he : normalizeReal (restoreReal store a) = normalizeReal (restoreReal store b) :=
    congrArg (restoreReal store) eqBounds
  have hnorm := normalized_real_equiv (restoreReal store a)
  rw [he] at hnorm
  exact real_equiv_trans _ _ _ (real_equiv_symm _ _ hnorm) (normalized_real_equiv _)

def optionalRealBoundaryWireWf := optionWireWf realBoundaryWireWf
def encodeOptionalRealBoundaryWire := encodeOptionWire encodeRealBoundaryWire
def parseOptionalRealBoundaryWire := parseOptionWire parseRealBoundaryWire

theorem optional_real_boundary_wire_roundtrip (r : Option RealBoundary)
    (wf : optionalRealBoundaryWireWf r) (rest : Bytes) :
    parseOptionalRealBoundaryWire (encodeOptionalRealBoundaryWire r ++ rest) =
      .ok (r.map normalizeRealBoundary, rest) := by
  cases r with
  | none => rfl
  | some r =>
    simp only [parseOptionalRealBoundaryWire, parseOptionWire, encodeOptionalRealBoundaryWire,
      encodeOptionWire, encOpt, List.append_assoc, pOption]
    have tag := pU8_ok ("optional" ++ " option tag") 1 (encodeRealBoundaryWire r ++ rest) (by decide)
    change pU8 ("optional" ++ " option tag") ([1] ++ (encodeRealBoundaryWire r ++ rest)) = _ at tag
    rw [tag]
    simp only [bind, Except.bind]
    rw [real_boundary_wire_roundtrip r (wf r rfl) rest]
    rfl

end NearCompression
