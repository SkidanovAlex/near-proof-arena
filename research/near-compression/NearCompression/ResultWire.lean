import NearCompression.StateWire

/-! Versioned whole-result encoding. Bounds and fixed-context authentication are
explicit; successful parsing is not itself a proof of valid execution. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def decodeComplete {α : Type} (parse : NearSpecV3.P α) (bs : Bytes) : Except String α := do
  let (a, rest) ← parse bs
  if rest.isEmpty then pure a else throw "trailing payload bytes"

theorem decode_complete_roundtrip {α : Type} (parse : NearSpecV3.P α)
    (bs : Bytes) (a : α) (h : parse (bs ++ []) = .ok (a, [])) :
    decodeComplete parse bs = .ok a := by
  simp only [List.append_nil] at h
  simp [decodeComplete, h]
  rfl

def resultBoundaryEnvelope : ResultBoundary → BoundaryEnvelope
  | .cont s => .cont (encodeStateBoundaryWire s)
  | .fin s => .fin (encodeStateBoundaryWire s)
  | .abort s e => .abort (encodeStateBoundaryWire s) (encodeStringWire e)
  | .unmodeled e => .unmodeled (encodeStringWire e)

def resultPayloadWireWf : ResultBoundary → Prop
  | .cont s | .fin s => stateBoundaryWireWf s
  | .abort s e => stateBoundaryWireWf s ∧ stringWireWf e
  | .unmodeled e => stringWireWf e

def resultBoundaryWireWf (r : ResultBoundary) : Prop :=
  resultPayloadWireWf r ∧ (resultBoundaryEnvelope r).wf

def normalizeResultBoundaryWire : ResultBoundary → ResultBoundary
  | .cont s => .cont (normalizeStateBoundaryWire s)
  | .fin s => .fin (normalizeStateBoundaryWire s)
  | .abort s e => .abort (normalizeStateBoundaryWire s) e
  | .unmodeled e => .unmodeled e

def decodeResultPayload : BoundaryEnvelope → Except String ResultBoundary
  | .cont bs => do return .cont (← decodeComplete parseStateBoundaryWire bs)
  | .fin bs => do return .fin (← decodeComplete parseStateBoundaryWire bs)
  | .abort bs es => do
    let s ← decodeComplete parseStateBoundaryWire bs
    let e ← decodeComplete parseStringWire es
    return .abort s e
  | .unmodeled es => do return .unmodeled (← decodeComplete parseStringWire es)

def encodeResultBoundaryWire (r : ResultBoundary) : Bytes := (resultBoundaryEnvelope r).encode

def decodeResultBoundaryWire (bs : Bytes) : Except String ResultBoundary := do
  decodeResultPayload (← decodeBoundaryEnvelope bs)

theorem result_payload_wire_roundtrip (r : ResultBoundary) (wf : resultPayloadWireWf r) :
    decodeResultPayload (resultBoundaryEnvelope r) = .ok (normalizeResultBoundaryWire r) := by
  cases r with
  | cont s =>
    simp [resultBoundaryEnvelope, decodeResultPayload, normalizeResultBoundaryWire,
      decode_complete_roundtrip _ _ _ (state_boundary_wire_roundtrip s wf [])]
    rfl
  | fin s =>
    simp [resultBoundaryEnvelope, decodeResultPayload, normalizeResultBoundaryWire,
      decode_complete_roundtrip _ _ _ (state_boundary_wire_roundtrip s wf [])]
    rfl
  | abort s e =>
    simp [resultBoundaryEnvelope, decodeResultPayload, normalizeResultBoundaryWire,
      decode_complete_roundtrip _ _ _ (state_boundary_wire_roundtrip s wf.1 []),
      decode_complete_roundtrip _ _ _ (string_wire_roundtrip e wf.2 [])]
    rfl
  | unmodeled e =>
    simp [resultBoundaryEnvelope, decodeResultPayload, normalizeResultBoundaryWire,
      decode_complete_roundtrip _ _ _ (string_wire_roundtrip e wf [])]
    rfl

theorem result_boundary_wire_roundtrip (r : ResultBoundary) (wf : resultBoundaryWireWf r) :
    decodeResultBoundaryWire (encodeResultBoundaryWire r) = .ok (normalizeResultBoundaryWire r) := by
  simp only [decodeResultBoundaryWire, encodeResultBoundaryWire,
    boundary_envelope_decode_encode _ wf.2, bind, Except.bind]
  exact result_payload_wire_roundtrip r wf.1

theorem restore_normalized_result_boundary (store : TTN.Store) (r : ResultBoundary) :
    ResultEquivalent (restoreResult store (normalizeResultBoundaryWire r)) (restoreResult store r) := by
  cases r with
  | cont s =>
    change StateEquivalent (restoreState store (normalizeStateBoundaryWire s)) (restoreState store s)
    rw [restore_normalized_state_boundary]
    exact normalized_state_equiv _
  | fin s =>
    change StateEquivalent (restoreState store (normalizeStateBoundaryWire s)) (restoreState store s)
    rw [restore_normalized_state_boundary]
    exact normalized_state_equiv _
  | abort s e =>
    change StateEquivalent (restoreState store (normalizeStateBoundaryWire s)) (restoreState store s) ∧ e = e
    exact ⟨by rw [restore_normalized_state_boundary]; exact normalized_state_equiv _, rfl⟩
  | unmodeled e => rfl

theorem result_boundary_wire_observed_roundtrip (store : TTN.Store) (r : ResultBoundary)
    (wf : resultBoundaryWireWf r) :
    ∃ decoded, decodeResultBoundaryWire (encodeResultBoundaryWire r) = .ok decoded ∧
      ResultEquivalent (restoreResult store decoded) (restoreResult store r) :=
  ⟨_, result_boundary_wire_roundtrip r wf, restore_normalized_result_boundary store r⟩

theorem result_boundary_wire_rejects_suffix (r : ResultBoundary) (wf : resultBoundaryWireWf r)
    (suffix : Bytes) (hne : suffix ≠ []) :
    decodeResultBoundaryWire (encodeResultBoundaryWire r ++ suffix) = .error "trailing boundary bytes" := by
  simp only [decodeResultBoundaryWire, encodeResultBoundaryWire,
    boundary_envelope_rejects_suffix _ wf.2 suffix hne, bind, Except.bind]

def encodeExecutionResultWire (r : Res) : Bytes := encodeResultBoundaryWire (captureResult r)
def decodeExecutionResultWire (store : TTN.Store) (bs : Bytes) : Option Res :=
  (decodeResultBoundaryWire bs).toOption.map (restoreResult store)

def executionResultWireWf (store : TTN.Store) (r : Res) : Prop :=
  resultBoundaryWireWf (captureResult r) ∧ Logged.W.ResOK store r

theorem execution_result_wire_observed_decodes (store : TTN.Store) (r : Res)
    (wf : executionResultWireWf store r) :
    ObservedDecodes encodeExecutionResultWire (decodeExecutionResultWire store) r := by
  refine ⟨restoreResult store (normalizeResultBoundaryWire (captureResult r)), ?_, ?_⟩
  · simp only [decodeExecutionResultWire, encodeExecutionResultWire,
      result_boundary_wire_roundtrip _ wf.1]
    rfl
  · have h := restore_normalized_result_boundary store (captureResult r)
    rw [backed_result_roundtrip store r wf.2] at h
    exact result_equiv_symm _ _ h

def executionBoundaryWireWf (store : TTN.Store) (input : Res)
    (ws : List SegmentWitness) (output : Res) : Prop :=
  ∀ a b, (a, b) ∈ boundaryLinks input ws output →
    executionResultWireWf store a ∧ executionResultWireWf store b

theorem execution_boundary_wire_observed_decodes (store : TTN.Store) (input : Res)
    (ws : List SegmentWitness) (output : Res)
    (wf : executionBoundaryWireWf store input ws output) :
    ObservedBoundaryDecodes encodeExecutionResultWire (decodeExecutionResultWire store) input ws output := by
  intro a b hab
  exact ⟨execution_result_wire_observed_decodes store a (wf a b hab).1,
    execution_result_wire_observed_decodes store b (wf a b hab).2⟩

/-- Concrete byte codec replaces the abstract decoder premise. Local execution,
representability, and common backing store remain required. No quantum extraction
or cryptographic soundness is asserted by this deterministic theorem. -/
theorem encoded_real_run_or_hash_collision {Digest : Type} (hash : Bytes → Digest)
    (store : TTN.Store) (cfg : NearCfg) (p : Prepared)
    (checked : checkRealWrapperImports p = true) (start : St)
    (real : start.real.isSome = true) (ws : List SegmentWitness)
    (output : Res) (remainingFuel : Nat)
    (cert : CertifiedChain (fun r => hash (encodeExecutionResultWire r)) cfg p (.cont start) ws output)
    (wf : executionBoundaryWireWf store (.cont start) ws output) :
    ResultEquivalent (run cfg p ((ws.map SegmentWitness.steps).sum + remainingFuel) start)
      (output.bind (run cfg p remainingFuel)) ∨
    ∃ a b, (a, b) ∈ boundaryLinks (.cont start) ws output ∧
      encodeExecutionResultWire a ≠ encodeExecutionResultWire b ∧
      hash (encodeExecutionResultWire a) = hash (encodeExecutionResultWire b) := by
  exact checked_real_run_or_hash_collision hash encodeExecutionResultWire
    (decodeExecutionResultWire store) cfg p checked start real ws output remainingFuel cert
    (execution_boundary_wire_observed_decodes store (.cont start) ws output wf)

end NearCompression
