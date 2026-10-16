import NearCompression.ResultWire

/-! Derive intermediate backing invariants from execution, then instantiate the
concrete wire theorem. This does not authenticate the shared external context. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

/-- Range/length bounds only: no backing or decoding assumption is hidden here. -/
def boundaryPayloadsFit (input : Res) (ws : List SegmentWitness) (output : Res) : Prop :=
  ∀ a b, (a, b) ∈ boundaryLinks input ws output →
    resultBoundaryWireWf (captureResult a) ∧ resultBoundaryWireWf (captureResult b)

theorem backed_wire_boundaries (context : ExecutionContext) (input output : Res)
    (ws : List SegmentWitness)
    (hi : Logged.W.ResOK (boundaryStore context.backing) input)
    (ho : Logged.W.ResOK (boundaryStore context.backing) output)
    (hs : ∀ w ∈ ws, Logged.W.StOK (boundaryStore context.backing) w.start)
    (valid : ∀ w ∈ ws, LocalValid context.cfg context.program w)
    (fits : boundaryPayloadsFit input ws output) :
    executionBoundaryWireWf (boundaryStore context.backing) input ws output := by
  intro a b hab
  obtain ⟨ha, hb⟩ := boundary_links_backed context input output ws hi ho hs valid a b hab
  exact ⟨⟨(fits a b hab).1, ha⟩, ⟨(fits a b hab).2, hb⟩⟩

theorem restored_result_backed (store : TTN.Store) (r : ResultBoundary) :
    Logged.W.ResOK store (restoreResult store r) := by
  unfold Logged.W.ResOK
  rw [← restore_capture_result, capture_restore_result]

/-- Finite starts reconstruct under the common backing context. Finishes remain
actual execution results: their backing invariant follows from local validity. -/
structure FiniteStartSegment where
  steps : Nat
  start : StateBoundary
  finish : Res

def restoreStartSegment (context : ExecutionContext) (w : FiniteStartSegment) : SegmentWitness :=
  ⟨w.steps, restoreState (boundaryStore context.backing) w.start, w.finish⟩

theorem restored_segment_starts_backed (context : ExecutionContext)
    (ws : List FiniteStartSegment) :
    ∀ w ∈ ws.map (restoreStartSegment context),
      Logged.W.StOK (boundaryStore context.backing) w.start := by
  intro w hw
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hw
  exact restored_state_backed _ _

/-- No per-finish backing premise and no abstract byte decoder. The theorem
still requires valid local execution and explicit encoding bounds. -/
theorem finite_start_wire_run_or_hash_collision {Digest : Type}
    (context : ExecutionContext) (hash : Bytes → Digest)
    (checked : checkRealWrapperImports context.program = true)
    (start : StateBoundary) (ws : List FiniteStartSegment) (output : ResultBoundary)
    (real : (restoreState (boundaryStore context.backing) start).real.isSome = true)
    (remainingFuel : Nat)
    (cert : CertifiedChain (fun r => hash (encodeExecutionResultWire r))
      context.cfg context.program (.cont (restoreState (boundaryStore context.backing) start))
      (ws.map (restoreStartSegment context)) (restoreResult (boundaryStore context.backing) output))
    (fits : boundaryPayloadsFit (.cont (restoreState (boundaryStore context.backing) start))
      (ws.map (restoreStartSegment context)) (restoreResult (boundaryStore context.backing) output)) :
    ResultEquivalent
      (run context.cfg context.program
        (((ws.map (restoreStartSegment context)).map SegmentWitness.steps).sum + remainingFuel)
        (restoreState (boundaryStore context.backing) start))
      ((restoreResult (boundaryStore context.backing) output).bind
        (run context.cfg context.program remainingFuel)) ∨
    ∃ a b, (a, b) ∈ boundaryLinks (.cont (restoreState (boundaryStore context.backing) start))
        (ws.map (restoreStartSegment context)) (restoreResult (boundaryStore context.backing) output) ∧
      encodeExecutionResultWire a ≠ encodeExecutionResultWire b ∧
      hash (encodeExecutionResultWire a) = hash (encodeExecutionResultWire b) := by
  apply encoded_real_run_or_hash_collision hash (boundaryStore context.backing)
    context.cfg context.program checked _ real _ _ remainingFuel cert
  apply backed_wire_boundaries context _ _ _ _
    (restored_result_backed _ output) (restored_segment_starts_backed context ws) cert.1 fits
  exact restored_result_backed _ (.cont start)

end NearCompression
