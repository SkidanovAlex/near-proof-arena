import NearCompression.GKRFixedInputEnvelope
import NearCompression.GKRContinuationFailure
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Compose the existing finite layered evaluator across a layer boundary. -/
theorem gkr_finite_circuit_append (inputs : Nat → K)
    (first rest : List (List GKRWiringGate)) :
    gkrFiniteCircuit inputs (first++rest)=gkrFiniteCircuit (gkrFiniteCircuit inputs first) rest := by
  induction first generalizing inputs with
  | nil => rfl
  | cons gates tail ih =>
    simp only [List.cons_append,gkrFiniteCircuit]
    exact ih _

/-- Circuit values in the output-to-input order used by GKR. All values are
computed from one input assignment, not supplied independently at each layer. -/
def gkrReverseCircuitValues (inputs : Nat → K) (layers : List (List GKRWiringGate))
    (depth : Nat) : Nat → K :=
  gkrFiniteCircuit inputs (layers.take (layers.length-depth))

def gkrReverseCircuitWiring (layers : List (List GKRWiringGate))
    (depth i : Nat) : GKRWiringGate :=
  ((layers.getD (layers.length-(depth+1)) []).getD i ⟨.add,0,0⟩)

theorem gkr_reverse_circuit_output (inputs : Nat → K) (layers : List (List GKRWiringGate)) :
    gkrReverseCircuitValues inputs layers 0=gkrFiniteCircuit inputs layers := by
  simp [gkrReverseCircuitValues]

theorem gkr_reverse_circuit_input (inputs : Nat → K) (layers : List (List GKRWiringGate)) :
    gkrReverseCircuitValues inputs layers layers.length=inputs := by
  simp [gkrReverseCircuitValues,gkrFiniteCircuit]

/-- Every actual layer entry agrees with the fixed-wiring evaluation needed
by the GKR path theorem. No independently trusted layer-value equality remains. -/
theorem gkr_reverse_circuit_step (inputs : Nat → K) (layers : List (List GKRWiringGate))
    (depth : Nat) (bound : depth<layers.length) (i : Nat)
    (entryBound : i<(layers.getD (layers.length-(depth+1)) []).length) :
    gkrReverseCircuitValues inputs layers depth i=
      gkrLayerValues (gkrReverseCircuitValues inputs layers (depth+1))
        (gkrReverseCircuitWiring layers depth) i := by
  let j := layers.length-(depth+1)
  have hj : j<layers.length := by dsimp [j]; omega
  have next : layers.length-depth=j+1 := by dsimp [j]; omega
  have gateList : layers.getD j []=layers[j] := by simp [List.getD,hj]
  have hi : i<(layers[j]).length := by simpa only [show layers.length-(depth+1)=j from rfl,gateList] using entryBound
  have gate : (layers[j]).getD i ⟨.add,0,0⟩=(layers[j])[i] := by simp [List.getD,hi]
  unfold gkrReverseCircuitValues
  rw [next,List.take_succ_eq_append_getElem hj,gkr_finite_circuit_append]
  simp only [gkrFiniteCircuit]
  change (gkrFiniteLayer (gkrFiniteCircuit inputs (layers.take j)) layers[j]).getD i 0=_
  simp only [gkrFiniteLayer,List.getD,List.getElem?_map,List.getElem?_eq_getElem hi,
    Option.map_some,Option.getD_some,gkrLayerValues,gkrReverseCircuitWiring]
  change gkrGateValue ((layers[j])[i]).op _ _=
    gkrGateValue ((layers.getD j []).getD i ⟨.add,0,0⟩).op _ _
  rw [gateList,gate]
  simp only [←show layers.length-(depth+1)=j from rfl]
  simp [show layers.length-(depth+1)<layers.length from hj,show i<(layers[layers.length-(depth+1)]).length from hi]

/-- Construct the input directly from the decoded tuple and known constants. -/
def gkrRecoveredCircuitInput (C : Nat) (entries : List (GKRSourceLane × Poly K))
    (rowpoints : GKRSourceLane → Nat → K) (constants : List (Nat × K)) : Nat → K :=
  fun i => gkrScatter (recoveredPrivateSlots C entries rowpoints) i+gkrScatter constants i

/-- The recovered-terminal adapter no longer asks for an assignment equality:
it follows from actual finite circuit evaluation of the decoded input. Only
alignment of path depth with circuit depth is required. -/
theorem gkr_evaluated_recovered_terminal_mismatch
    (strategy : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (layers : List (List GKRWiringGate)) (rounds : List Nat)
    (blocks history : List (GKRBlock K)) (sameLength : blocks.length=rounds.length)
    (depth : Nat) (aligned : depth+rounds.length=layers.length) (block : GKRBlock K)
    (layout : GKRJointLayout) (entries : List (GKRSourceLane × Poly K))
    (rowpoints : GKRSourceLane → Nat → K) (constants : List (Nat × K)) :
    gkrTerminalMismatch strategy
      (gkrReverseCircuitValues (gkrRecoveredCircuitInput layout.commonLog entries rowpoints constants) layers)
      depth history (rounds++[layout.inputLog]) (blocks++[block]) ↔
      (strategy layout.inputLog (history++blocks)).a block.1 block.2.1+
        block.2.2*(strategy layout.inputLog (history++blocks)).b block.1 block.2.1≠
      gkrInputFunctional layout.inputLog (fun i => block.1.getD i 0) (fun i => block.2.1.getD i 0)
        block.2.2 (gkrRecoveredCircuitInput layout.commonLog entries rowpoints constants) := by
  apply gkr_terminal_recovered_mismatch strategy _ rounds blocks history sameLength depth block
    layout entries rowpoints constants
  rw [aligned,gkr_reverse_circuit_input]
  rfl

end NearCompression
