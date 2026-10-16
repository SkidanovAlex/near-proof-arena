import NearCompression.GKROutputWeights
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

/-- The executable helper relocates only references to the old final zero slot. -/
def gkrEnvelopeIndex (oldSize newSize index : Nat) : Nat :=
  if index=oldSize-1 then newSize-1 else index

def gkrEnvelopeValues (oldSize : Nat) (values : Nat → K) (index : Nat) : K :=
  if index<oldSize then values index else 0

def gkrEnvelopeGate (oldSize newSize : Nat) (gate : GKRWiringGate) : GKRWiringGate :=
  ⟨gate.op,gkrEnvelopeIndex oldSize newSize gate.left,gkrEnvelopeIndex oldSize newSize gate.right⟩

/-- Every remapped operand remains inside the trusted larger envelope. -/
theorem gkr_envelope_index_bound (oldSize newSize index : Nat)
    (positive : 0<oldSize) (fits : oldSize≤newSize) (bound : index<oldSize) :
    gkrEnvelopeIndex oldSize newSize index<newSize := by
  unfold gkrEnvelopeIndex
  split <;> omega

/-- The zero slot may move or stay put. Every valid old operand retains its
value, for arbitrary private inputs and public constants. -/
theorem gkr_envelope_operand_value (oldSize newSize index : Nat) (values : Nat → K)
    (positive : 0<oldSize) (fits : oldSize≤newSize) (bound : index<oldSize)
    (zero : values (oldSize-1)=0) :
    gkrEnvelopeValues oldSize values (gkrEnvelopeIndex oldSize newSize index)=values index := by
  unfold gkrEnvelopeIndex gkrEnvelopeValues
  by_cases last : index=oldSize-1
  · simp only [last,ite_true]
    by_cases same : newSize=oldSize
    · simp [same,show oldSize-1<oldSize by omega]
    · simp [show ¬newSize-1<oldSize by omega,zero]
  · simp [last,bound]

def gkrFiniteLayer (values : Nat → K) (gates : List GKRWiringGate) : List K :=
  gates.map (fun gate => gkrGateValue gate.op (values gate.left) (values gate.right))

/-- Includes explicit zero and relay gates in the first arithmetic layer. -/
theorem gkr_envelope_first_layer (oldSize newSize : Nat) (values : Nat → K)
    (gates : List GKRWiringGate) (positive : 0<oldSize) (fits : oldSize≤newSize)
    (zero : values (oldSize-1)=0)
    (bounded : ∀ gate∈gates,gate.left<oldSize ∧ gate.right<oldSize) :
    gkrFiniteLayer (gkrEnvelopeValues oldSize values) (gates.map (gkrEnvelopeGate oldSize newSize))=
      gkrFiniteLayer values gates := by
  simp only [gkrFiniteLayer,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro gate member
  simp only [gkrEnvelopeGate]
  rw [gkr_envelope_operand_value oldSize newSize gate.left values positive fits (bounded gate member).1 zero,
    gkr_envelope_operand_value oldSize newSize gate.right values positive fits (bounded gate member).2 zero]

/-- Finite layer execution with the executable verifier's zero fallback. -/
def gkrFiniteCircuit (values : Nat → K) : List (List GKRWiringGate) → (Nat → K)
  | [] => values
  | gates::rest => gkrFiniteCircuit (fun i => (gkrFiniteLayer values gates).getD i 0) rest

/-- Relocating only first-layer input references preserves every output of
all subsequent layers. Later layers address gate outputs, not input slots. -/
theorem gkr_envelope_circuit (oldSize newSize : Nat) (values : Nat → K)
    (first : List GKRWiringGate) (rest : List (List GKRWiringGate))
    (positive : 0<oldSize) (fits : oldSize≤newSize) (zero : values (oldSize-1)=0)
    (bounded : ∀ gate∈first,gate.left<oldSize ∧ gate.right<oldSize) :
    gkrFiniteCircuit (gkrEnvelopeValues oldSize values)
      (first.map (gkrEnvelopeGate oldSize newSize)::rest)=gkrFiniteCircuit values (first::rest) := by
  simp only [gkrFiniteCircuit]
  rw [gkr_envelope_first_layer oldSize newSize values first positive fits zero bounded]

end NearCompression
