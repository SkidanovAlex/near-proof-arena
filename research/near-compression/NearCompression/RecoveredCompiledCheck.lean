import NearCompression.TerminalCompiledCheck
import NearCompression.GKRRecoveredCircuit
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

/-- Separation is a support condition; duplicate values within either region
are not silently ruled out or turned into ownership claims. -/
theorem gkr_scatter_split_initial {K : Type} [Field K]
    (capacity : Nat) (privateSlots constants : List (Nat × K))
    (privateBound : ∀ e∈privateSlots,e.1<capacity)
    (constantBound : ∀ e∈constants,capacity≤e.1) :
    (fun i => gkrScatter privateSlots i+gkrScatter constants i)=
      terminalInitialValues capacity (gkrScatter privateSlots) (gkrScatter constants) := by
  funext i
  unfold terminalInitialValues
  by_cases inside : i<capacity
  · have absent : i∉constants.map Prod.fst := by
      intro hi
      obtain ⟨e,he,eq⟩ := List.mem_map.mp hi
      have h := constantBound e he
      omega
    rw [ite_eq_left inside,gkr_scatter_unassigned constants i absent]
    grind
  · have absent : i∉privateSlots.map Prod.fst := by
      intro hi
      obtain ⟨e,he,eq⟩ := List.mem_map.mp hi
      have h := privateBound e he
      omega
    rw [ite_eq_right inside,gkr_scatter_unassigned privateSlots i absent]
    grind

/-- Metadata bounds cover both current and next halves, including masked
partial lanes. No power-of-two private capacity is required for separation. -/
theorem recovered_private_slots_capacity {K : Type} [Field K]
    (C capacity : Nat) (entries : List (GKRSourceLane × Poly K))
    (rowpoints : GKRSourceLane → Nat → K)
    (geometry : ∀ e∈entries,e.1.inputStart+e.1.width≤capacity ∧
      e.1.inputStart+e.1.nextOffset+e.1.width≤capacity) :
    ∀ slot∈recoveredPrivateSlots C entries rowpoints,slot.1<capacity := by
  intro slot hs
  obtain ⟨entry,he,hs⟩ := List.mem_flatMap.mp hs
  have bounds := geometry entry he
  simp only [lanePrivateSlots] at hs
  obtain ⟨col,hc,hs⟩ := List.mem_flatMap.mp hs
  split at hs
  · rename_i live
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl <;> simp only <;> omega
  · simp at hs

theorem recovered_circuit_input_initial {K : Type} [Field K]
    (C capacity : Nat) (entries : List (GKRSourceLane × Poly K))
    (rowpoints : GKRSourceLane → Nat → K) (constants : List (Nat × K))
    (geometry : ∀ e∈entries,e.1.inputStart+e.1.width≤capacity ∧
      e.1.inputStart+e.1.nextOffset+e.1.width≤capacity)
    (constantBound : ∀ e∈constants,capacity≤e.1) :
    gkrRecoveredCircuitInput C entries rowpoints constants=
      terminalInitialValues capacity (gkrScatter (recoveredPrivateSlots C entries rowpoints)) (gkrScatter constants) :=
  gkr_scatter_split_initial capacity _ constants
    (recovered_private_slots_capacity C capacity entries rowpoints geometry) constantBound

/-- The compiled output theorem now uses exactly the recovered assignment in
GKRRecoveredCircuit. No separate equality between private and full vectors is
assumed. Geometry and checked compiler data do not establish root extraction. -/
theorem recovered_compiled_finite_value {K : Type} [Field K] [DecidableEq K]
    (C capacity : Nat) (entries : List (GKRSourceLane × Poly K))
    (rowpoints : GKRSourceLane → Nat → K) (constants : List (Nat × K))
    (geometry : ∀ e∈entries,e.1.inputStart+e.1.width≤capacity ∧
      e.1.inputStart+e.1.nextOffset+e.1.width≤capacity)
    (constantBound : ∀ e∈constants,capacity≤e.1)
    (nodes : List (TerminalDAGNode K)) (rho : K) (tables : List (TerminalCompiledTable K))
    (balance : TerminalBalanceCertificate K) (root zeroNode : Nat)
    (live positions : List Nat) (zeroSlot : Nat) (stages : List TerminalStoredPlan) (outputSlot : Nat)
    (checked : terminalCompiledFiniteCheck nodes
      (gkrScatter (recoveredPrivateSlots C entries rowpoints)) (gkrScatter constants)
      rho tables balance root zeroNode capacity live positions zeroSlot stages outputSlot=true) :
    gkrFiniteCircuit (gkrRecoveredCircuitInput C entries rowpoints constants)
      (stages.map (fun s => s.gates)) outputSlot=
      terminalResidualValue rho 1 (terminalCompiledOutputs tables) := by
  rw [recovered_circuit_input_initial C capacity entries rowpoints constants geometry constantBound]
  exact terminal_compiled_finite_checked nodes _ _ rho tables balance root zeroNode capacity
    live positions zeroSlot stages outputSlot checked

/-- The same conclusion at depth zero of the existing reverse GKR layer
assignment, aligning the compiler result with the protocol's circuit values. -/
theorem recovered_compiled_reverse_output {K : Type} [Field K] [DecidableEq K]
    (C capacity : Nat) (entries : List (GKRSourceLane × Poly K))
    (rowpoints : GKRSourceLane → Nat → K) (constants : List (Nat × K))
    (geometry : ∀ e∈entries,e.1.inputStart+e.1.width≤capacity ∧
      e.1.inputStart+e.1.nextOffset+e.1.width≤capacity)
    (constantBound : ∀ e∈constants,capacity≤e.1)
    (nodes : List (TerminalDAGNode K)) (rho : K) (tables : List (TerminalCompiledTable K))
    (balance : TerminalBalanceCertificate K) (root zeroNode : Nat)
    (live positions : List Nat) (zeroSlot : Nat) (stages : List TerminalStoredPlan) (outputSlot : Nat)
    (checked : terminalCompiledFiniteCheck nodes
      (gkrScatter (recoveredPrivateSlots C entries rowpoints)) (gkrScatter constants)
      rho tables balance root zeroNode capacity live positions zeroSlot stages outputSlot=true) :
    gkrReverseCircuitValues (gkrRecoveredCircuitInput C entries rowpoints constants)
      (stages.map (fun s => s.gates)) 0 outputSlot=
      terminalResidualValue rho 1 (terminalCompiledOutputs tables) := by
  rw [gkr_reverse_circuit_output]
  exact recovered_compiled_finite_value C capacity entries rowpoints constants geometry constantBound
    nodes rho tables balance root zeroNode live positions zeroSlot stages outputSlot checked

/-- Duplicated private keys still add, absent private slots remain zero, and
both kinds of support overlap break the desired split. This does not claim
unique decoded ownership without its separate metadata theorem. -/
theorem recovered_scatter_split_regressions :
    gkrScatter [(0,(3:Rat)),(0,4)] 0+gkrScatter [(2,(5:Rat))] 0=7 ∧
    terminalInitialValues 2 (gkrScatter [(0,(3:Rat)),(0,4)]) (gkrScatter [(2,(5:Rat))]) 0=7 ∧
    terminalInitialValues 2 (gkrScatter [(0,(3:Rat))]) (gkrScatter [(2,(5:Rat))]) 1=0 ∧
    terminalInitialValues 2 (gkrScatter [(0,(3:Rat))]) (gkrScatter [(2,(5:Rat))]) 2=5 ∧
    gkrScatter [(0,(3:Rat))] 0+gkrScatter [(0,(1:Rat))] 0≠
      terminalInitialValues 2 (gkrScatter [(0,(3:Rat))]) (gkrScatter [(0,(1:Rat))]) 0 ∧
    gkrScatter [(2,(5:Rat))] 2+gkrScatter [(2,(7:Rat))] 2≠
      terminalInitialValues 2 (gkrScatter [(2,(5:Rat))]) (gkrScatter [(2,(7:Rat))]) 2 := by decide +kernel

end NearCompression
