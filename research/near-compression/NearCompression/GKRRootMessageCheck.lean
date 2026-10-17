import NearCompression.GKRPathMessageCheck
import NearCompression.CallGKRRoot
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K] [DecidableEq K]

/-- Bind the first sumcheck to the zero claim at the actual selected output.
The Boolean index is checked, so supplied bits cannot silently select another
gate. Output width and bounds are checked against the actual final layer. -/
def gkrRootMessageCheck
    (raw : (m : Nat)→List (GKRBlock K)→GKRLayerStrategy K m)
    (layers : List (List GKRWiringGate)) (m outputSlot : Nat) (bits : List Bool) : Bool :=
  decide (0<layers.length ∧
    (layers.getD (layers.length-1) []).length=2^bits.length ∧
    outputSlot<(layers.getD (layers.length-1) []).length ∧
    genericRowBitIndex bits.length (fun i=>bits.getD i false)=outputSlot ∧
    (raw m []).gates=gkrWeightedLayer bits.length (gkrReverseCircuitWiring layers 0)
      [(genericRowBooleanPoint (fun i=>bits.getD i false),1)] ∧
    (raw m []).claimLeft []=0)

theorem gkr_root_message_checked
    (raw : (m : Nat)→List (GKRBlock K)→GKRLayerStrategy K m)
    (layers : List (List GKRWiringGate)) (m outputSlot : Nat) (bits : List Bool)
    (checked : gkrRootMessageCheck raw layers m outputSlot bits=true) :
    0<layers.length ∧
    (layers.getD (layers.length-1) []).length=2^bits.length ∧
    outputSlot<(layers.getD (layers.length-1) []).length ∧
    genericRowBitIndex bits.length (fun i=>bits.getD i false)=outputSlot ∧
    (raw m []).gates=gkrWeightedLayer bits.length (gkrReverseCircuitWiring layers 0)
      [(genericRowBooleanPoint (fun i=>bits.getD i false),1)] ∧
    (raw m []).claimLeft []=0 := by
  exact _root_.of_decide_eq_true checked

/-- The executable root check now discharges all root-query, initial-claim
and output-slot assumptions of the checked call-to-GKR bridge. -/
theorem call_root_message_wrong
    (nodes : List (TerminalDAGNode K)) (capacity : Nat)
    (equations : List (K × CallBatchEquation K)) (v constants : Nat→K)
    (root : Nat) (cert : CallCircuitCertificate K)
    (live positions : List Nat) (zeroSlot : Nat) (stages : List TerminalStoredPlan) (outputSlot : Nat)
    (bounds : ∀ e∈callCompiledEntries equations,e.1<capacity)
    (checked : callCircuitCheck nodes capacity
      (fun i=>(callArrayRun equations (Array.replicate capacity 0,0)).1.getD i 0)
      (callArrayRun equations (Array.replicate capacity 0,0)).2 root cert=true)
    (layered : terminalStoredBundleCheck nodes capacity constants live positions zeroSlot stages root outputSlot=true)
    (nonzero : (equations.map (fun pair=>pair.1*pair.2.residual v)).sum≠0)
    (raw : (m : Nat)→List (GKRBlock K)→GKRLayerStrategy K m)
    (m : Nat) (bits : List Bool)
    (rootChecked : gkrRootMessageCheck raw (stages.map (fun s=>s.gates)) m outputSlot bits=true) :
    (gkrBindCircuitValues raw (terminalInitialValues capacity v constants)
      (stages.map (fun s=>s.gates)) m []).wrong := by
  have facts:=gkr_root_message_checked raw _ m outputSlot bits rootChecked
  exact call_checked_gkr_root_wrong nodes capacity equations v constants root cert
    live positions zeroSlot stages outputSlot bounds checked layered
    (by simpa using facts.1) (by simpa using facts.2.2.1) nonzero raw m bits.length
    (fun i=>bits.getD i false) facts.2.2.2.1 facts.2.2.2.2.1 facts.2.2.2.2.2
end NearCompression
