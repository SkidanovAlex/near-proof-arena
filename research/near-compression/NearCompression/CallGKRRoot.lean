import NearCompression.CallCircuitCheck
import NearCompression.GKRRootOutput
import NearCompression.GKREvaluatedStrategy
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K] [DecidableEq K]

/-- A checked call compiler and a nonzero batched residual establish the
actual initial GKR mismatch. The initial root query and zero claim are explicit
verifier interfaces, rather than an assumed abstract wrong-claim predicate. -/
theorem call_checked_gkr_root_wrong
    (nodes : List (TerminalDAGNode K)) (capacity : Nat)
    (equations : List (K × CallBatchEquation K)) (v constants : Nat→K)
    (root : Nat) (cert : CallCircuitCertificate K)
    (live positions : List Nat) (zeroSlot : Nat) (stages : List TerminalStoredPlan) (outputSlot : Nat)
    (bounds : ∀ e∈callCompiledEntries equations,e.1<capacity)
    (checked : callCircuitCheck nodes capacity
      (fun i=>(callArrayRun equations (Array.replicate capacity 0,0)).1.getD i 0)
      (callArrayRun equations (Array.replicate capacity 0,0)).2 root cert=true)
    (layered : terminalStoredBundleCheck nodes capacity constants live positions zeroSlot stages root outputSlot=true)
    (nonempty : 0<stages.length)
    (outputBound : outputSlot<((stages.map (fun s=>s.gates)).getD (stages.length-1) []).length)
    (nonzero : (equations.map (fun pair=>pair.1*pair.2.residual v)).sum≠0)
    (raw : (m : Nat)→List (GKRBlock K)→GKRLayerStrategy K m)
    (m n : Nat) (bits : Nat→Bool)
    (slot : genericRowBitIndex n bits=outputSlot)
    (queries : (raw m []).gates=gkrWeightedLayer n
      (gkrReverseCircuitWiring (stages.map (fun s=>s.gates)) 0) [(genericRowBooleanPoint bits,1)])
    (claim : (raw m []).claimLeft []=0) :
    (gkrBindCircuitValues raw (terminalInitialValues capacity v constants)
      (stages.map (fun s=>s.gates)) m []).wrong := by
  let inputs:=terminalInitialValues capacity v constants
  let layers:=stages.map (fun s=>s.gates)
  have output:=call_layered_checked_residual_sum nodes capacity equations v constants root cert
    live positions zeroSlot stages outputSlot bounds checked layered
  have step:=gkr_reverse_circuit_step inputs layers 0 (by simpa [layers] using nonempty)
    outputSlot (by simpa [layers] using outputBound)
  rw [gkr_reverse_circuit_output] at step
  apply gkr_root_output_wrong (gkrBindCircuitValues raw inputs layers m []) n
    (gkrReverseCircuitWiring layers 0) bits queries
  change (raw m []).claimLeft []≠
    gkrLayerValues (gkrReverseCircuitValues inputs layers 1) (gkrReverseCircuitWiring layers 0)
      (genericRowBitIndex n bits)
  rw [claim,slot,←step]
  change 0≠gkrFiniteCircuit (terminalInitialValues capacity v constants) (stages.map (fun s=>s.gates)) outputSlot
  rw [output]
  exact Ne.symm nonzero

omit [DecidableEq K] in
/-- Once the preceding theorem supplies the initial mismatch, acceptance is
bounded by GKR cancellation plus accepted wrong terminal openings on the SAME
experiment. The latter term remains explicit for PCS composition. -/
theorem call_gkr_terminal_budget {R : Type}
    (sample : List K) (distinct : sample.Nodup)
    (raw : (m : Nat)→List (GKRBlock K)→GKRLayerStrategy K m)
    (capacity : Nat) (v constants : Nat→K) (stages : List TerminalStoredPlan)
    (m : Nat) (rest : List Nat) (continuations : List R)
    (accepted : List (GKRBlock K)→R→Prop)
    (checks : ∀ blocks r,accepted blocks r →
      gkrEvaluatedVerifierPath raw (stages.map (fun s=>s.gates)) [] (m::rest) blocks)
    (wrong : (gkrBindCircuitValues raw (terminalInitialValues capacity v constants)
      (stages.map (fun s=>s.gates)) m []).wrong) :
    let inputs:=terminalInitialValues capacity v constants
    let layers:=stages.map (fun s=>s.gates)
    let experiment:=(gkrChallengePaths sample (m::rest)).flatMap
      (fun blocks=>continuations.map (fun r=>(blocks,r)))
    count experiment (fun pair=>accepted pair.1 pair.2)*sample.length≤
      ((m::rest).map (fun k=>4*k+1)).sum*(gkrChallengePaths sample (m::rest)).length*continuations.length+
      count experiment (fun pair=>accepted pair.1 pair.2 ∧
        gkrTerminalMismatch (gkrBindCircuitValues raw inputs layers) (gkrReverseCircuitValues inputs layers)
          1 [] (m::rest) pair.1)*sample.length := by
  apply gkr_evaluated_continuation_budget sample distinct raw
    (terminalInitialValues capacity v constants) (stages.map (fun s=>s.gates)) (m::rest) []
    continuations accepted checks
  intro k ks equal
  cases equal
  exact wrong
end NearCompression
