import NearCompression.TerminalBatchFailure
import NearCompression.GKREvaluatedStrategy
import NearCompression.GKRRootOutput
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

/-- Derive the first GKR wrong-claim predicate from a nonzero finite output,
with actual computed layer values and a Boolean query selecting the root. -/
theorem evaluated_gkr_zero_root_wrong {K : Type} [Field K]
    (raw : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (inputs : Nat → K) (layers : List (List GKRWiringGate)) (m n : Nat) (bits : Nat → Bool)
    (nonempty : 0<layers.length)
    (rootBound : genericRowBitIndex n bits<(layers.getD (layers.length-1) []).length)
    (queries : (raw m []).gates=gkrWeightedLayer n (gkrReverseCircuitWiring layers 0) [(genericRowBooleanPoint bits,1)])
    (claim : (raw m []).claimLeft []=0)
    (nonzero : gkrFiniteCircuit inputs layers (genericRowBitIndex n bits)≠0) :
    (gkrBindCircuitValues raw inputs layers m []).wrong := by
  apply gkr_root_output_wrong (gkrBindCircuitValues raw inputs layers m []) n (gkrReverseCircuitWiring layers 0) bits queries
  change (raw m []).claimLeft []≠gkrLayerValues (gkrReverseCircuitValues inputs layers 1)
    (gkrReverseCircuitWiring layers 0) (genericRowBitIndex n bits)
  rw [claim,←gkr_reverse_circuit_step inputs layers 0 nonempty _ rootBound,gkr_reverse_circuit_output]
  exact Ne.symm nonzero

/-- One exact continuation sample space for the fixed GKR round envelope. -/
def evaluatedGKRExperiment {K R : Type} (sample : List K) (rounds : List Nat) (continuations : List R) :
    List (List (GKRBlock K) × R) :=
  (gkrChallengePaths sample rounds).flatMap (fun blocks => continuations.map (fun r => (blocks,r)))

/-- Batch cancellation plus evaluated GKR repair, leaving only accepted
terminal input mismatch as a PCS budget. Circuits and strategies may depend
on rho, while semantic outputs and the round envelope precede rho. -/
theorem batched_evaluated_gkr_budget {K R : Type} [Field K]
    (outputs : List (K × K)) (lane : Nat) (positive : 0<outputs.length)
    (wrong : (outputs.map Prod.fst).getD lane 0≠(outputs.map Prod.snd).getD lane 0)
    (sample : List K) (distinct : sample.Nodup) (continuations : List R)
    (raw : K → (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (inputs : K → Nat → K) (layers : K → List (List GKRWiringGate))
    (m : Nat) (rest : List Nat) (n : Nat) (bits : Nat → Bool)
    (binding : ∀ rho∈sample,gkrFiniteCircuit (inputs rho) (layers rho) (genericRowBitIndex n bits)=terminalResidualValue rho 1 outputs)
    (nonempty : ∀ rho∈sample,0<(layers rho).length)
    (rootBound : ∀ rho∈sample,genericRowBitIndex n bits<((layers rho).getD ((layers rho).length-1) []).length)
    (queries : ∀ rho∈sample,(raw rho m []).gates=gkrWeightedLayer n (gkrReverseCircuitWiring (layers rho) 0) [(genericRowBooleanPoint bits,1)])
    (claim : ∀ rho∈sample,(raw rho m []).claimLeft []=0)
    (accept : K → List (GKRBlock K) → R → Prop)
    (checks : ∀ rho∈sample,∀ blocks r,accept rho blocks r → gkrEvaluatedVerifierPath (raw rho) (layers rho) [] (m::rest) blocks)
    (pcsBudget : Nat)
    (pcs : ∀ rho∈sample,
      count (evaluatedGKRExperiment sample (m::rest) continuations) (fun pair => accept rho pair.1 pair.2 ∧
        gkrTerminalMismatch (gkrBindCircuitValues (raw rho) (inputs rho) (layers rho))
          (gkrReverseCircuitValues (inputs rho) (layers rho)) 1 [] (m::rest) pair.1)≤pcsBudget) :
    (sample.map (fun rho => count (evaluatedGKRExperiment sample (m::rest) continuations)
      (fun pair => accept rho pair.1 pair.2))).sum*sample.length≤
      (outputs.length-1)*(evaluatedGKRExperiment sample (m::rest) continuations).length*sample.length+
      sample.length*(((m::rest).map (fun k => 4*k+1)).sum*
        (gkrChallengePaths sample (m::rest)).length*continuations.length+pcsBudget*sample.length) := by
  apply terminal_batch_continuation_budget outputs lane positive wrong sample distinct
    (evaluatedGKRExperiment sample (m::rest) continuations)
    (fun rho => gkrFiniteCircuit (inputs rho) (layers rho) (genericRowBitIndex n bits)) binding
    (fun rho pair => accept rho pair.1 pair.2) sample.length _
  intro rho member nz
  have first := evaluated_gkr_zero_root_wrong (raw rho) (inputs rho) (layers rho) m n bits
    (nonempty rho member) (rootBound rho member) (queries rho member) (claim rho member) nz
  have gkr := gkr_evaluated_continuation_budget sample distinct (raw rho) (inputs rho) (layers rho)
    (m::rest) [] continuations (accept rho) (checks rho member) (by
      intro k ks eq
      cases eq
      exact first)
  exact Nat.le_trans gkr (Nat.add_le_add_left (Nat.mul_le_mul_right sample.length (pcs rho member)) _)

end NearCompression
