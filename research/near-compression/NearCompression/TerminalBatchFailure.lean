import NearCompression.DecodedLocalSoundness
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

/-- Exact compiler batching polynomial, including zero rho and arbitrary
starting power. Outputs and claims must be fixed before rho is sampled. -/
theorem terminal_residual_power_batch {K : Type} [Field K]
    (rho power : K) (outputs : List (K × K)) :
    terminalResidualValue rho power outputs=
      power*(lanePowerBatch rho (outputs.map Prod.fst)-lanePowerBatch rho (outputs.map Prod.snd)) := by
  induction outputs generalizing power with
  | nil => simp only [terminalResidualValue,List.map_nil,lanePowerBatch];grind
  | cons pair rest ih =>
    rcases pair with ⟨output,claim⟩
    simp only [terminalResidualValue,List.map_cons,lanePowerBatch,ih]
    grind

/-- A fixed wrong table claim can cancel in the batched terminal circuit at
at most tableCount-1 distinct rho values. -/
theorem terminal_residual_cancellation_count {K : Type} [Field K]
    (outputs : List (K × K)) (lane : Nat) (positive : 0<outputs.length)
    (wrong : (outputs.map Prod.fst).getD lane 0≠(outputs.map Prod.snd).getD lane 0)
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun rho => terminalResidualValue rho 1 outputs=0)≤outputs.length-1 := by
  have bound := lane_claim_batch_bad_count_le (outputs.map Prod.fst) (outputs.map Prod.snd)
    outputs.length lane positive (by simp) (by simp) wrong sample distinct
  apply Nat.le_trans (count_mono _ (fun rho zero => ?_)) bound
  rw [terminal_residual_power_batch] at zero
  grind

/-- Finite circuit identities can be substituted without requiring circuits
at different rho values to share a DAG. Their output/claim list stays fixed. -/
theorem terminal_circuit_cancellation_count {K : Type} [Field K]
    (outputs : List (K × K)) (lane : Nat) (positive : 0<outputs.length)
    (wrong : (outputs.map Prod.fst).getD lane 0≠(outputs.map Prod.snd).getD lane 0)
    (sample : List K) (distinct : sample.Nodup) (circuit : K → K)
    (binding : ∀ rho∈sample,circuit rho=terminalResidualValue rho 1 outputs) :
    count sample (fun rho => circuit rho=0)≤outputs.length-1 := by
  apply Nat.le_trans (count_mono_mem _ (fun rho member zero => ?_))
    (terminal_residual_cancellation_count outputs lane positive wrong sample distinct)
  rwa [←binding rho member]

/-- Compose batching cancellation with a conditional downstream GKR/PCS
budget. Downstream strategies may depend on rho; no independence between
acceptance and terminal failure is assumed. The supplied budget still needs
to be instantiated by the actual circuit verifier experiment. -/
theorem terminal_batch_continuation_budget {K R : Type} [Field K]
    (outputs : List (K × K)) (lane : Nat) (positive : 0<outputs.length)
    (wrong : (outputs.map Prod.fst).getD lane 0≠(outputs.map Prod.snd).getD lane 0)
    (sample : List K) (distinct : sample.Nodup) (continuations : List R)
    (circuit : K → K) (binding : ∀ rho∈sample,circuit rho=terminalResidualValue rho 1 outputs)
    (accept : K → R → Prop) (scale budget : Nat)
    (nonzero : ∀ rho∈sample,circuit rho≠0 → count continuations (accept rho)*scale≤budget) :
    (sample.map (fun rho => count continuations (accept rho))).sum*scale≤
      (outputs.length-1)*continuations.length*scale+sample.length*budget := by
  have split := conditional_scaled_accept_count sample continuations (fun rho => circuit rho=0)
    accept scale budget nonzero
  have cancellation := terminal_circuit_cancellation_count outputs lane positive wrong sample distinct circuit binding
  have scaled := Nat.mul_le_mul_right scale (Nat.mul_le_mul_right continuations.length cancellation)
  exact Nat.le_trans split (Nat.add_le_add_right scaled _)

/-- Wrong claims may cancel: a nonzero local mismatch alone does not imply a
nonzero batched output. The rho challenge is essential. -/
theorem terminal_batch_cancellation_regressions :
    terminalResidualValue (1:Rat) 1 [(1,0),(-1,0)]=0 ∧
    terminalResidualValue (0:Rat) 1 [(1,0),(-1,0)]=1 ∧
    terminalResidualValue (2:Rat) 1 [(1,0),(-1,0)]=(-1) ∧
    terminalResidualValue (0:Rat) 1 [(0,0),(1,0)]=0 := by decide +kernel

end NearCompression
