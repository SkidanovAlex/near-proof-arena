import NearCompression.BatchedEvaluatedGKR
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

/-- Keep downstream error counts as a sum over initial choices. A uniform
per-choice PCS bound is not needed and must not be inferred from a joint one. -/
theorem conditional_scaled_accept_errors {A B : Type} (initial : List A) (paths : List B)
    (bad : A → Prop) (accept : A → B → Prop) (scale fixed : Nat) (errors : A → Nat)
    (good : ∀ a∈initial,¬bad a → count paths (accept a)*scale≤fixed+errors a*scale) :
    (initial.map (fun a => count paths (accept a))).sum*scale≤
      count initial bad*paths.length*scale+initial.length*fixed+(initial.map errors).sum*scale := by
  classical
  induction initial with
  | nil => simp [count]
  | cons a rest ih =>
    have tail := ih (fun b hb => good b (List.mem_cons_of_mem _ hb))
    have head := good a (List.mem_cons_self ..)
    have maximum : count paths (accept a)*scale≤paths.length*scale :=
      Nat.mul_le_mul_right scale List.countP_le_length
    simp only [List.map_cons,List.sum_cons,count,List.countP_cons,List.length_cons,Nat.add_mul] at tail head maximum ⊢
    by_cases h : bad a <;> simp_all <;> grind

/-- Batching cancellation plus downstream repair, retaining every rho's
terminal-error count instead of replacing it with a conditional PCS budget. -/
theorem terminal_batch_averaged_errors {K R : Type} [Field K]
    (outputs : List (K × K)) (lane : Nat) (positive : 0<outputs.length)
    (wrong : (outputs.map Prod.fst).getD lane 0≠(outputs.map Prod.snd).getD lane 0)
    (sample : List K) (distinct : sample.Nodup) (continuations : List R)
    (circuit : K → K) (binding : ∀ rho∈sample,circuit rho=terminalResidualValue rho 1 outputs)
    (accept : K → R → Prop) (scale repair : Nat) (errors : K → Nat)
    (nonzero : ∀ rho∈sample,circuit rho≠0 → count continuations (accept rho)*scale≤repair+errors rho*scale) :
    (sample.map (fun rho => count continuations (accept rho))).sum*scale≤
      (outputs.length-1)*continuations.length*scale+sample.length*repair+(sample.map errors).sum*scale := by
  have split := conditional_scaled_accept_errors sample continuations (fun rho => circuit rho=0)
    accept scale repair errors nonzero
  have cancellation := terminal_circuit_cancellation_count outputs lane positive wrong sample distinct circuit binding
  have scaled := Nat.mul_le_mul_right scale (Nat.mul_le_mul_right continuations.length cancellation)
  exact Nat.le_trans split (Nat.add_le_add_right (Nat.add_le_add_right scaled _) _)

/-- Summing a per-rowpoint GKR repair inequality preserves the total terminal
error term. The joint PCS bound can be applied only after this aggregation. -/
theorem sum_scaled_error_budget {A : Type} (rows : List A) (accepted errors : A → Nat)
    (scale repair : Nat) (each : ∀ row∈rows,accepted row*scale≤repair+errors row*scale) :
    (rows.map accepted).sum*scale≤rows.length*repair+(rows.map errors).sum*scale := by
  induction rows with
  | nil => simp
  | cons row rest ih =>
    have head := each row (by simp)
    have tail := ih (fun r hr => each r (by simp [hr]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul]
    omega

/-- The concrete evaluated GKR theorem supplies the repair term. Its exact
accepted terminal-mismatch count remains averaged over rho, ready to be
summed over rowpoints and rearranged into the joint PCS experiment. -/
theorem batched_evaluated_gkr_averaged_errors {K R : Type} [Field K]
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
    (checks : ∀ rho∈sample,∀ blocks r,accept rho blocks r → gkrEvaluatedVerifierPath (raw rho) (layers rho) [] (m::rest) blocks) :
    let experiment := evaluatedGKRExperiment sample (m::rest) continuations
    let errors := fun rho => count experiment (fun pair => accept rho pair.1 pair.2 ∧
      gkrTerminalMismatch (gkrBindCircuitValues (raw rho) (inputs rho) (layers rho))
        (gkrReverseCircuitValues (inputs rho) (layers rho)) 1 [] (m::rest) pair.1)
    (sample.map (fun rho => count experiment (fun pair => accept rho pair.1 pair.2))).sum*sample.length≤
      (outputs.length-1)*experiment.length*sample.length+
      sample.length*(((m::rest).map (fun k => 4*k+1)).sum*
        (gkrChallengePaths sample (m::rest)).length*continuations.length)+(sample.map errors).sum*sample.length := by
  intro experiment errors
  apply terminal_batch_averaged_errors outputs lane positive wrong sample distinct experiment
    (fun rho => gkrFiniteCircuit (inputs rho) (layers rho) (genericRowBitIndex n bits)) binding
    (fun rho pair => accept rho pair.1 pair.2) sample.length _ errors
  intro rho member nz
  have first := evaluated_gkr_zero_root_wrong (raw rho) (inputs rho) (layers rho) m n bits
    (nonempty rho member) (rootBound rho member) (queries rho member) (claim rho member) nz
  exact gkr_evaluated_continuation_budget sample distinct (raw rho) (inputs rho) (layers rho)
    (m::rest) [] continuations (accept rho) (checks rho member) (by
      intro k ks eq
      cases eq
      exact first)

end NearCompression
