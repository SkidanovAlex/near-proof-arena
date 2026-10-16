import NearCompression.FirstTableFixedSourcePCS
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

/-- Evaluated GKR supplies the terminal-repair bound across arbitrary later
local prefixes. Each prefix's semantic output vector is fixed before rho.
Accepted terminal mismatches are retained in one joint event count, which may
also include absent representatives. No per-rowpoint PCS bound is required. -/
theorem two_table_terminal_repair {Q : Type}
    (sample : List Fp8) (distinct : sample.Nodup) (future : List Q)
    (layout : GKRJointLayout) (earlierRounds : List Nat) (queryCount : Nat)
    (m : Nat) (rest : List Nat) (rounds : earlierRounds++[layout.inputLog]=m::rest)
    (outputs : Q → List (Fp8 × Fp8)) (tableCount : Nat)
    (length : ∀ q∈future,(outputs q).length=tableCount)
    (mismatch : ∀ q∈future,0<(outputs q).length ∧ ∃ lane,
      ((outputs q).map Prod.fst).getD lane 0≠((outputs q).map Prod.snd).getD lane 0)
    (raw : Q → Fp8 → (k : Nat) → List (GKRBlock Fp8) → GKRLayerStrategy Fp8 k)
    (inputs : Q → Fp8 → Nat → Fp8) (layers : Q → Fp8 → List (List GKRWiringGate))
    (n : Nat) (bits : Nat → Bool)
    (binding : ∀ q∈future,∀ rho∈sample,
      gkrFiniteCircuit (inputs q rho) (layers q rho) (genericRowBitIndex n bits)=terminalResidualValue rho 1 (outputs q))
    (nonempty : ∀ q∈future,∀ rho∈sample,0<(layers q rho).length)
    (rootBound : ∀ q∈future,∀ rho∈sample,
      genericRowBitIndex n bits<((layers q rho).getD ((layers q rho).length-1) []).length)
    (queries : ∀ q∈future,∀ rho∈sample,
      (raw q rho m []).gates=gkrWeightedLayer n (gkrReverseCircuitWiring (layers q rho) 0) [(genericRowBooleanPoint bits,1)])
    (claim : ∀ q∈future,∀ rho∈sample,(raw q rho m []).claimLeft []=0)
    (accept event : Q → Fp8 → List (GKRBlock Fp8) → List Fp8 → List Fp8 → List Nat → Prop)
    (checks : ∀ q∈future,∀ rho∈sample,∀ blocks z path qs,
      accept q rho blocks z path qs → gkrEvaluatedVerifierPath (raw q rho) (layers q rho) [] (m::rest) blocks)
    (errorInclusion : ∀ q∈future,∀ rho∈sample,
      ∀ item∈evaluatedGKRExperiment sample (m::rest) (gkrPCSContinuationSamples sample layout queryCount),
      accept q rho item.1 item.2.1 item.2.2.1 item.2.2.2 →
      gkrTerminalMismatch (gkrBindCircuitValues (raw q rho) (inputs q rho) (layers q rho))
        (gkrReverseCircuitValues (inputs q rho) (layers q rho)) 1 [] (m::rest) item.1 →
      event q rho item.1 item.2.1 item.2.2.1 item.2.2.2) :
    let downstream := twoTablePCSContinuations sample layout earlierRounds queryCount
    let experiment := future.flatMap (fun q=>downstream.map (fun r=>(q,r)))
    count experiment (fun x=>accept x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)*sample.length ≤
      future.length*((tableCount-1)*
        (evaluatedGKRExperiment sample (m::rest) (gkrPCSContinuationSamples sample layout queryCount)).length*sample.length+
        sample.length*(((m::rest).map (fun k=>4*k+1)).sum*
          (gkrChallengePaths sample (m::rest)).length*(gkrPCSContinuationSamples sample layout queryCount).length))+
      count experiment (fun x=>event x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)*sample.length := by
  classical
  intro downstream experiment
  let accepted := fun q=>count downstream (fun r=>accept q r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2)
  let errors := fun q=>count downstream (fun r=>event q r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2)
  have each : ∀ q∈future,accepted q*sample.length ≤
      ((tableCount-1)*(evaluatedGKRExperiment sample (m::rest) (gkrPCSContinuationSamples sample layout queryCount)).length*sample.length+
        sample.length*(((m::rest).map (fun k=>4*k+1)).sum*
          (gkrChallengePaths sample (m::rest)).length*(gkrPCSContinuationSamples sample layout queryCount).length))+
      errors q*sample.length := by
    intro q hq
    obtain ⟨positive,lane,wrong⟩ := mismatch q hq
    have bound := batched_evaluated_gkr_averaged_errors (outputs q) lane positive wrong sample distinct
      (gkrPCSContinuationSamples sample layout queryCount) (raw q) (inputs q) (layers q)
      m rest n bits (binding q hq) (nonempty q hq) (rootBound q hq) (queries q hq) (claim q hq)
      (fun rho blocks item=>accept q rho blocks item.1 item.2.1 item.2.2)
      (fun rho hr blocks item ha=>checks q hq rho hr blocks item.1 item.2.1 item.2.2 ha)
    dsimp only at bound
    rw [length q hq] at bound
    have inclusion : count downstream (fun r=>accept q r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2 ∧
      gkrTerminalMismatch (gkrBindCircuitValues (raw q r.1) (inputs q r.1) (layers q r.1))
        (gkrReverseCircuitValues (inputs q r.1) (layers q r.1)) 1 [] (m::rest) r.2.1)≤errors q := by
      apply count_mono_mem
      intro r hr h
      simp only [downstream,twoTablePCSContinuations,rounds,List.mem_flatMap,List.mem_map] at hr
      obtain ⟨rho,hrho,item,hi,rfl⟩ := hr
      exact errorInclusion q hq rho hrho item hi h.1 h.2
    have lifted := Nat.add_le_add_left (Nat.mul_le_mul_right sample.length inclusion)
      ((tableCount-1)*(evaluatedGKRExperiment sample (m::rest) (gkrPCSContinuationSamples sample layout queryCount)).length*sample.length+
        sample.length*(((m::rest).map (fun k=>4*k+1)).sum*
          (gkrChallengePaths sample (m::rest)).length*(gkrPCSContinuationSamples sample layout queryCount).length))
    apply Nat.le_trans ?_ lifted
    simpa only [accepted,downstream,twoTablePCSContinuations,rounds,count,List.countP_flatMap,List.countP_map,Function.comp_def] using bound
  have total := sum_scaled_error_budget future accepted errors sample.length _ each
  simpa only [accepted,errors,experiment,count,List.countP_flatMap,List.countP_map,Function.comp_def] using total

end NearCompression
