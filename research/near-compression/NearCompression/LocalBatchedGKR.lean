import NearCompression.SemanticCircuitBinding
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

/-- Full local-prefix/rho/GKR experiment. The only residual error is accepted
GKR terminal mismatch, summed jointly over local prefixes and rho. Neither a
per-rowpoint PCS estimate nor a uniform conditional terminal budget is used. -/
theorem decoded_local_batched_gkr_split {K R : Type} [Field K]
    (sample : List K) (distinct : sample.Nodup)
    (rowLog : Nat) (decoded : Nat → Nat → K) (publicValues : List K)
    (residuals : List (AIRBusResidual K × Nat)) (d : Nat)
    (sent : K → List K → List K → Poly K) (localClaim : K → List K → List K → K)
    (outputs : LocalChallengePrefix K → List (K × K)) (tableCount : Nat)
    (outputLength : ∀ p∈decodedLocalPrefixes sample rowLog,(outputs p).length=tableCount)
    (wrongOutputs : ∀ p∈decodedLocalPrefixes sample rowLog,
      ¬decodedLocalTerminalCorrect rowLog decoded publicValues residuals localClaim p →
      0<(outputs p).length ∧ ∃ lane,((outputs p).map Prod.fst).getD lane 0≠((outputs p).map Prod.snd).getD lane 0)
    (continuations : List R)
    (raw : LocalChallengePrefix K → K → (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (inputs : LocalChallengePrefix K → K → Nat → K)
    (layers : LocalChallengePrefix K → K → List (List GKRWiringGate))
    (m : Nat) (rest : List Nat) (n : Nat) (bits : Nat → Bool)
    (binding : ∀ p∈decodedLocalPrefixes sample rowLog,∀ rho∈sample,
      gkrFiniteCircuit (inputs p rho) (layers p rho) (genericRowBitIndex n bits)=terminalResidualValue rho 1 (outputs p))
    (nonempty : ∀ p∈decodedLocalPrefixes sample rowLog,∀ rho∈sample,0<(layers p rho).length)
    (rootBound : ∀ p∈decodedLocalPrefixes sample rowLog,∀ rho∈sample,
      genericRowBitIndex n bits<((layers p rho).getD ((layers p rho).length-1) []).length)
    (queries : ∀ p∈decodedLocalPrefixes sample rowLog,∀ rho∈sample,
      (raw p rho m []).gates=gkrWeightedLayer n (gkrReverseCircuitWiring (layers p rho) 0) [(genericRowBooleanPoint bits,1)])
    (claim : ∀ p∈decodedLocalPrefixes sample rowLog,∀ rho∈sample,(raw p rho m []).claimLeft []=0)
    (accept : LocalChallengePrefix K → K → List (GKRBlock K) → R → Prop)
    (localChecks : ∀ p∈decodedLocalPrefixes sample rowLog,∀ rho∈sample,∀ blocks r,
      accept p rho blocks r → decodedLocalChecks d sent localClaim p)
    (gkrChecks : ∀ p∈decodedLocalPrefixes sample rowLog,∀ rho∈sample,∀ blocks r,
      accept p rho blocks r → gkrEvaluatedVerifierPath (raw p rho) (layers p rho) [] (m::rest) blocks) :
    let experiment := evaluatedGKRExperiment sample (m::rest) continuations
    let downstream := sample.flatMap (fun rho => experiment.map (fun pair => (rho,pair)))
    let accepted := fun p => count downstream (fun x => accept p x.1 x.2.1 x.2.2)
    let errors := fun p => (sample.map (fun rho => count experiment (fun pair => accept p rho pair.1 pair.2 ∧
      gkrTerminalMismatch (gkrBindCircuitValues (raw p rho) (inputs p rho) (layers p rho))
        (gkrReverseCircuitValues (inputs p rho) (layers p rho)) 1 [] (m::rest) pair.1))).sum
    ( (decodedLocalPrefixes sample rowLog).map accepted).sum*sample.length≤
      decodedLocalAcceptedCount sample rowLog decoded publicValues residuals d sent localClaim*downstream.length*sample.length+
      (decodedLocalPrefixes sample rowLog).length*
        ((tableCount-1)*experiment.length*sample.length+
          sample.length*(((m::rest).map (fun k => 4*k+1)).sum*
            (gkrChallengePaths sample (m::rest)).length*continuations.length))+
      ((decodedLocalPrefixes sample rowLog).map errors).sum*sample.length := by
  classical
  intro experiment downstream accepted errors
  apply decoded_local_continuation_split sample rowLog decoded publicValues residuals d sent localClaim
    downstream (fun p x => accept p x.1 x.2.1 x.2.2) ?_ _ errors ?_
  · intro p hp x hx ha
    obtain ⟨rho,hr,hpair⟩ := List.mem_flatMap.mp hx
    obtain ⟨value,hvalue,same⟩ := List.mem_map.mp hpair
    cases same
    exact localChecks p hp rho hr _ _ ha
  · intro p hp wrong
    obtain ⟨positive,lane,mismatch⟩ := wrongOutputs p hp wrong
    have bound := batched_evaluated_gkr_averaged_errors (outputs p) lane positive mismatch sample distinct continuations
      (raw p) (inputs p) (layers p) m rest n bits (binding p hp) (nonempty p hp)
      (rootBound p hp) (queries p hp) (claim p hp) (accept p) (gkrChecks p hp)
    dsimp only at bound
    rw [outputLength p hp] at bound
    simpa only [downstream,experiment,errors,count,List.countP_flatMap,List.countP_map,Function.comp_def] using bound

/-- The residual sum is exactly one chronological accepted-error count,
including duplicate sample values with their multiplicities. -/
theorem local_gkr_joint_error_count {K R : Type} [Field K]
    (sample : List K) (rowLog : Nat) (rounds : List Nat) (continuations : List R)
    (bad : LocalChallengePrefix K → K → List (GKRBlock K) → R → Prop) :
    ((decodedLocalPrefixes sample rowLog).map (fun p =>
      (sample.map (fun rho => count (evaluatedGKRExperiment sample rounds continuations)
        (fun pair => bad p rho pair.1 pair.2))).sum)).sum=
    count ((decodedLocalPrefixes sample rowLog).flatMap (fun p => sample.flatMap (fun rho =>
      (evaluatedGKRExperiment sample rounds continuations).map (fun pair => (p,rho,pair)))))
      (fun x => bad x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  classical
  simp only [count,List.countP_flatMap,List.countP_map,Function.comp_def]

end NearCompression
