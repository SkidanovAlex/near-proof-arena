import NearCompression.TwoTableTerminalRepair
namespace NearCompression
open Lean.Grind ZkFormal.Near ZkFormal.Udr ZkFormal.V2 ZkFormal.Air ZkFormal.Algebra ArenaCore.Security

/-- Second-table failed-source acceptance with actual batching/GKR repair
substituted. Only the concrete joint PCS bound remains numerical input;
semantic circuit binding and accepted verifier checks remain explicit. -/
theorem second_table_evaluated_gkr_pcs_budget
    (sample : List Fp8) (distinct : sample.Nodup) (layout : GKRJointLayout) (firstRows : Nat) (earlierRounds : List Nat) (queries : Nat)
    (table : Table) (sourceTrace : Trace Fp) (sourceWidth : Nat → Nat) (t n : Nat)
    (rowShape : layout.rowCoordinates=firstRows+(n+1))
    (log : sourceTrace.log t=n+1) (upper : sourceTrace.log t≤table.maxLog)
    (pub : List Fp) (invalid : ¬TableLocal table sourceTrace t pub)
    (bounds : ∀ e∈tableSourceResiduals table,e.colBound≤sourceWidth t)
    (traces : LocalChallengePrefix Fp8 → Trace Fp8)
    (logs : ∀ a∈decodedLocalPrefixes sample firstRows,(traces a).log=sourceTrace.log)
    (fixed : ∀ a∈decodedLocalPrefixes sample firstRows,∀ s row column,column<sourceWidth s →
      (traces a).cell s row column=Fp8.ofBase (sourceTrace.cell s row column)) (auxiliary : LocalChallengePrefix Fp8 → List (BusProgramFormula Fp8))
    (auxiliaryLength : Nat) (auxiliaryShape : ∀ a∈decodedLocalPrefixes sample firstRows,(auxiliary a).length=auxiliaryLength)
    (residuals : LocalChallengePrefix Fp8 → List (AIRBusResidual Fp8 × Nat))
    (order : ∀ a∈decodedLocalPrefixes sample firstRows,(residuals a).map Prod.fst=(tableSourceResiduals table).map Sum.inl++(auxiliary a).map Sum.inr)
    (d : Nat)
    (sourceDegrees : ∀ e∈tableSourceResiduals table,e.degree≤d) (auxDegrees : ∀ a∈decodedLocalPrefixes sample firstRows,∀ e∈auxiliary a,busFormulaDegree e≤d)
    (sent : LocalChallengePrefix Fp8 → Fp8 → List Fp8 → List Fp8 → Poly Fp8) (claim : LocalChallengePrefix Fp8 → Fp8 → List Fp8 → List Fp8 → Fp8)
    (initialZero : ∀ a∈decodedLocalPrefixes sample firstRows,∀ mixing tau,claim a mixing tau []=0)
    (accept : LocalChallengePrefix Fp8 → LocalChallengePrefix Fp8 → (Fp8 × (List (GKRBlock Fp8) × (List Fp8 × (List Fp8 × List Nat)))) → Prop)
    (checks : ∀ a∈decodedLocalPrefixes sample firstRows,∀ p∈decodedLocalPrefixes sample (n+1),∀ r∈(twoTablePCSContinuations sample layout earlierRounds queries),
      accept a p r → decodedLocalChecks d (sent a) (claim a) p)
    (budget : Nat)
    (event : LocalChallengePrefix Fp8 → LocalChallengePrefix Fp8 → Fp8 →
      List (GKRBlock Fp8) → List Fp8 → List Fp8 → List Nat → Prop)
    (m : Nat) (rest : List Nat) (rounds : earlierRounds++[layout.inputLog]=m::rest)
    (outputs : LocalChallengePrefix Fp8 → LocalChallengePrefix Fp8 → List (Fp8 × Fp8))
    (tableCount : Nat)
    (length : ∀ a∈decodedLocalPrefixes sample firstRows,∀ p∈decodedLocalPrefixes sample (n+1),
      (outputs a p).length=tableCount)
    (mismatch : ∀ a∈decodedLocalPrefixes sample firstRows,∀ p∈decodedLocalPrefixes sample (n+1),
      ¬decodedLocalTerminalCorrect (n+1) (fun column row=>(traces a).cell t row column)
        (pub.map Fp8.ofBase) (residuals a) (claim a) p →
      0<(outputs a p).length ∧ ∃ lane,
        ((outputs a p).map Prod.fst).getD lane 0≠((outputs a p).map Prod.snd).getD lane 0)
    (raw : LocalChallengePrefix Fp8 → LocalChallengePrefix Fp8 → Fp8 →
      (k : Nat) → List (GKRBlock Fp8) → GKRLayerStrategy Fp8 k)
    (inputs : LocalChallengePrefix Fp8 → LocalChallengePrefix Fp8 → Fp8 → Nat → Fp8)
    (layers : LocalChallengePrefix Fp8 → LocalChallengePrefix Fp8 → Fp8 → List (List GKRWiringGate))
    (rootLog : Nat) (bits : Nat → Bool)
    (binding : ∀ a∈decodedLocalPrefixes sample firstRows,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,
      gkrFiniteCircuit (inputs a p rho) (layers a p rho) (genericRowBitIndex rootLog bits)=terminalResidualValue rho 1 (outputs a p))
    (nonempty : ∀ a∈decodedLocalPrefixes sample firstRows,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,0<(layers a p rho).length)
    (rootBound : ∀ a∈decodedLocalPrefixes sample firstRows,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,
      genericRowBitIndex rootLog bits<((layers a p rho).getD ((layers a p rho).length-1) []).length)
    (gates : ∀ a∈decodedLocalPrefixes sample firstRows,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,
      (raw a p rho m []).gates=gkrWeightedLayer rootLog (gkrReverseCircuitWiring (layers a p rho) 0) [(genericRowBooleanPoint bits,1)])
    (rootClaim : ∀ a∈decodedLocalPrefixes sample firstRows,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,
      (raw a p rho m []).claimLeft []=0)
    (gkrChecks : ∀ a∈decodedLocalPrefixes sample firstRows,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,
      ∀ blocks z path qs,accept a p (rho,blocks,z,path,qs) →
        gkrEvaluatedVerifierPath (raw a p rho) (layers a p rho) [] (m::rest) blocks)
    (errorInclusion : ∀ a∈decodedLocalPrefixes sample firstRows,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,
      ∀ item∈evaluatedGKRExperiment sample (m::rest) (gkrPCSContinuationSamples sample layout queries),
      accept a p (rho,item) →
      gkrTerminalMismatch (gkrBindCircuitValues (raw a p rho) (inputs a p rho) (layers a p rho))
        (gkrReverseCircuitValues (inputs a p rho) (layers a p rho)) 1 [] (m::rest) item.1 →
      event a p rho item.1 item.2.1 item.2.2.1 item.2.2.2)
    (joint : ∀ first∈airLocalInitialChallenges sample firstRows,
      ∀ second∈airLocalInitialChallenges sample (n+1),∀ rho∈sample,
      ∀ earlier∈gkrChallengePaths sample earlierRounds,
      count (gkrConcretePCSSamples sample layout queries) (fun item =>
        event (first,item.1.take firstRows) (second,item.1.drop firstRows) rho
          (earlier++[item.2.1]) item.2.2.1 item.2.2.2.1 item.2.2.2.2)*sample.length≤budget) :
    count ((decodedLocalPrefixes sample firstRows).flatMap (fun a => (decodedLocalPrefixes sample (n+1)).flatMap (fun p =>
      (twoTablePCSContinuations sample layout earlierRounds queries).map (fun r => (a,p,r))))) (fun x => accept x.1 x.2.1 x.2.2)*sample.length≤
      (decodedLocalPrefixes sample firstRows).length*
        ((((tableSourceResiduals table).length+auxiliaryLength-1+(n+1)+(d+1)*(n+1))*sample.length^(2*(n+1)+1))*(twoTablePCSContinuations sample layout earlierRounds queries).length+
          (decodedLocalPrefixes sample (n+1)).length*((tableCount-1)*(evaluatedGKRExperiment sample (m::rest) (gkrPCSContinuationSamples sample layout queries)).length*sample.length+
            sample.length*(((m::rest).map (fun k=>4*k+1)).sum*(gkrChallengePaths sample (m::rest)).length*
              (gkrPCSContinuationSamples sample layout queries).length)))+((airLocalInitialChallenges sample firstRows).length*((airLocalInitialChallenges sample (n+1)).length*(sample.length*((gkrChallengePaths sample earlierRounds).length*budget)))) := by
  apply second_table_fixed_source_pcs_budget sample distinct layout firstRows earlierRounds queries
    table sourceTrace sourceWidth t n rowShape log upper pub invalid bounds traces logs fixed
    auxiliary auxiliaryLength auxiliaryShape residuals order d sourceDegrees auxDegrees sent claim initialZero
    accept checks _ budget event ?_ joint
  intro a ha p hp wrong
  have h := two_table_terminal_repair sample distinct [()] layout earlierRounds queries m rest rounds
    (fun _=>outputs a p) tableCount (fun _ _=>length a ha p hp)
    (fun _ _=>mismatch a ha p hp wrong) (fun _=>raw a p) (fun _=>inputs a p) (fun _=>layers a p)
    rootLog bits (fun _ _=>binding a ha p hp) (fun _ _=>nonempty a ha p hp)
    (fun _ _=>rootBound a ha p hp) (fun _ _=>gates a ha p hp) (fun _ _=>rootClaim a ha p hp)
    (fun _ rho blocks z path qs=>accept a p (rho,blocks,z,path,qs)) (fun _=>event a p)
    (fun _ _=>gkrChecks a ha p hp) (fun _ _=>errorInclusion a ha p hp)
  dsimp only at h
  simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_cons,List.length_nil,
    Nat.zero_add,Nat.one_mul,count_map] using h

end NearCompression
