import NearCompression.SecondTableEvaluatedGKRPCS
namespace NearCompression
open Lean.Grind ZkFormal.Near ZkFormal.Udr ZkFormal.V2 ZkFormal.Air ZkFormal.Algebra ArenaCore.Security

/-- The first-table acceptance bound with actual evaluated-GKR repair,
including all later second-table local prefixes. Source and semantic binding
and the concrete joint PCS event bound remain explicit. -/
theorem first_table_evaluated_gkr_pcs_budget
    (sample : List Fp8) (distinct : sample.Nodup) (layout : GKRJointLayout)
    (secondRows : Nat) (earlierRounds : List Nat) (queries : Nat)
    (table : Table) (sourceTrace : Trace Fp) (sourceWidth : Nat → Nat) (t n : Nat)
    (rowShape : layout.rowCoordinates=(n+1)+secondRows)
    (log : sourceTrace.log t=n+1) (upper : sourceTrace.log t≤table.maxLog)
    (pub : List Fp) (invalid : ¬TableLocal table sourceTrace t pub)
    (bounds : ∀ e∈tableSourceResiduals table,e.colBound≤sourceWidth t)
    (trace : Trace Fp8) (logs : trace.log=sourceTrace.log)
    (fixed : ∀ s row column,column<sourceWidth s → trace.cell s row column=Fp8.ofBase (sourceTrace.cell s row column))
    (auxiliary : List (BusProgramFormula Fp8)) (residuals : List (AIRBusResidual Fp8 × Nat))
    (order : residuals.map Prod.fst=(tableSourceResiduals table).map Sum.inl++auxiliary.map Sum.inr)
    (d : Nat) (sourceDegrees : ∀ e∈tableSourceResiduals table,e.degree≤d)
    (auxDegrees : ∀ e∈auxiliary,busFormulaDegree e≤d)
    (sent : Fp8 → List Fp8 → List Fp8 → Poly Fp8) (claim : Fp8 → List Fp8 → List Fp8 → Fp8)
    (initialZero : ∀ mixing tau,claim mixing tau []=0)
    (accept : LocalChallengePrefix Fp8 → LocalChallengePrefix Fp8 →
      (Fp8 × (List (GKRBlock Fp8) × (List Fp8 × (List Fp8 × List Nat)))) → Prop)
    (checks : ∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈decodedLocalPrefixes sample secondRows,
      ∀ r∈twoTablePCSContinuations sample layout earlierRounds queries,
      accept p q r → decodedLocalChecks d sent claim p)
    (budget : Nat)
    (event : LocalChallengePrefix Fp8 → LocalChallengePrefix Fp8 → Fp8 →
      List (GKRBlock Fp8) → List Fp8 → List Fp8 → List Nat → Prop)
    (m : Nat) (rest : List Nat) (rounds : earlierRounds++[layout.inputLog]=m::rest)
    (outputs : LocalChallengePrefix Fp8 → LocalChallengePrefix Fp8 → List (Fp8 × Fp8))
    (tableCount : Nat)
    (length : ∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈decodedLocalPrefixes sample secondRows,
      (outputs p q).length=tableCount)
    (mismatch : ∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈decodedLocalPrefixes sample secondRows,
      ¬decodedLocalTerminalCorrect (n+1) (fun column row=>trace.cell t row column)
        (pub.map Fp8.ofBase) residuals claim p →
      0<(outputs p q).length ∧ ∃ lane,
        ((outputs p q).map Prod.fst).getD lane 0≠((outputs p q).map Prod.snd).getD lane 0)
    (raw : LocalChallengePrefix Fp8 → LocalChallengePrefix Fp8 → Fp8 →
      (k : Nat) → List (GKRBlock Fp8) → GKRLayerStrategy Fp8 k)
    (inputs : LocalChallengePrefix Fp8 → LocalChallengePrefix Fp8 → Fp8 → Nat → Fp8)
    (layers : LocalChallengePrefix Fp8 → LocalChallengePrefix Fp8 → Fp8 → List (List GKRWiringGate))
    (rootLog : Nat) (bits : Nat → Bool)
    (binding : ∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈decodedLocalPrefixes sample secondRows,∀ rho∈sample,
      gkrFiniteCircuit (inputs p q rho) (layers p q rho) (genericRowBitIndex rootLog bits)=terminalResidualValue rho 1 (outputs p q))
    (nonempty : ∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈decodedLocalPrefixes sample secondRows,∀ rho∈sample,0<(layers p q rho).length)
    (rootBound : ∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈decodedLocalPrefixes sample secondRows,∀ rho∈sample,
      genericRowBitIndex rootLog bits<((layers p q rho).getD ((layers p q rho).length-1) []).length)
    (gates : ∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈decodedLocalPrefixes sample secondRows,∀ rho∈sample,
      (raw p q rho m []).gates=gkrWeightedLayer rootLog (gkrReverseCircuitWiring (layers p q rho) 0) [(genericRowBooleanPoint bits,1)])
    (rootClaim : ∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈decodedLocalPrefixes sample secondRows,∀ rho∈sample,
      (raw p q rho m []).claimLeft []=0)
    (gkrChecks : ∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈decodedLocalPrefixes sample secondRows,∀ rho∈sample,
      ∀ blocks z path qs,accept p q (rho,blocks,z,path,qs) →
        gkrEvaluatedVerifierPath (raw p q rho) (layers p q rho) [] (m::rest) blocks)
    (errorInclusion : ∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈decodedLocalPrefixes sample secondRows,∀ rho∈sample,
      ∀ item∈evaluatedGKRExperiment sample (m::rest) (gkrPCSContinuationSamples sample layout queries),
      accept p q (rho,item) →
      gkrTerminalMismatch (gkrBindCircuitValues (raw p q rho) (inputs p q rho) (layers p q rho))
        (gkrReverseCircuitValues (inputs p q rho) (layers p q rho)) 1 [] (m::rest) item.1 →
      event p q rho item.1 item.2.1 item.2.2.1 item.2.2.2)
    (joint : ∀ first∈airLocalInitialChallenges sample (n+1),
      ∀ second∈airLocalInitialChallenges sample secondRows,∀ rho∈sample,
      ∀ earlier∈gkrChallengePaths sample earlierRounds,
      count (gkrConcretePCSSamples sample layout queries) (fun item=>
        event (first,item.1.take (n+1)) (second,item.1.drop (n+1)) rho
          (earlier++[item.2.1]) item.2.2.1 item.2.2.2.1 item.2.2.2.2)*sample.length≤budget) :
    count ((decodedLocalPrefixes sample (n+1)).flatMap (fun p=>
      (decodedLocalPrefixes sample secondRows).flatMap (fun q=>
        (twoTablePCSContinuations sample layout earlierRounds queries).map (fun r=>(p,q,r)))))
      (fun x=>accept x.1 x.2.1 x.2.2)*sample.length ≤
      (((tableSourceResiduals table).length+auxiliary.length-1+(n+1)+(d+1)*(n+1))*
        sample.length^(2*(n+1)+1))*(firstTablePCSContinuations sample secondRows layout earlierRounds queries).length+
      (decodedLocalPrefixes sample (n+1)).length*((decodedLocalPrefixes sample secondRows).length*((tableCount-1)*
        (evaluatedGKRExperiment sample (m::rest) (gkrPCSContinuationSamples sample layout queries)).length*sample.length+
        sample.length*(((m::rest).map (fun k=>4*k+1)).sum*(gkrChallengePaths sample (m::rest)).length*
          (gkrPCSContinuationSamples sample layout queries).length)))+
      (airLocalInitialChallenges sample (n+1)).length*((airLocalInitialChallenges sample secondRows).length*
        (sample.length*((gkrChallengePaths sample earlierRounds).length*budget))) := by
  apply first_table_fixed_source_pcs_budget sample distinct layout secondRows earlierRounds queries
    table sourceTrace sourceWidth t n rowShape log upper pub invalid bounds trace logs fixed
    auxiliary residuals order d sourceDegrees auxDegrees sent claim initialZero accept checks _ budget event ?_ joint
  intro p hp wrong
  have h := two_table_terminal_repair sample distinct (decodedLocalPrefixes sample secondRows)
    layout earlierRounds queries m rest rounds (outputs p) tableCount (length p hp)
    (fun q hq=>mismatch p hp q hq wrong) (raw p) (inputs p) (layers p) rootLog bits
    (binding p hp) (nonempty p hp) (rootBound p hp) (gates p hp) (rootClaim p hp)
    (fun q rho blocks z path qs=>accept p q (rho,blocks,z,path,qs)) (event p)
    (gkrChecks p hp) (errorInclusion p hp)
  dsimp only at h
  simpa only [firstTablePCSContinuations] using h

end NearCompression
