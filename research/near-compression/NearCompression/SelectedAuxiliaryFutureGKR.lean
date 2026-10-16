import NearCompression.SelectedAuxiliaryGKR
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra ArenaCore.Security

/-- Include later local protocols in the continuation of the selected table.
Their outputs and GKR strategy may vary with those future prefixes, while
this table's decoded trace and residual list remain earlier-history indexed.
The shared accepted failure count stays exact over the full experiment. -/
theorem selected_auxiliary_future_gkr_error_count {A Q : Type}
    (sample : List Fp8) (distinct : sample.Nodup) (earlier : List A) (future : List Q)
    (layout : GKRJointLayout) (earlierRounds : List Nat) (queries : Nat)
    (fixed : A → Trace Fp) (tr : A → Trace Fp8) (width : Nat → Nat)
    (start : Nat) (b : Bool) (publicValues : List Fp8)
    (formulas : A → Nat → List (BusProgramFormula Fp8))
    (selected : ∀ a∈earlier,twoTableAuxiliaryBranch (airExt8Trace (fixed a)) (formulas a) start=some b)
    (logs : ∀ a∈earlier,(tr a).log=(fixed a).log)
    (cells : ∀ a∈earlier,∀ t row column,column<width t →
      (tr a).cell t row column=Fp8.ofBase ((fixed a).cell t row column))
    (source : List Expr)
    (auxiliaryLength : Nat) (auxiliaryShape : ∀ a∈earlier,(formulas a (start+(if b then 1 else 0))).length=auxiliaryLength)
    (residuals : A → List (AIRBusResidual Fp8 × Nat))
    (order : ∀ a∈earlier,(residuals a).map Prod.fst=source.map Sum.inl++(formulas a (start+(if b then 1 else 0))).map Sum.inr)
    (d n : Nat) (positive : 0<source.length+auxiliaryLength)
    (rowLogs : ∀ a∈earlier,(tr a).log (start+(if b then 1 else 0))=n+1)
    (bounds : ∀ a∈earlier,∀ e∈formulas a (start+(if b then 1 else 0)),
      busFormulaColumnBound e≤width (start+(if b then 1 else 0)))
    (sourceDegrees : ∀ e∈source,e.degree≤d) (auxDegrees : ∀ a∈earlier,∀ e∈formulas a (start+(if b then 1 else 0)),busFormulaDegree e≤d)
    (sent : A → Fp8 → List Fp8 → List Fp8 → Poly Fp8) (claim : A → Fp8 → List Fp8 → List Fp8 → Fp8)
    (initialZero : ∀ a∈earlier,∀ mixing tau,claim a mixing tau []=0)
    (accept failure : A → LocalChallengePrefix Fp8 →
      (Q × (Fp8 × (List (GKRBlock Fp8) × (List Fp8 × (List Fp8 × List Nat))))) → Prop)
    (checks : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),
      ∀ r∈future.flatMap (fun q=>(twoTablePCSContinuations sample layout earlierRounds queries).map (fun r=>(q,r))),
      accept a p r → decodedLocalChecks d (sent a) (claim a) p)
    (m : Nat) (rest : List Nat) (rounds : earlierRounds++[layout.inputLog]=m::rest)
    (outputs : A → LocalChallengePrefix Fp8 → Q → List (Fp8 × Fp8))
    (tableCount : Nat)
    (length : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈future,
      (outputs a p q).length=tableCount)
    (mismatch : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈future,
      ¬decodedLocalTerminalCorrect (n+1) (fun column row=>(tr a).cell (start+(if b then 1 else 0)) row column)
        publicValues (residuals a) (claim a) p →
      0<(outputs a p q).length ∧ ∃ lane,
        ((outputs a p q).map Prod.fst).getD lane 0≠((outputs a p q).map Prod.snd).getD lane 0)
    (raw : A → LocalChallengePrefix Fp8 → Q → Fp8 →
      (k : Nat) → List (GKRBlock Fp8) → GKRLayerStrategy Fp8 k)
    (inputs : A → LocalChallengePrefix Fp8 → Q → Fp8 → Nat → Fp8)
    (layers : A → LocalChallengePrefix Fp8 → Q → Fp8 → List (List GKRWiringGate))
    (rootLog : Nat) (bits : Nat → Bool)
    (binding : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈future,∀ rho∈sample,
      gkrFiniteCircuit (inputs a p q rho) (layers a p q rho) (genericRowBitIndex rootLog bits)=terminalResidualValue rho 1 (outputs a p q))
    (nonempty : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈future,∀ rho∈sample,0<(layers a p q rho).length)
    (rootBound : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈future,∀ rho∈sample,
      genericRowBitIndex rootLog bits<((layers a p q rho).getD ((layers a p q rho).length-1) []).length)
    (gates : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈future,∀ rho∈sample,
      (raw a p q rho m []).gates=gkrWeightedLayer rootLog (gkrReverseCircuitWiring (layers a p q rho) 0) [(genericRowBooleanPoint bits,1)])
    (rootClaim : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈future,∀ rho∈sample,
      (raw a p q rho m []).claimLeft []=0)
    (gkrChecks : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈future,∀ rho∈sample,
      ∀ blocks z path qs,accept a p (q,rho,blocks,z,path,qs) →
        gkrEvaluatedVerifierPath (raw a p q rho) (layers a p q rho) [] (m::rest) blocks)
    (errorInclusion : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈future,∀ rho∈sample,
      ∀ item∈evaluatedGKRExperiment sample (m::rest) (gkrPCSContinuationSamples sample layout queries),
      accept a p (q,rho,item) →
      gkrTerminalMismatch (gkrBindCircuitValues (raw a p q rho) (inputs a p q rho) (layers a p q rho))
        (gkrReverseCircuitValues (inputs a p q rho) (layers a p q rho)) 1 [] (m::rest) item.1 →
      failure a p (q,rho,item))
 :
    let downstream := future.flatMap (fun q=>(twoTablePCSContinuations sample layout earlierRounds queries).map (fun r=>(q,r)))
    let experiment := earlier.flatMap (fun a=>(decodedLocalPrefixes sample (n+1)).flatMap
      (fun p=>downstream.map (fun r=>(a,p,r))))
    count experiment (fun x=>accept x.1 x.2.1 x.2.2)*sample.length≤
      earlier.length*
        (((source.length+auxiliaryLength-1+(n+1)+(d+1)*(n+1))*sample.length^(2*(n+1)+1))*downstream.length+
          (decodedLocalPrefixes sample (n+1)).length*
            (future.length*((tableCount-1)*(evaluatedGKRExperiment sample (m::rest) (gkrPCSContinuationSamples sample layout queries)).length*sample.length+
              sample.length*(((m::rest).map (fun k=>4*k+1)).sum*(gkrChallengePaths sample (m::rest)).length*
                (gkrPCSContinuationSamples sample layout queries).length))))+
      count experiment (fun x=>accept x.1 x.2.1 x.2.2 ∧ failure x.1 x.2.1 x.2.2)*sample.length := by
  intro downstream experiment
  apply selected_auxiliary_local_error_count sample distinct earlier fixed tr width start b publicValues
    formulas selected logs cells source auxiliaryLength auxiliaryShape residuals order d n positive
    rowLogs bounds sourceDegrees auxDegrees sent claim initialZero downstream accept failure checks _
  intro a ha p hp wrong
  have h := two_table_terminal_repair sample distinct future layout earlierRounds queries m rest rounds
    (outputs a p) tableCount (length a ha p hp)
    (fun q hq=>mismatch a ha p hp q hq wrong) (raw a p) (inputs a p) (layers a p)
    rootLog bits (binding a ha p hp) (nonempty a ha p hp)
    (rootBound a ha p hp) (gates a ha p hp) (rootClaim a ha p hp)
    (fun q rho blocks z path qs=>accept a p (q,rho,blocks,z,path,qs))
    (fun q rho blocks z path qs=>accept a p (q,rho,blocks,z,path,qs) ∧ failure a p (q,rho,blocks,z,path,qs))
    (gkrChecks a ha p hp)
    (fun q hq rho hr item hi accepted bad=>⟨accepted,errorInclusion a ha p hp q hq rho hr item hi accepted bad⟩)
  exact h

end NearCompression
