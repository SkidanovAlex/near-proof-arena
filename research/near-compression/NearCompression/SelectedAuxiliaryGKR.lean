import NearCompression.SelectedAuxiliaryLocalBudget
import NearCompression.TwoTableTerminalRepair
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra ArenaCore.Security

/-- Substitute actual batching/evaluated-GKR repair after the selected local
protocol. This covers the last-local-table case and retains the shared
accepted failure count for the eventual joint PCS bound. -/
theorem selected_auxiliary_gkr_error_count {A : Type}
    (sample : List Fp8) (distinct : sample.Nodup) (earlier : List A)
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
      (Fp8 × (List (GKRBlock Fp8) × (List Fp8 × (List Fp8 × List Nat)))) → Prop)
    (checks : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),
      ∀ r∈twoTablePCSContinuations sample layout earlierRounds queries,
      accept a p r → decodedLocalChecks d (sent a) (claim a) p)
    (m : Nat) (rest : List Nat) (rounds : earlierRounds++[layout.inputLog]=m::rest)
    (outputs : A → LocalChallengePrefix Fp8 → List (Fp8 × Fp8))
    (tableCount : Nat)
    (length : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),
      (outputs a p).length=tableCount)
    (mismatch : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),
      ¬decodedLocalTerminalCorrect (n+1) (fun column row=>(tr a).cell (start+(if b then 1 else 0)) row column)
        publicValues (residuals a) (claim a) p →
      0<(outputs a p).length ∧ ∃ lane,
        ((outputs a p).map Prod.fst).getD lane 0≠((outputs a p).map Prod.snd).getD lane 0)
    (raw : A → LocalChallengePrefix Fp8 → Fp8 →
      (k : Nat) → List (GKRBlock Fp8) → GKRLayerStrategy Fp8 k)
    (inputs : A → LocalChallengePrefix Fp8 → Fp8 → Nat → Fp8)
    (layers : A → LocalChallengePrefix Fp8 → Fp8 → List (List GKRWiringGate))
    (rootLog : Nat) (bits : Nat → Bool)
    (binding : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,
      gkrFiniteCircuit (inputs a p rho) (layers a p rho) (genericRowBitIndex rootLog bits)=terminalResidualValue rho 1 (outputs a p))
    (nonempty : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,0<(layers a p rho).length)
    (rootBound : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,
      genericRowBitIndex rootLog bits<((layers a p rho).getD ((layers a p rho).length-1) []).length)
    (gates : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,
      (raw a p rho m []).gates=gkrWeightedLayer rootLog (gkrReverseCircuitWiring (layers a p rho) 0) [(genericRowBooleanPoint bits,1)])
    (rootClaim : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,
      (raw a p rho m []).claimLeft []=0)
    (gkrChecks : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,
      ∀ blocks z path qs,accept a p (rho,blocks,z,path,qs) →
        gkrEvaluatedVerifierPath (raw a p rho) (layers a p rho) [] (m::rest) blocks)
    (errorInclusion : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,
      ∀ item∈evaluatedGKRExperiment sample (m::rest) (gkrPCSContinuationSamples sample layout queries),
      accept a p (rho,item) →
      gkrTerminalMismatch (gkrBindCircuitValues (raw a p rho) (inputs a p rho) (layers a p rho))
        (gkrReverseCircuitValues (inputs a p rho) (layers a p rho)) 1 [] (m::rest) item.1 →
      failure a p (rho,item))
 :
    let downstream := twoTablePCSContinuations sample layout earlierRounds queries
    let experiment := earlier.flatMap (fun a=>(decodedLocalPrefixes sample (n+1)).flatMap
      (fun p=>downstream.map (fun r=>(a,p,r))))
    count experiment (fun x=>accept x.1 x.2.1 x.2.2)*sample.length≤
      earlier.length*
        (((source.length+auxiliaryLength-1+(n+1)+(d+1)*(n+1))*sample.length^(2*(n+1)+1))*downstream.length+
          (decodedLocalPrefixes sample (n+1)).length*
            ((tableCount-1)*(evaluatedGKRExperiment sample (m::rest) (gkrPCSContinuationSamples sample layout queries)).length*sample.length+
              sample.length*(((m::rest).map (fun k=>4*k+1)).sum*(gkrChallengePaths sample (m::rest)).length*
                (gkrPCSContinuationSamples sample layout queries).length)))+
      count experiment (fun x=>accept x.1 x.2.1 x.2.2 ∧ failure x.1 x.2.1 x.2.2)*sample.length := by
  intro downstream experiment
  apply selected_auxiliary_local_error_count sample distinct earlier fixed tr width start b publicValues
    formulas selected logs cells source auxiliaryLength auxiliaryShape residuals order d n positive
    rowLogs bounds sourceDegrees auxDegrees sent claim initialZero downstream accept failure checks _
  intro a ha p hp wrong
  have h := two_table_terminal_repair sample distinct [()] layout earlierRounds queries m rest rounds
    (fun _=>outputs a p) tableCount (fun _ _=>length a ha p hp)
    (fun _ _=>mismatch a ha p hp wrong) (fun _=>raw a p) (fun _=>inputs a p) (fun _=>layers a p)
    rootLog bits (fun _ _=>binding a ha p hp) (fun _ _=>nonempty a ha p hp)
    (fun _ _=>rootBound a ha p hp) (fun _ _=>gates a ha p hp) (fun _ _=>rootClaim a ha p hp)
    (fun _ rho blocks z path qs=>accept a p (rho,blocks,z,path,qs))
    (fun _ rho blocks z path qs=>accept a p (rho,blocks,z,path,qs) ∧ failure a p (rho,blocks,z,path,qs))
    (fun _ _=>gkrChecks a ha p hp)
    (fun _ _ rho hr item hi accepted bad=>⟨accepted,errorInclusion a ha p hp rho hr item hi accepted bad⟩)
  dsimp only at h
  simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_cons,List.length_nil,
    Nat.zero_add,Nat.one_mul,count_map] using h

end NearCompression
