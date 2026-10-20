import NearCompression.SelectedAuxiliaryFutureGKR
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra ArenaCore.Security

/-- Semantic proof data for selected-table soundness. Numeric acceptance
budgets are computed from geometry, not supplied as proof fields. -/
structure SelectedLastGKREvidence {A : Type}
    (sample : List Fp8) (distinct : sample.Nodup) (earlier : List A)
    (layout : GKRJointLayout) (earlierRounds : List Nat) (queries n : Nat)
    (accept failure : A → LocalChallengePrefix Fp8 →
      (Fp8 × (List (GKRBlock Fp8) × (List Fp8 × (List Fp8 × List Nat)))) → Prop) where
  fixed : A → Trace Fp
  tr : A → Trace Fp8
  width : Nat → Nat
  start : Nat
  b : Bool
  publicValues : List Fp8
  formulas : A → Nat → List (BusProgramFormula Fp8)
  selected : ∀ a∈earlier,twoTableAuxiliaryBranch (airExt8Trace (fixed a)) (formulas a) start=some b
  logs : ∀ a∈earlier,(tr a).log=(fixed a).log
  cells : ∀ a∈earlier,∀ t row column,column<width t →
      (tr a).cell t row column=Fp8.ofBase ((fixed a).cell t row column)
  source : List Expr
  auxiliaryLength : Nat
  auxiliaryShape : ∀ a∈earlier,(formulas a (start+(if b then 1 else 0))).length=auxiliaryLength
  residuals : A → List (AIRBusResidual Fp8 × Nat)
  order : ∀ a∈earlier,(residuals a).map Prod.fst=source.map Sum.inl++(formulas a (start+(if b then 1 else 0))).map Sum.inr
  d : Nat
  positive : 0<source.length+auxiliaryLength
  rowLogs : ∀ a∈earlier,(tr a).log (start+(if b then 1 else 0))=n+1
  bounds : ∀ a∈earlier,∀ e∈formulas a (start+(if b then 1 else 0)),
      busFormulaColumnBound e≤width (start+(if b then 1 else 0))
  sourceDegrees : ∀ e∈source,e.degree≤d
  auxDegrees : ∀ a∈earlier,∀ e∈formulas a (start+(if b then 1 else 0)),busFormulaDegree e≤d
  sent : A → Fp8 → List Fp8 → List Fp8 → Poly Fp8
  claim : A → Fp8 → List Fp8 → List Fp8 → Fp8
  initialZero : ∀ a∈earlier,∀ mixing tau,claim a mixing tau []=0
  checks : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),
      ∀ r∈twoTablePCSContinuations sample layout earlierRounds queries,
      accept a p r → decodedLocalChecks d (sent a) (claim a) p
  m : Nat
  rest : List Nat
  rounds : earlierRounds++[layout.inputLog]=m::rest
  outputs : A → LocalChallengePrefix Fp8 → List (Fp8 × Fp8)
  tableCount : Nat
  length : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),
      (outputs a p).length=tableCount
  mismatch : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),
      ¬decodedLocalTerminalCorrect (n+1) (fun column row=>(tr a).cell (start+(if b then 1 else 0)) row column)
        publicValues (residuals a) (claim a) p →
      0<(outputs a p).length ∧ ∃ lane,
        ((outputs a p).map Prod.fst).getD lane 0≠((outputs a p).map Prod.snd).getD lane 0
  raw : A → LocalChallengePrefix Fp8 → Fp8 →
      (k : Nat) → List (GKRBlock Fp8) → GKRLayerStrategy Fp8 k
  inputs : A → LocalChallengePrefix Fp8 → Fp8 → Nat → Fp8
  layers : A → LocalChallengePrefix Fp8 → Fp8 → List (List GKRWiringGate)
  rootLog : Nat
  bits : Nat → Bool
  binding : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,
      gkrFiniteCircuit (inputs a p rho) (layers a p rho) (genericRowBitIndex rootLog bits)=terminalResidualValue rho 1 (outputs a p)
  nonempty : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,0<(layers a p rho).length
  rootBound : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,
      genericRowBitIndex rootLog bits<((layers a p rho).getD ((layers a p rho).length-1) []).length
  gates : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,
      (raw a p rho m []).gates=gkrWeightedLayer rootLog (gkrReverseCircuitWiring (layers a p rho) 0) [(genericRowBooleanPoint bits,1)]
  rootClaim : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,
      (raw a p rho m []).claimLeft []=0
  gkrChecks : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,
      ∀ blocks z path qs,accept a p (rho,blocks,z,path,qs) →
        gkrEvaluatedVerifierPath (raw a p rho) (layers a p rho) [] (m::rest) blocks
  errorInclusion : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ rho∈sample,
      ∀ item∈evaluatedGKRExperiment sample (m::rest) (gkrPCSContinuationSamples sample layout queries),
      accept a p (rho,item) →
      gkrTerminalMismatch (gkrBindCircuitValues (raw a p rho) (inputs a p rho) (layers a p rho))
        (gkrReverseCircuitValues (inputs a p rho) (layers a p rho)) 1 [] (m::rest) item.1 →
      failure a p (rho,item)

noncomputable def selectedLastEvidenceBudget {A : Type}
    (sample : List Fp8) (distinct : sample.Nodup) (earlier : List A)
    (layout : GKRJointLayout) (earlierRounds : List Nat) (queries n : Nat)
    (accept failure : A → LocalChallengePrefix Fp8 →
      (Fp8 × (List (GKRBlock Fp8) × (List Fp8 × (List Fp8 × List Nat)))) → Prop)
    (c : SelectedLastGKREvidence sample distinct earlier layout earlierRounds queries n accept failure) : Nat :=
  earlier.length*
    (((c.source.length+c.auxiliaryLength-1+(n+1)+(c.d+1)*(n+1))*sample.length^(2*(n+1)+1))*(twoTablePCSContinuations sample layout earlierRounds queries).length+
      (decodedLocalPrefixes sample (n+1)).length*((c.tableCount-1)*(evaluatedGKRExperiment sample (c.m::c.rest) (gkrPCSContinuationSamples sample layout queries)).length*sample.length+
      sample.length*(((c.m::c.rest).map (fun k=>4*k+1)).sum*(gkrChallengePaths sample (c.m::c.rest)).length*
        (gkrPCSContinuationSamples sample layout queries).length)))

/-- Apply the existing selected local/GKR theorem to semantic evidence;
no local acceptance inequality is stored in the evidence record. -/
theorem selected_last_evidence_bound {A : Type}
    (sample : List Fp8) (distinct : sample.Nodup) (earlier : List A)
    (layout : GKRJointLayout) (earlierRounds : List Nat) (queries n : Nat)
    (accept failure : A → LocalChallengePrefix Fp8 →
      (Fp8 × (List (GKRBlock Fp8) × (List Fp8 × (List Fp8 × List Nat)))) → Prop)
    (c : SelectedLastGKREvidence sample distinct earlier layout earlierRounds queries n accept failure) :
    let downstream := twoTablePCSContinuations sample layout earlierRounds queries
    let experiment := earlier.flatMap (fun a=>(decodedLocalPrefixes sample (n+1)).flatMap
      (fun p=>downstream.map (fun r=>(a,p,r))))
    count experiment (fun x=>accept x.1 x.2.1 x.2.2)*sample.length≤
      selectedLastEvidenceBudget sample distinct earlier layout earlierRounds queries n accept failure c+
      count experiment (fun x=>accept x.1 x.2.1 x.2.2 ∧ failure x.1 x.2.1 x.2.2)*sample.length := by
  exact selected_auxiliary_gkr_error_count
    sample distinct earlier layout earlierRounds queries c.fixed c.tr c.width c.start c.b c.publicValues c.formulas c.selected c.logs c.cells c.source c.auxiliaryLength c.auxiliaryShape c.residuals c.order c.d n c.positive c.rowLogs c.bounds c.sourceDegrees c.auxDegrees c.sent c.claim c.initialZero accept failure c.checks c.m c.rest c.rounds c.outputs c.tableCount c.length c.mismatch c.raw c.inputs c.layers c.rootLog c.bits c.binding c.nonempty c.rootBound c.gates c.rootClaim c.gkrChecks c.errorInclusion


structure SelectedFutureGKREvidence {A Q : Type}
    (sample : List Fp8) (distinct : sample.Nodup) (earlier : List A) (future : List Q)
    (layout : GKRJointLayout) (earlierRounds : List Nat) (queries n : Nat)
    (accept failure : A → LocalChallengePrefix Fp8 →
      (Q × (Fp8 × (List (GKRBlock Fp8) × (List Fp8 × (List Fp8 × List Nat))))) → Prop) where
  fixed : A → Trace Fp
  tr : A → Trace Fp8
  width : Nat → Nat
  start : Nat
  b : Bool
  publicValues : List Fp8
  formulas : A → Nat → List (BusProgramFormula Fp8)
  selected : ∀ a∈earlier,twoTableAuxiliaryBranch (airExt8Trace (fixed a)) (formulas a) start=some b
  logs : ∀ a∈earlier,(tr a).log=(fixed a).log
  cells : ∀ a∈earlier,∀ t row column,column<width t →
      (tr a).cell t row column=Fp8.ofBase ((fixed a).cell t row column)
  source : List Expr
  auxiliaryLength : Nat
  auxiliaryShape : ∀ a∈earlier,(formulas a (start+(if b then 1 else 0))).length=auxiliaryLength
  residuals : A → List (AIRBusResidual Fp8 × Nat)
  order : ∀ a∈earlier,(residuals a).map Prod.fst=source.map Sum.inl++(formulas a (start+(if b then 1 else 0))).map Sum.inr
  d : Nat
  positive : 0<source.length+auxiliaryLength
  rowLogs : ∀ a∈earlier,(tr a).log (start+(if b then 1 else 0))=n+1
  bounds : ∀ a∈earlier,∀ e∈formulas a (start+(if b then 1 else 0)),
      busFormulaColumnBound e≤width (start+(if b then 1 else 0))
  sourceDegrees : ∀ e∈source,e.degree≤d
  auxDegrees : ∀ a∈earlier,∀ e∈formulas a (start+(if b then 1 else 0)),busFormulaDegree e≤d
  sent : A → Fp8 → List Fp8 → List Fp8 → Poly Fp8
  claim : A → Fp8 → List Fp8 → List Fp8 → Fp8
  initialZero : ∀ a∈earlier,∀ mixing tau,claim a mixing tau []=0
  checks : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),
      ∀ r∈future.flatMap (fun q=>(twoTablePCSContinuations sample layout earlierRounds queries).map (fun r=>(q,r))),
      accept a p r → decodedLocalChecks d (sent a) (claim a) p
  m : Nat
  rest : List Nat
  rounds : earlierRounds++[layout.inputLog]=m::rest
  outputs : A → LocalChallengePrefix Fp8 → Q → List (Fp8 × Fp8)
  tableCount : Nat
  length : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈future,
      (outputs a p q).length=tableCount
  mismatch : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈future,
      ¬decodedLocalTerminalCorrect (n+1) (fun column row=>(tr a).cell (start+(if b then 1 else 0)) row column)
        publicValues (residuals a) (claim a) p →
      0<(outputs a p q).length ∧ ∃ lane,
        ((outputs a p q).map Prod.fst).getD lane 0≠((outputs a p q).map Prod.snd).getD lane 0
  raw : A → LocalChallengePrefix Fp8 → Q → Fp8 →
      (k : Nat) → List (GKRBlock Fp8) → GKRLayerStrategy Fp8 k
  inputs : A → LocalChallengePrefix Fp8 → Q → Fp8 → Nat → Fp8
  layers : A → LocalChallengePrefix Fp8 → Q → Fp8 → List (List GKRWiringGate)
  rootLog : Nat
  bits : Nat → Bool
  binding : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈future,∀ rho∈sample,
      gkrFiniteCircuit (inputs a p q rho) (layers a p q rho) (genericRowBitIndex rootLog bits)=terminalResidualValue rho 1 (outputs a p q)
  nonempty : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈future,∀ rho∈sample,0<(layers a p q rho).length
  rootBound : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈future,∀ rho∈sample,
      genericRowBitIndex rootLog bits<((layers a p q rho).getD ((layers a p q rho).length-1) []).length
  gates : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈future,∀ rho∈sample,
      (raw a p q rho m []).gates=gkrWeightedLayer rootLog (gkrReverseCircuitWiring (layers a p q rho) 0) [(genericRowBooleanPoint bits,1)]
  rootClaim : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈future,∀ rho∈sample,
      (raw a p q rho m []).claimLeft []=0
  gkrChecks : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈future,∀ rho∈sample,
      ∀ blocks z path qs,accept a p (q,rho,blocks,z,path,qs) →
        gkrEvaluatedVerifierPath (raw a p q rho) (layers a p q rho) [] (m::rest) blocks
  errorInclusion : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈future,∀ rho∈sample,
      ∀ item∈evaluatedGKRExperiment sample (m::rest) (gkrPCSContinuationSamples sample layout queries),
      accept a p (q,rho,item) →
      gkrTerminalMismatch (gkrBindCircuitValues (raw a p q rho) (inputs a p q rho) (layers a p q rho))
        (gkrReverseCircuitValues (inputs a p q rho) (layers a p q rho)) 1 [] (m::rest) item.1 →
      failure a p (q,rho,item)

noncomputable def selectedFutureEvidenceBudget {A Q : Type}
    (sample : List Fp8) (distinct : sample.Nodup) (earlier : List A) (future : List Q)
    (layout : GKRJointLayout) (earlierRounds : List Nat) (queries n : Nat)
    (accept failure : A → LocalChallengePrefix Fp8 →
      (Q × (Fp8 × (List (GKRBlock Fp8) × (List Fp8 × (List Fp8 × List Nat))))) → Prop)
    (c : SelectedFutureGKREvidence sample distinct earlier future layout earlierRounds queries n accept failure) : Nat :=
  earlier.length*
    (((c.source.length+c.auxiliaryLength-1+(n+1)+(c.d+1)*(n+1))*sample.length^(2*(n+1)+1))*(future.flatMap (fun q=>(twoTablePCSContinuations sample layout earlierRounds queries).map (fun r=>(q,r)))).length+
      (decodedLocalPrefixes sample (n+1)).length*(future.length*((c.tableCount-1)*(evaluatedGKRExperiment sample (c.m::c.rest) (gkrPCSContinuationSamples sample layout queries)).length*sample.length+
      sample.length*(((c.m::c.rest).map (fun k=>4*k+1)).sum*(gkrChallengePaths sample (c.m::c.rest)).length*
        (gkrPCSContinuationSamples sample layout queries).length))))

/-- Apply the existing selected local/GKR theorem to semantic evidence;
no local acceptance inequality is stored in the evidence record. -/
theorem selected_future_evidence_bound {A Q : Type}
    (sample : List Fp8) (distinct : sample.Nodup) (earlier : List A) (future : List Q)
    (layout : GKRJointLayout) (earlierRounds : List Nat) (queries n : Nat)
    (accept failure : A → LocalChallengePrefix Fp8 →
      (Q × (Fp8 × (List (GKRBlock Fp8) × (List Fp8 × (List Fp8 × List Nat))))) → Prop)
    (c : SelectedFutureGKREvidence sample distinct earlier future layout earlierRounds queries n accept failure) :
    let downstream := future.flatMap (fun q=>(twoTablePCSContinuations sample layout earlierRounds queries).map (fun r=>(q,r)))
    let experiment := earlier.flatMap (fun a=>(decodedLocalPrefixes sample (n+1)).flatMap
      (fun p=>downstream.map (fun r=>(a,p,r))))
    count experiment (fun x=>accept x.1 x.2.1 x.2.2)*sample.length≤
      selectedFutureEvidenceBudget sample distinct earlier future layout earlierRounds queries n accept failure c+
      count experiment (fun x=>accept x.1 x.2.1 x.2.2 ∧ failure x.1 x.2.1 x.2.2)*sample.length := by
  exact selected_auxiliary_future_gkr_error_count
    sample distinct earlier future layout earlierRounds queries c.fixed c.tr c.width c.start c.b c.publicValues c.formulas c.selected c.logs c.cells c.source c.auxiliaryLength c.auxiliaryShape c.residuals c.order c.d n c.positive c.rowLogs c.bounds c.sourceDegrees c.auxDegrees c.sent c.claim c.initialZero accept failure c.checks c.m c.rest c.rounds c.outputs c.tableCount c.length c.mismatch c.raw c.inputs c.layers c.rootLog c.bits c.binding c.nonempty c.rootBound c.gates c.rootClaim c.gkrChecks c.errorInclusion

end NearCompression
