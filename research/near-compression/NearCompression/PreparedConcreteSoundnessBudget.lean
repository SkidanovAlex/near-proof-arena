import NearCompression.HistoryConcretePCS
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra ZkFormal.Near
open ArenaCore.Security ZkFormal.Udr NearSpecV3.Wasm

/-- For the locally valid fixed-source branch, derive all numerical bus,
local/GKR and shared PCS terms from existing soundness theorems. Semantic
and ideal-oracle evidence remains explicit, including failure-event inclusion;
this is not native verifier acceptance or a Fiat-Shamir/QROM theorem. -/
theorem prepared_concrete_soundness_budget
    (codeCount : Nat) (sourceWidth : Nat → Nat) (source : Trace Fp) (pub : List Fp)
    (locals : ∀ t (ht : t<(preparedLiteralAir codeCount).tables.length),
      TableLocal (preparedLiteralAir codeCount).tables[t] source t pub)
    (fits : pubFit (preparedLiteralAir codeCount) pub=true)
    (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (blockLevel full : Bool) (eligible : PreparedRunCallEligible)
    (prepared : preparedLiteralRunCallCheck cfg code method ctx pub blockLevel=some eligible)
    (fuel : Nat) (enoughFuel : source.height 0≤fuel)
    (wrong : ¬∃ final error,runCall cfg code method ctx fuel blockLevel full none=.done final error ∧
      PreparedExecPublishedOutput pub final error)
    (sample : List Fp8) (distinct : sample.Nodup) (layout : GKRJointLayout) (earlierRounds : List Nat) (queries n0 n1 : Nat)
    (fixed : (Fp8 × Fp8) → Trace Fp) (coordinateWidth : Nat → Nat)
    (formulas : (Fp8 × Fp8) → Nat → List (BusProgramFormula Fp8))
    (finals : (Fp8 × Fp8) → Nat → Nat → Fp8)
    (widths : ∀ j,∀ hj : j<(preparedLiteralAir codeCount).tables.length,
      (preparedLiteralAir codeCount).tables[j].width=sourceWidth j)
    (sourceChecks : ∀ j,∀ hj : j<(preparedLiteralAir codeCount).tables.length,
      (∀ e∈(preparedLiteralAir codeCount).tables[j].allConstraints,e.colBound≤sourceWidth j) ∧
      (∀ i∈(preparedLiteralAir codeCount).tables[j].interactions,∀ e∈i.exprs,e.colBound≤sourceWidth j))
    (checked : ∀ alpha∈sample,∀ gamma∈sample,∀ j,∀ hj : j<(preparedLiteralAir codeCount).tables.length,
      generatedExt8BusSpecCheck
        ((preparedLiteralAir codeCount).tables[j].interactions.map
          (lowerBusInteraction (pub.map Fp8.ofBase) alpha gamma))
        (sourceWidth j) (finals (alpha,gamma) j) (formulas (alpha,gamma) j)=true)
    (bounds : ∀ alpha∈sample,∀ gamma∈sample,∀ j,∀ hj : j<(preparedLiteralAir codeCount).tables.length,
      ∀ e∈formulas (alpha,gamma) j,busFormulaColumnBound e≤coordinateWidth j)
    (accept failure : (Fp8 × Fp8) → PreparedTwoTableContinuation → Prop)
    (witness : ∀ alpha∈sample,∀ gamma∈sample,∀ r∈preparedTwoTableContinuations sample layout earlierRounds queries n0 n1,
      accept (alpha,gamma) r → failure (alpha,gamma) r ∨
      ∃ decoded : Trace Fp8,
        decoded.log=source.log ∧
        (∀ t row column,column<sourceWidth t → decoded.cell t row column=Fp8.ofBase (source.cell t row column)) ∧
        decoded.log=(fixed (alpha,gamma)).log ∧
        (∀ t row column,column<coordinateWidth t →
          decoded.cell t row column=Fp8.ofBase ((fixed (alpha,gamma)).cell t row column)) ∧
        busExt8ClaimedSideProduct (preparedLiteralAir codeCount) (decodedBaseTrace decoded) sourceWidth pub alpha gamma (finals (alpha,gamma)) true=
          busExt8ClaimedSideProduct (preparedLiteralAir codeCount) (decodedBaseTrace decoded) sourceWidth pub alpha gamma (finals (alpha,gamma)) false)
    (T : Nat) (sizes : Nat → Nat) :
    let pairs := sample.flatMap (fun alpha=>sample.map (fun gamma=>(alpha,gamma)))
    let first := decodedLocalPrefixes sample (n0+1)
    let second := decodedLocalPrefixes sample (n1+1)
    let later := twoTablePCSContinuations sample layout earlierRounds queries
    let continuation := preparedTwoTableContinuations sample layout earlierRounds queries n0 n1
    let branch := fun pair=>twoTableAuxiliaryBranch (airExt8Trace (fixed pair)) (formulas pair) 0
    let chosen0 := pairs.filter (fun a=>@decide (branch a=some false) (Classical.propDecidable _))
    let chosen1 := pairs.filter (fun a=>@decide (branch a=some true) (Classical.propDecidable _))
    let experiment := pairs.flatMap (fun pair=>continuation.map (fun r=>(pair,r)))
    ∀ c0 : SelectedFutureGKREvidence sample distinct chosen0 second layout earlierRounds queries n0
      (fun a p qr=>accept a (p,qr)) (fun a p qr=>failure a (p,qr)),
    ∀ c1 : SelectedLastGKREvidence sample distinct (chosen1.flatMap (fun a=>first.map (fun p=>(a,p))))
      layout earlierRounds queries n1 (fun ap q r=>accept ap.1 (ap.2,q,r)) (fun ap q r=>failure ap.1 (ap.2,q,r)),
    ∀ pcs : ∀ pair∈pairs,ConcreteTwoTablePCSEvidence layout sample distinct T queries sizes
      earlierRounds (n0+1) (n1+1)
      (fun p q rho blocks z path qs=>accept pair (p,q,rho,blocks,z,path,qs) ∧
        failure pair (p,q,rho,blocks,z,path,qs)),
    count experiment (fun x=>accept x.1 x.2)*sample.length≤
      busTraceErrorBudget (preparedLiteralAir codeCount) source pub 28*
        sample.length*continuation.length*sample.length+
      selectedFutureEvidenceBudget sample distinct chosen0 second layout earlierRounds queries n0
        (fun a p qr=>accept a (p,qr)) (fun a p qr=>failure a (p,qr)) c0+
      selectedLastEvidenceBudget sample distinct (chosen1.flatMap (fun a=>first.map (fun p=>(a,p))))
        layout earlierRounds queries n1 (fun ap q r=>accept ap.1 (ap.2,q,r)) (fun ap q r=>failure ap.1 (ap.2,q,r)) c1+
      pairs.length*concreteTwoTablePCSBudget layout sample T queries sizes earlierRounds (n0+1) (n1+1) := by
  intro pairs first second later continuation branch chosen0 chosen1 experiment c0 c1 pcs
  apply prepared_selected_gkr_budget codeCount sourceWidth source pub locals fits cfg code method ctx
    blockLevel full eligible prepared fuel enoughFuel wrong sample distinct layout earlierRounds queries n0 n1
    fixed coordinateWidth formulas finals widths sourceChecks checked bounds accept failure witness
    (pairs.length*concreteTwoTablePCSBudget layout sample T queries sizes earlierRounds (n0+1) (n1+1)) c0 c1
  exact history_concrete_pcs_failure_budget pairs layout sample distinct T queries sizes earlierRounds n0 n1
    (fun pair r=>accept pair r ∧ failure pair r) pcs

end NearCompression
