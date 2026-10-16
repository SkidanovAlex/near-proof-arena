import NearCompression.FirstTableEvaluatedGKRPCS
import NearCompression.CheckedTerminalSemantics
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

/-- Checked scalar terminal bindings and checked compiler witnesses supply
both the mismatch and finite-circuit identity for evaluated GKR repair. -/
theorem checked_terminal_gkr_repair
    (C capacity : Nat) (metadata : List GKRTableMetadata) (entries : List (GKRSourceLane × Poly Fp8))
    (decoded : GKRTableMetadata → Nat → Nat → Fp8)
    (agreement : ∀ table∈metadata,∀ placement : TerminalSymbolicPlacement Fp8,
      symbolicPlacementMetadataCheck placement table=true → ∀ rowpoints : GKRSourceLane → Nat → Fp8,
        TerminalEnvironmentAgreement (table.sourceWidth+table.auxiliaryWidth)
          (placement.environment (gkrScatter (recoveredPrivateSlots C entries rowpoints)))
          (decodedColumnEnvironment table placement (decoded table) rowpoints))
    (layout : GKRJointLayout) (history : List Fp8) (witness : Fp8 → TerminalCompilerWitness Fp8)
    (metadataOf : SymbolicFormulaTable Fp8 → GKRTableMetadata) (meanings : List (TerminalTableMeaning Fp8))
    (selected : TerminalTableMeaning Fp8) (selectedMember : selected∈meanings)
    (p : LocalChallengePrefix Fp8) (localClaim : Fp8 → List Fp8 → List Fp8 → Fp8)
    (residuals : List (AIRBusResidual Fp8 × Nat))
    (point : gkrTableHistoryPoint selected.metadata history=p.2)
    (formulas : selected.formulas=residuals.map Prod.fst)
    (terminalCheck : localTerminalBindingCheck selected.metadata.rowLog p.2 p.1.2 selected.mixing p.1.1
      selected.weight selected.claim (localClaim p.1.1 p.1.2 p.2)=true)
    (wrong : ¬decodedLocalTerminalCorrect selected.metadata.rowLog (decoded selected.metadata)
      selected.publicValues residuals localClaim p)
    (sample : List Fp8) (distinct : sample.Nodup)
    (geometry : ∀ e∈entries,e.1.inputStart+e.1.width≤capacity ∧ e.1.inputStart+e.1.nextOffset+e.1.width≤capacity)
    (binding : ∀ rho∈sample,(witness rho).tables.map (terminalTableMeaning metadataOf)=meanings)
    (constantBound : ∀ rho∈sample,∀ e∈(witness rho).constants,capacity≤e.1)
    (members : ∀ rho∈sample,∀ t∈(witness rho).tables,metadataOf t∈metadata)
    (placements : ∀ rho∈sample,∀ t∈(witness rho).tables,
      symbolicPlacementMetadataCheck t.compiled.placement (metadataOf t)=true)
    (selectors : ∀ rho∈sample,∀ t∈(witness rho).tables,
      symbolicSelectorCheck (metadataOf t).rowLog t.compiled.placement (gkrTableHistoryPoint (metadataOf t) history)=true)
    (widths : ∀ rho∈sample,∀ t∈(witness rho).tables,t.width≤(metadataOf t).sourceWidth+(metadataOf t).auxiliaryWidth)
    (checked : ∀ rho∈sample,terminalCompilerWitnessCheck capacity rho (witness rho)=true)
    (earlierRounds : List Nat) (queryCount m : Nat) (rest : List Nat)
    (rounds : earlierRounds++[layout.inputLog]=m::rest)
    (raw : Fp8 → (k : Nat) → List (GKRBlock Fp8) → GKRLayerStrategy Fp8 k)
    (rootLog : Nat) (bits : Nat → Bool)
    (outputSlot : ∀ rho∈sample,(witness rho).outputSlot=genericRowBitIndex rootLog bits)
    (nonempty : ∀ rho∈sample,0<(witness rho).stages.length)
    (rootBound : ∀ rho∈sample,genericRowBitIndex rootLog bits<
      (((witness rho).stages.map (fun s=>s.gates)).getD ((witness rho).stages.length-1) []).length)
    (gates : ∀ rho∈sample,(raw rho m []).gates=gkrWeightedLayer rootLog
      (gkrReverseCircuitWiring ((witness rho).stages.map (fun s=>s.gates)) 0) [(genericRowBooleanPoint bits,1)])
    (rootClaim : ∀ rho∈sample,(raw rho m []).claimLeft []=0)
    (accept event : Fp8 → List (GKRBlock Fp8) → List Fp8 → List Fp8 → List Nat → Prop)
    (gkrChecks : ∀ rho∈sample,∀ blocks z path qs,accept rho blocks z path qs →
      gkrEvaluatedVerifierPath (raw rho) ((witness rho).stages.map (fun s=>s.gates)) [] (m::rest) blocks)
    (errorInclusion : ∀ rho∈sample,
      ∀ item∈evaluatedGKRExperiment sample (m::rest) (gkrPCSContinuationSamples sample layout queryCount),
      accept rho item.1 item.2.1 item.2.2.1 item.2.2.2 →
      gkrTerminalMismatch
        (gkrBindCircuitValues (raw rho)
          (gkrRecoveredCircuitInput C entries (gkrHistoryRowpoints layout history) (witness rho).constants)
          ((witness rho).stages.map (fun s=>s.gates)))
        (gkrReverseCircuitValues
          (gkrRecoveredCircuitInput C entries (gkrHistoryRowpoints layout history) (witness rho).constants)
          ((witness rho).stages.map (fun s=>s.gates))) 1 [] (m::rest) item.1 →
      event rho item.1 item.2.1 item.2.2.1 item.2.2.2) :
    let downstream := twoTablePCSContinuations sample layout earlierRounds queryCount
    count downstream (fun r=>accept r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2)*sample.length ≤
      (meanings.length-1)*
        (evaluatedGKRExperiment sample (m::rest) (gkrPCSContinuationSamples sample layout queryCount)).length*sample.length+
      sample.length*(((m::rest).map (fun k=>4*k+1)).sum*
        (gkrChallengePaths sample (m::rest)).length*(gkrPCSContinuationSamples sample layout queryCount).length)+
      count downstream (fun r=>event r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2)*sample.length := by
  intro downstream
  have mismatch := checked_local_terminal_mismatch decoded history meanings selected selectedMember
    p localClaim residuals point formulas terminalCheck wrong
  have value : ∀ rho∈sample,
      gkrFiniteCircuit
        (gkrRecoveredCircuitInput C entries (gkrHistoryRowpoints layout history) (witness rho).constants)
        ((witness rho).stages.map (fun s=>s.gates)) (genericRowBitIndex rootLog bits)=
      terminalResidualValue rho 1 (terminalMeaningOutputs decoded history meanings) := by
    intro rho hr
    have h := checked_semantic_circuit_value C capacity metadata entries decoded agreement layout history rho
      (witness rho) metadataOf meanings (binding rho hr) geometry (constantBound rho hr)
      (members rho hr) (placements rho hr) (selectors rho hr) (widths rho hr) (checked rho hr)
    simpa only [recoveredWitnessValue,outputSlot rho hr] using h
  have h := two_table_terminal_repair sample distinct [()] layout earlierRounds queryCount m rest rounds
    (fun _=>terminalMeaningOutputs decoded history meanings) meanings.length
    (fun _ _=>by simp only [terminalMeaningOutputs,List.length_map]) (fun _ _=>mismatch)
    (fun _=>raw)
    (fun _ rho=>gkrRecoveredCircuitInput C entries (gkrHistoryRowpoints layout history) (witness rho).constants)
    (fun _ rho=>(witness rho).stages.map (fun s=>s.gates)) rootLog bits
    (fun _ _=>value) (fun _ _ rho hr=>by simpa only [List.length_map] using nonempty rho hr)
    (fun _ _ rho hr=>by simpa only [List.length_map] using rootBound rho hr)
    (fun _ _=>gates) (fun _ _=>rootClaim) (fun _=>accept) (fun _=>event)
    (fun _ _=>gkrChecks) (fun _ _=>errorInclusion)
  dsimp only at h
  simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_cons,List.length_nil,
    Nat.zero_add,Nat.one_mul,count_map] using h

end NearCompression
