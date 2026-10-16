import NearCompression.PrechallengeDecodedTables
import NearCompression.DecodedLocalContinuation
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

/-- Semantic data fixed before rho. Register IDs, accumulator witnesses,
reconstruction records and batch-power nodes are deliberately absent. -/
structure TerminalTableMeaning (K : Type) where
  metadata : GKRTableMetadata
  publicValues : List K
  mixing : K
  formulas : List (AIRBusResidual K)
  weight : K
  claim : K

def terminalTableMeaning {K : Type} (metadataOf : SymbolicFormulaTable K → GKRTableMetadata)
    (t : SymbolicFormulaTable K) : TerminalTableMeaning K :=
  ⟨metadataOf t,t.publicValues,t.mixing,t.residuals.map Prod.fst,t.compiled.entry.weight,t.compiled.entry.claim⟩

def terminalMeaningValue {K : Type} [Field K] (decoded : GKRTableMetadata → Nat → Nat → K)
    (history : List K) (t : TerminalTableMeaning K) : K :=
  lanePowerBatch t.mixing (t.formulas.map (airBusResidualValue
    (decodedRowEnvironment t.metadata.rowLog (decoded t.metadata) (gkrTableHistoryPoint t.metadata history)) t.publicValues))*t.weight

def terminalMeaningOutputs {K : Type} [Field K] (decoded : GKRTableMetadata → Nat → Nat → K)
    (history : List K) (tables : List (TerminalTableMeaning K)) : List (K × K) :=
  tables.map (fun t => (terminalMeaningValue decoded history t,t.claim))

/-- Erasing compiler witnesses preserves the complete ordered output list. -/
theorem terminal_outputs_semantic_projection {K : Type} [Field K]
    (metadataOf : SymbolicFormulaTable K → GKRTableMetadata)
    (decoded : GKRTableMetadata → Nat → Nat → K) (history : List K)
    (tables : List (SymbolicFormulaTable K)) :
    historyRowFormulaOutputs metadataOf (fun t => decoded (metadataOf t)) history tables=
      terminalMeaningOutputs decoded history (tables.map (terminalTableMeaning metadataOf)) := by
  unfold historyRowFormulaOutputs terminalMeaningOutputs
  rw [List.map_map]
  apply List.map_congr_left
  intro t _
  unfold terminalMeaningValue terminalTableMeaning
  rw [mixed_formula_power_batch]
  simp only [List.map_map,Function.comp_def]
  congr 1
  grind

/-- A per-rho compiler may change all witnesses while the projected semantic
list stays fixed. The resulting output/claim list is then rho-independent. -/
theorem terminal_outputs_fixed_meaning {K : Type} [Field K]
    (metadataOf : SymbolicFormulaTable K → GKRTableMetadata)
    (decoded : GKRTableMetadata → Nat → Nat → K) (history : List K)
    (tables : List (SymbolicFormulaTable K)) (meanings : List (TerminalTableMeaning K))
    (binding : tables.map (terminalTableMeaning metadataOf)=meanings) :
    historyRowFormulaOutputs metadataOf (fun t => decoded (metadataOf t)) history tables=
      terminalMeaningOutputs decoded history meanings := by
  rw [terminal_outputs_semantic_projection,binding]

/-- A concrete unequal pair supplies the indexed mismatch used by the root
count theorem, without assuming a preferred index or uniqueness of tables. -/
theorem terminal_pair_mismatch_index {K : Type} [Field K]
    (outputs : List (K × K)) (value claim : K) (member : (value,claim)∈outputs) (wrong : value≠claim) :
    0<outputs.length ∧ ∃ lane,(outputs.map Prod.fst).getD lane 0≠(outputs.map Prod.snd).getD lane 0 := by
  obtain ⟨i,hi,same⟩ := List.mem_iff_getElem.mp member
  refine ⟨by omega,i,?_⟩
  have fstBound : i<(outputs.map Prod.fst).length := by simpa using hi
  have sndBound : i<(outputs.map Prod.snd).length := by simpa using hi
  simpa only [List.getD,List.getElem?_eq_getElem fstBound,List.getElem?_eq_getElem sndBound,
    Option.getD_some,List.getElem_map,same] using wrong

/-- Match the local weighted terminal to one semantic table. A wrong local
claim implies a nonzero batch coefficient, before rho is sampled. -/
theorem local_terminal_semantic_mismatch {K : Type} [Field K]
    (decoded : GKRTableMetadata → Nat → Nat → K) (history : List K)
    (meanings : List (TerminalTableMeaning K)) (t : TerminalTableMeaning K) (member : t∈meanings)
    (p : LocalChallengePrefix K) (claim : K → List K → List K → K)
    (residuals : List (AIRBusResidual K × Nat))
    (point : gkrTableHistoryPoint t.metadata history=p.2)
    (mixing : t.mixing=p.1.1) (formulas : t.formulas=residuals.map Prod.fst)
    (weight : t.weight=whirKernel p.1.2 p.2) (sentClaim : t.claim=claim p.1.1 p.1.2 p.2)
    (wrong : ¬decodedLocalTerminalCorrect t.metadata.rowLog (decoded t.metadata) t.publicValues residuals claim p) :
    0<(terminalMeaningOutputs decoded history meanings).length ∧
      ∃ lane,((terminalMeaningOutputs decoded history meanings).map Prod.fst).getD lane 0≠
        ((terminalMeaningOutputs decoded history meanings).map Prod.snd).getD lane 0 := by
  apply terminal_pair_mismatch_index _ (terminalMeaningValue decoded history t) t.claim
    (List.mem_map.mpr ⟨t,member,rfl⟩)
  intro equal
  apply wrong
  unfold decodedLocalTerminalCorrect
  unfold terminalMeaningValue at equal
  rw [point,mixing,formulas,weight,sentClaim,List.map_map] at equal
  rw [mixed_formula_power_batch]
  simp only [Function.comp_def] at equal
  grind

/-- Compose source ownership, checked selector transport, and witness erasure.
The decoded family and semantic list can both precede a rho-dependent compiler. -/
theorem preselected_semantic_outputs {K : Type} [Field K] [DecidableEq K]
    (C : Nat) (metadata : List GKRTableMetadata) (entries : List (GKRSourceLane × Poly K))
    (decoded : GKRTableMetadata → Nat → Nat → K)
    (agreement : ∀ table∈metadata,∀ placement : TerminalSymbolicPlacement K,
      symbolicPlacementMetadataCheck placement table=true → ∀ rowpoints : GKRSourceLane → Nat → K,
        TerminalEnvironmentAgreement (table.sourceWidth+table.auxiliaryWidth)
          (placement.environment (gkrScatter (recoveredPrivateSlots C entries rowpoints)))
          (decodedColumnEnvironment table placement (decoded table) rowpoints))
    (layout : GKRJointLayout) (history : List K) (tables : List (SymbolicFormulaTable K))
    (metadataOf : SymbolicFormulaTable K → GKRTableMetadata)
    (meanings : List (TerminalTableMeaning K))
    (binding : tables.map (terminalTableMeaning metadataOf)=meanings)
    (members : ∀ t∈tables,metadataOf t∈metadata)
    (placements : ∀ t∈tables,symbolicPlacementMetadataCheck t.compiled.placement (metadataOf t)=true)
    (selectors : ∀ t∈tables,symbolicSelectorCheck (metadataOf t).rowLog t.compiled.placement
      (gkrTableHistoryPoint (metadataOf t) history)=true)
    (widths : ∀ t∈tables,t.width≤(metadataOf t).sourceWidth+(metadataOf t).auxiliaryWidth)
    (checked : tables.all symbolicFormulaTableCheck=true) :
    symbolicFormulaOutputs (gkrScatter (recoveredPrivateSlots C entries (gkrHistoryRowpoints layout history))) tables=
      terminalMeaningOutputs decoded history meanings := by
  rw [preselected_formula_outputs C metadata entries decoded agreement _ tables metadataOf members placements widths checked,
    history_decoded_formula_outputs layout history tables metadataOf _ selectors widths checked,
    terminal_outputs_fixed_meaning metadataOf decoded history tables meanings binding]

/-- A wrong local terminal claim can vanish in a later compiled batch for at
most tableCount-1 sampled rho values. Semantic binding is required for every
rho; compiler witnesses and circuit structure may vary with it. -/
theorem local_terminal_compiler_cancellation {K : Type} [Field K]
    (decoded : GKRTableMetadata → Nat → Nat → K) (history : List K)
    (meanings : List (TerminalTableMeaning K)) (t : TerminalTableMeaning K) (member : t∈meanings)
    (p : LocalChallengePrefix K) (claim : K → List K → List K → K)
    (residuals : List (AIRBusResidual K × Nat))
    (point : gkrTableHistoryPoint t.metadata history=p.2)
    (mixing : t.mixing=p.1.1) (formulas : t.formulas=residuals.map Prod.fst)
    (weight : t.weight=whirKernel p.1.2 p.2) (sentClaim : t.claim=claim p.1.1 p.1.2 p.2)
    (wrong : ¬decodedLocalTerminalCorrect t.metadata.rowLog (decoded t.metadata) t.publicValues residuals claim p)
    (sample : List K) (distinct : sample.Nodup)
    (tables : K → List (SymbolicFormulaTable K))
    (metadataOf : SymbolicFormulaTable K → GKRTableMetadata)
    (fixedMeaning : ∀ rho∈sample,(tables rho).map (terminalTableMeaning metadataOf)=meanings)
    (circuit : K → K)
    (compiled : ∀ rho∈sample,circuit rho=terminalResidualValue rho 1
      (historyRowFormulaOutputs metadataOf (fun t => decoded (metadataOf t)) history (tables rho))) :
    count sample (fun rho => circuit rho=0)≤meanings.length-1 := by
  obtain ⟨positive,lane,mismatch⟩ := local_terminal_semantic_mismatch decoded history meanings t member
    p claim residuals point mixing formulas weight sentClaim wrong
  have bound := terminal_circuit_cancellation_count (terminalMeaningOutputs decoded history meanings)
    lane positive mismatch sample distinct circuit (by
      intro rho hr
      rw [compiled rho hr,terminal_outputs_fixed_meaning metadataOf decoded history (tables rho) meanings (fixedMeaning rho hr)])
  simpa only [terminalMeaningOutputs,List.length_map] using bound

end NearCompression
