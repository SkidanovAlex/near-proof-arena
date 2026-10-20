import NearCompression.LocalTerminalBindingCheck
import NearCompression.TerminalSemanticOutputs
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

/-- The checker used by the native adapter supplies all scalar terminal
bindings. History point and formula-specification bindings remain separate. -/
theorem checked_local_terminal_mismatch {K : Type} [Field K] [DecidableEq K]
    (decoded : GKRTableMetadata → Nat → Nat → K) (history : List K)
    (meanings : List (TerminalTableMeaning K)) (t : TerminalTableMeaning K) (member : t∈meanings)
    (p : LocalChallengePrefix K) (claim : K → List K → List K → K)
    (residuals : List (AIRBusResidual K × Nat))
    (point : gkrTableHistoryPoint t.metadata history=p.2)
    (formulas : t.formulas=residuals.map Prod.fst)
    (checked : localTerminalBindingCheck t.metadata.rowLog p.2 p.1.2 t.mixing p.1.1
      t.weight t.claim (claim p.1.1 p.1.2 p.2)=true)
    (wrong : ¬decodedLocalTerminalCorrect t.metadata.rowLog (decoded t.metadata) t.publicValues residuals claim p) :
    0<(terminalMeaningOutputs decoded history meanings).length ∧
      ∃ lane,((terminalMeaningOutputs decoded history meanings).map Prod.fst).getD lane 0≠
        ((terminalMeaningOutputs decoded history meanings).map Prod.snd).getD lane 0 := by
  have bindings := local_terminal_binding_checked _ _ _ _ _ _ _ _ checked
  exact local_terminal_semantic_mismatch decoded history meanings t member p claim residuals point
    bindings.2.2.1 formulas bindings.2.2.2.1 bindings.2.2.2.2 wrong

/-- A selected checked compiler table directly supplies the local mismatch
coefficient. Its semantic table membership follows from the checked list
projection; no separately postulated semantic-table membership is needed. -/
theorem checked_formula_table_mismatch {K : Type} [Field K] [DecidableEq K]
    (metadataOf : SymbolicFormulaTable K → GKRTableMetadata)
    (decoded : GKRTableMetadata → Nat → Nat → K) (history : List K)
    (tables : List (SymbolicFormulaTable K)) (t : SymbolicFormulaTable K) (member : t∈tables)
    (meanings : List (TerminalTableMeaning K))
    (projection : tables.map (terminalTableMeaning metadataOf)=meanings)
    (p : LocalChallengePrefix K) (claim : K → List K → List K → K)
    (point : gkrTableHistoryPoint (metadataOf t) history=p.2)
    (checked : localTerminalBindingCheck (metadataOf t).rowLog p.2 p.1.2 t.mixing p.1.1
      t.compiled.entry.weight t.compiled.entry.claim (claim p.1.1 p.1.2 p.2)=true)
    (wrong : ¬decodedLocalTerminalCorrect (metadataOf t).rowLog (decoded (metadataOf t))
      t.publicValues t.residuals claim p) :
    0<(terminalMeaningOutputs decoded history meanings).length ∧
      ∃ lane,((terminalMeaningOutputs decoded history meanings).map Prod.fst).getD lane 0≠
        ((terminalMeaningOutputs decoded history meanings).map Prod.snd).getD lane 0 := by
  have semanticMember : terminalTableMeaning metadataOf t∈meanings := by
    rw [←projection]
    exact List.mem_map.mpr ⟨t,member,rfl⟩
  exact checked_local_terminal_mismatch decoded history meanings (terminalTableMeaning metadataOf t)
    semanticMember p claim t.residuals point rfl checked wrong

/-- The native terminal checker plus ordered semantic binding feeds the
batching root bound. Compiled circuit identities still come from the separate
checked compiler theorem, and the semantic list must precede rho. -/
theorem checked_formula_batch_cancellation {K : Type} [Field K] [DecidableEq K]
    (metadataOf : SymbolicFormulaTable K → GKRTableMetadata)
    (decoded : GKRTableMetadata → Nat → Nat → K) (history : List K)
    (tables : List (SymbolicFormulaTable K)) (t : SymbolicFormulaTable K) (member : t∈tables)
    (meanings : List (TerminalTableMeaning K))
    (projection : tables.map (terminalTableMeaning metadataOf)=meanings)
    (p : LocalChallengePrefix K) (claim : K → List K → List K → K)
    (point : gkrTableHistoryPoint (metadataOf t) history=p.2)
    (checked : localTerminalBindingCheck (metadataOf t).rowLog p.2 p.1.2 t.mixing p.1.1
      t.compiled.entry.weight t.compiled.entry.claim (claim p.1.1 p.1.2 p.2)=true)
    (wrong : ¬decodedLocalTerminalCorrect (metadataOf t).rowLog (decoded (metadataOf t))
      t.publicValues t.residuals claim p)
    (sample : List K) (distinct : sample.Nodup) (circuit : K → K)
    (binding : ∀ rho∈sample,circuit rho=terminalResidualValue rho 1 (terminalMeaningOutputs decoded history meanings)) :
    count sample (fun rho => circuit rho=0)≤meanings.length-1 := by
  obtain ⟨positive,lane,mismatch⟩ := checked_formula_table_mismatch metadataOf decoded history tables t member
    meanings projection p claim point checked wrong
  have bound := terminal_circuit_cancellation_count (terminalMeaningOutputs decoded history meanings)
    lane positive mismatch sample distinct circuit binding
  simpa only [terminalMeaningOutputs,List.length_map] using bound

end NearCompression
