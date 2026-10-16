import NearCompression.RecoveredSymbolicEnvironment
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra

structure TerminalEnvironmentAgreement {K : Type} (width : Nat)
    (left right : TerminalProgramEnvironment K) : Prop where
  current : ∀ c,c<width → left.current c=right.current c
  next : ∀ c,c<width → left.next c=right.next c
  first : left.first=right.first
  last : left.last=right.last
  transition : left.transition=right.transition

theorem air_expression_environment_transport {K : Type} [Field K] [DecidableEq K]
    (program : List (TerminalInstruction K)) (pubValues : List K) (width : Nat)
    (left right : TerminalProgramEnvironment K) (agree : TerminalEnvironmentAgreement width left right)
    (expr : Expr) (i : Nat) (checked : airExpressionCheck program pubValues width expr i=true) :
    expr.evalWith (airProgramEnv left pubValues)=expr.evalWith (airProgramEnv right pubValues) := by
  induction expr generalizing i with
  | const _ | pub _ => rfl
  | isFirst => exact agree.first
  | isLast => exact agree.last
  | isTransition => exact agree.transition
  | col c nx =>
    simp only [airExpressionCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
    cases nx
    · exact agree.current c checked.2.1
    · exact agree.next c checked.2.1
  | add a b ha hb =>
    simp only [airExpressionCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
    change a.evalWith _ + b.evalWith _ = a.evalWith _ + b.evalWith _
    rw [ha _ checked.2.1.2, hb _ checked.2.2]
  | mul a b ha hb =>
    simp only [airExpressionCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
    change a.evalWith _ * b.evalWith _ = a.evalWith _ * b.evalWith _
    rw [ha _ checked.2.1.2, hb _ checked.2.2]
  | neg a ha =>
    simp only [airExpressionCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
    exact congrArg Neg.neg (ha _ checked.2.2)

theorem bus_formula_environment_transport {K : Type} [Field K] [DecidableEq K]
    (program : List (TerminalInstruction K)) (width : Nat)
    (left right : TerminalProgramEnvironment K) (agree : TerminalEnvironmentAgreement width left right)
    (formula : BusProgramFormula K) (i : Nat) (checked : busFormulaCheck program width formula i=true) :
    busProgramFormulaValue left formula=busProgramFormulaValue right formula := by
  induction formula generalizing i with
  | literal _ => rfl
  | first => exact agree.first
  | last => exact agree.last
  | transition => exact agree.transition
  | current c =>
    simp only [busFormulaCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
    exact agree.current c checked.2.1
  | next c =>
    simp only [busFormulaCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
    exact agree.next c checked.2.1
  | add a b ha hb | sub a b ha hb | mul a b ha hb =>
    simp only [busFormulaCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
    simp only [busProgramFormulaValue,ha _ checked.2.1.2,hb _ checked.2.2]

theorem mixed_formula_environment_transport {K : Type} [Field K] [DecidableEq K]
    (program : List (TerminalInstruction K)) (pubValues : List K) (width : Nat)
    (left right : TerminalProgramEnvironment K) (agree : TerminalEnvironmentAgreement width left right)
    (formula : AIRBusResidual K) (i : Nat) (checked : airBusResidualCheck program pubValues width formula i=true) :
    airBusResidualValue left pubValues formula=airBusResidualValue right pubValues formula := by
  cases formula with
  | inl expr => exact air_expression_environment_transport program pubValues width left right agree expr i checked
  | inr formula => exact bus_formula_environment_transport program width left right agree formula i checked

theorem mixed_sum_environment_transport {K : Type} [Field K] [DecidableEq K]
    (program : List (TerminalInstruction K)) (pubValues : List K) (width : Nat)
    (left right : TerminalProgramEnvironment K) (agree : TerminalEnvironmentAgreement width left right)
    (mixing power : K) (residuals : List (AIRBusResidual K × Nat))
    (checked : residuals.all (fun r => airBusResidualCheck program pubValues width r.1 r.2)=true) :
    airBusMixValue left pubValues mixing power residuals=airBusMixValue right pubValues mixing power residuals := by
  induction residuals generalizing power with
  | nil => rfl
  | cons r rest ih =>
    simp only [List.all_cons,Bool.and_eq_true] at checked
    simp only [airBusMixValue]
    rw [mixed_formula_environment_transport program pubValues width left right agree r.1 r.2 checked.1,
      ih (power*mixing) checked.2]

def decodedColumnEnvironment {K : Type} [Field K] (table : GKRTableMetadata)
    (placement : TerminalSymbolicPlacement K) (decoded : Nat → Nat → K)
    (rowpoints : GKRSourceLane → Nat → K) : TerminalProgramEnvironment K :=
  ⟨(fun c => genericRowMLE table.rowLog (decoded c) (rowpoints (metadataColumnLane table c))),
   (fun c => genericRowNextMLE table.rowLog (decoded c) (rowpoints (metadataColumnLane table c))),
   placement.first,placement.last,placement.transition⟩

/-- Construct the bounded agreement needed by expression and bus transport.
The decoded columns and their provenance precede all rowpoint choices. -/
theorem recovered_decoded_environment_agreement {K : Type} [Field K]
    (C : Nat) (metadata : List GKRTableMetadata) (entries : List (GKRSourceLane × Poly K))
    (canonical : entries.map Prod.fst=metadata.flatMap gkrMetadataLanes)
    (disjoint : AllLaneSupportsDisjoint (entries.map Prod.fst))
    (table : GKRTableMetadata) (member : table∈metadata) (placement : TerminalSymbolicPlacement K)
    (placed : symbolicPlacementMetadataCheck placement table=true) :
    ∃ decoded : Nat → Nat → K,
      (∀ column,column<table.sourceWidth+table.auxiliaryWidth →
        ∃ polynomial : Poly K,(metadataColumnLane table column,polynomial)∈entries ∧
          decoded column=recoveredColumnValues C (metadataColumnLane table column) (metadataColumnOffset table column) polynomial) ∧
      ∀ rowpoints : GKRSourceLane → Nat → K,
        TerminalEnvironmentAgreement (table.sourceWidth+table.auxiliaryWidth)
          (placement.environment (gkrScatter (recoveredPrivateSlots C entries rowpoints)))
          (decodedColumnEnvironment table placement decoded rowpoints) := by
  obtain ⟨decoded,provenance,reads⟩ := recovered_symbolic_environment C metadata entries canonical disjoint table member placement placed
  refine ⟨decoded,provenance,?_⟩
  intro rowpoints
  refine ⟨?_,?_,rfl,rfl,rfl⟩
  · intro c hc
    exact reads c hc rowpoints false
  · intro c hc
    exact reads c hc rowpoints true

/-- The same fixed decoded table supports any later checked formula list,
public values, mixing and rowpoints. No environment equality is a premise. -/
theorem recovered_mixed_formula_transport {K : Type} [Field K] [DecidableEq K]
    (C : Nat) (metadata : List GKRTableMetadata) (entries : List (GKRSourceLane × Poly K))
    (canonical : entries.map Prod.fst=metadata.flatMap gkrMetadataLanes)
    (disjoint : AllLaneSupportsDisjoint (entries.map Prod.fst))
    (table : GKRTableMetadata) (member : table∈metadata) (placement : TerminalSymbolicPlacement K)
    (placed : symbolicPlacementMetadataCheck placement table=true) :
    ∃ decoded : Nat → Nat → K,
      (∀ column,column<table.sourceWidth+table.auxiliaryWidth →
        ∃ polynomial : Poly K,(metadataColumnLane table column,polynomial)∈entries ∧
          decoded column=recoveredColumnValues C (metadataColumnLane table column) (metadataColumnOffset table column) polynomial) ∧
      ∀ rowpoints : GKRSourceLane → Nat → K,∀ program : List (TerminalInstruction K),
      ∀ pubValues : List K,∀ width : Nat,∀ mixing power : K,∀ residuals : List (AIRBusResidual K × Nat),
      width≤table.sourceWidth+table.auxiliaryWidth →
      residuals.all (fun r => airBusResidualCheck program pubValues width r.1 r.2)=true →
      airBusMixValue (placement.environment (gkrScatter (recoveredPrivateSlots C entries rowpoints)))
        pubValues mixing power residuals=
      airBusMixValue (decodedColumnEnvironment table placement decoded rowpoints) pubValues mixing power residuals := by
  obtain ⟨decoded,provenance,agree⟩ := recovered_decoded_environment_agreement C metadata entries canonical disjoint table member placement placed
  refine ⟨decoded,provenance,?_⟩
  intro rowpoints program pubValues width mixing power residuals bound checked
  have full := agree rowpoints
  have narrow : TerminalEnvironmentAgreement width _ _ :=
    ⟨(fun c hc => full.current c (by omega)),(fun c hc => full.next c (by omega)),
      full.first,full.last,full.transition⟩
  exact mixed_sum_environment_transport program pubValues width _ _ narrow mixing power residuals checked

private def transportLeft : TerminalProgramEnvironment Rat :=
  ⟨(fun c => if c=0 then 2 else 11),(fun c => if c=0 then 3 else 13),1,0,1⟩
private def transportRight : TerminalProgramEnvironment Rat :=
  ⟨(fun c => if c=0 then 2 else 17),(fun c => if c=0 then 3 else 19),1,0,1⟩

/-- Agreement is deliberately bounded: unused columns may differ, but the
checker rejects a formula that tries to read them. Swapping current/next or
changing a selector changes evaluation. -/
theorem formula_environment_transport_regressions :
    TerminalEnvironmentAgreement 1 transportLeft transportRight ∧
    transportLeft.current 1 ≠ transportRight.current 1 ∧
    transportLeft.next 1 ≠ transportRight.next 1 ∧
    busFormulaCheck [⟨.current,1,0,(0:Rat)⟩] 1 (.current 1) 0=false ∧
    airExpressionCheck [⟨.next,1,0,(0:Rat)⟩] [] 1 (.col 1 true) 0=false ∧
    busProgramFormulaValue transportLeft (.sub (.next 0) (.current 0))=1 ∧
    busProgramFormulaValue transportLeft (.sub (.current 0) (.next 0))=(-1) ∧
    busProgramFormulaValue transportLeft .first ≠
      busProgramFormulaValue {transportRight with first := 0} .first := by
  constructor
  · refine ⟨?_,?_,rfl,rfl,rfl⟩
    · intro c hc
      have : c=0 := by omega
      subst c
      rfl
    · intro c hc
      have : c=0 := by omega
      subst c
      rfl
  · decide +kernel

end NearCompression
