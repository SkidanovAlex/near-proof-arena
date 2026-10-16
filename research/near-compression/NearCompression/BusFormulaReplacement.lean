import NearCompression.GeneratedExt8BusSpecCheck
import NearCompression.ExpandedBusFingerprint
namespace NearCompression
open Lean.Grind

/-- Replace exact subexpressions, retaining all surrounding operations. -/
def replaceBusFormula {K : Type} [DecidableEq K]
    (before after : BusProgramFormula K) (formula : BusProgramFormula K) : BusProgramFormula K :=
  if formula=before then after else
    match formula with
    | .add a b => .add (replaceBusFormula before after a) (replaceBusFormula before after b)
    | .sub a b => .sub (replaceBusFormula before after a) (replaceBusFormula before after b)
    | .mul a b => .mul (replaceBusFormula before after a) (replaceBusFormula before after b)
    | leaf => leaf

/-- A value-preserving replacement stays valid in arbitrary residual contexts. -/
theorem replace_bus_formula_value {K : Type} [Field K] [DecidableEq K]
    (env : TerminalProgramEnvironment K) (before after formula : BusProgramFormula K)
    (same : busProgramFormulaValue env after=busProgramFormulaValue env before) :
    busProgramFormulaValue env (replaceBusFormula before after formula)=busProgramFormulaValue env formula := by
  induction formula with
  | add a b ha hb =>
    by_cases h : BusProgramFormula.add a b=before
    · simp only [replaceBusFormula,ite_eq_left h]; exact same.trans (congrArg (busProgramFormulaValue env) h.symm)
    · simp only [replaceBusFormula,ite_eq_right h,busProgramFormulaValue,ha,hb]
  | sub a b ha hb =>
    by_cases h : BusProgramFormula.sub a b=before
    · simp only [replaceBusFormula,ite_eq_left h]; exact same.trans (congrArg (busProgramFormulaValue env) h.symm)
    · simp only [replaceBusFormula,ite_eq_right h,busProgramFormulaValue,ha,hb]
  | mul a b ha hb =>
    by_cases h : BusProgramFormula.mul a b=before
    · simp only [replaceBusFormula,ite_eq_left h]; exact same.trans (congrArg (busProgramFormulaValue env) h.symm)
    · simp only [replaceBusFormula,ite_eq_right h,busProgramFormulaValue,ha,hb]
  | literal x | current x | next x =>
    simp only [replaceBusFormula]; split
    · rename_i h; exact same.trans (congrArg (busProgramFormulaValue env) h.symm)
    · rfl
  | first | last | transition =>
    simp only [replaceBusFormula]; split
    · rename_i h; exact same.trans (congrArg (busProgramFormulaValue env) h.symm)
    · rfl

/-- Expand one tagged fingerprint wherever it occurs in a residual. -/
def expandBusFingerprintIn {K : Type} [Field K] [DecidableEq K]
    (alpha tag : K) (message : List (BusProgramFormula K)) (formula : BusProgramFormula K) :=
  replaceBusFormula (busTaggedFormula alpha tag message)
    (expandedBusTagged alpha tag 1 (.literal 0) message) formula

theorem expand_bus_fingerprint_in_value {K : Type} [Field K] [DecidableEq K]
    (env : TerminalProgramEnvironment K) (alpha tag : K)
    (message : List (BusProgramFormula K)) (formula : BusProgramFormula K) :
    busProgramFormulaValue env (expandBusFingerprintIn alpha tag message formula)=busProgramFormulaValue env formula :=
  replace_bus_formula_value env _ _ formula (expanded_bus_fingerprint_value env alpha tag message)

/-- Each bus residual contains at most one interaction's fingerprint. Unchanged
residuals and exact context replacements are both accepted. -/
def busExpandedFormulaCheck {K : Type} [Field K] [DecidableEq K]
    (alpha : K) (messages : List (K × List (BusProgramFormula K)))
    (canonical actual : BusProgramFormula K) : Bool :=
  decide (actual=canonical) || messages.any (fun m=>
    decide (actual=expandBusFingerprintIn alpha m.1 m.2 canonical))

theorem bus_expanded_formula_checked {K : Type} [Field K] [DecidableEq K]
    (env : TerminalProgramEnvironment K) (alpha : K)
    (messages : List (K × List (BusProgramFormula K))) (canonical actual : BusProgramFormula K)
    (checked : busExpandedFormulaCheck alpha messages canonical actual=true) :
    busProgramFormulaValue env actual=busProgramFormulaValue env canonical := by
  simp only [busExpandedFormulaCheck,Bool.or_eq_true,decide_eq_true_eq,List.any_eq_true] at checked
  rcases checked with same | ⟨m,_,same⟩
  · rw [same]
  · rw [same]
    exact expand_bus_fingerprint_in_value env alpha m.1 m.2 canonical

def busExpandedListCheck {K : Type} [Field K] [DecidableEq K]
    (alpha : K) (messages : List (K × List (BusProgramFormula K))) :
    List (BusProgramFormula K) → List (BusProgramFormula K) → Bool
  | [],[] => true
  | c::cs,a::as => busExpandedFormulaCheck alpha messages c a && busExpandedListCheck alpha messages cs as
  | _,_ => false

theorem bus_expanded_list_checked {K : Type} [Field K] [DecidableEq K]
    (env : TerminalProgramEnvironment K) (alpha : K)
    (messages : List (K × List (BusProgramFormula K))) (canonical actual : List (BusProgramFormula K))
    (checked : busExpandedListCheck alpha messages canonical actual=true) :
    actual.map (busProgramFormulaValue env)=canonical.map (busProgramFormulaValue env) := by
  induction canonical generalizing actual with
  | nil => cases actual with
    | nil => rfl
    | cons a as => simp [busExpandedListCheck] at checked
  | cons c cs ih => cases actual with
    | nil => simp [busExpandedListCheck] at checked
    | cons a as =>
      simp only [busExpandedListCheck,Bool.and_eq_true] at checked
      simp only [List.map_cons,bus_expanded_formula_checked env alpha messages c a checked.1,ih as checked.2]

/-- Ordered expanded residual checks retain the existing decoded-coordinate
specification semantics. Authentication and coordinate typing are unchanged. -/
theorem generated_expanded_bus_spec_checked
    (env : TerminalProgramEnvironment ZkFormal.Algebra.Fp8)
    (interactions : List (BusFormulaInteraction ZkFormal.Algebra.Fp8))
    (width : Nat) (finals : Nat → ZkFormal.Algebra.Fp8)
    (alpha : ZkFormal.Algebra.Fp8)
    (messages : List (ZkFormal.Algebra.Fp8 × List (BusProgramFormula ZkFormal.Algebra.Fp8)))
    (actual : List (BusProgramFormula ZkFormal.Algebra.Fp8))
    (checked : busExpandedListCheck alpha messages (generatedExt8BusSpec interactions width finals) actual=true) :
    actual.map (busProgramFormulaValue env)=
      (busTableResiduals interactions width finals).map
        (busProgramFormulaValue (busCoordinateEnvironment width env)) := by
  rw [bus_expanded_list_checked env alpha messages _ actual checked]
  exact generated_ext8_bus_spec_checked interactions width finals _ (by simp [generatedExt8BusSpecCheck]) env

end NearCompression
