import NearCompression.BusSourceFormulaLowering
import NearCompression.BoundedBusCoordinateTyping
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

/-- Expand a tagged Horner message into public scalar-weighted summands.
The accumulator matches the compiler generator's left-to-right construction;
the existing DAG balancing pass can balance its additive chain. -/
def expandedBusTagged (alpha tag weight : K) (acc : BusProgramFormula K) :
    List (BusProgramFormula K) → BusProgramFormula K
  | [] => .add acc (.literal (tag*weight))
  | x::xs => expandedBusTagged alpha tag (weight*alpha)
      (.add acc (.mul x (.literal weight))) xs

/-- Public-weight expansion preserves values for every environment, including
zero challenges and arbitrary extension-valued input coordinates. -/
theorem expanded_bus_tagged_value (env : TerminalProgramEnvironment K)
    (alpha tag weight : K) (acc : BusProgramFormula K) (message : List (BusProgramFormula K)) :
    busProgramFormulaValue env (expandedBusTagged alpha tag weight acc message)=
      busProgramFormulaValue env acc+weight*busProgramFormulaValue env (busTaggedFormula alpha tag message) := by
  induction message generalizing weight acc with
  | nil => simp only [expandedBusTagged,busTaggedFormula,busProgramFormulaValue];grind
  | cons x xs ih =>
    simp only [expandedBusTagged,ih,busTaggedFormula,busProgramFormulaValue]
    grind

/-- Starting with zero and unit weight gives the exact canonical fingerprint. -/
theorem expanded_bus_fingerprint_value (env : TerminalProgramEnvironment K)
    (alpha tag : K) (message : List (BusProgramFormula K)) :
    busProgramFormulaValue env (expandedBusTagged alpha tag 1 (.literal 0) message)=
      busProgramFormulaValue env (busTaggedFormula alpha tag message) := by
  rw [expanded_bus_tagged_value]
  simp only [busProgramFormulaValue]
  grind

/-- Expanding public constants introduces no additional local degree. -/
theorem expanded_bus_tagged_degree (alpha tag weight : K) (acc : BusProgramFormula K)
    (message : List (BusProgramFormula K)) (d : Nat)
    (accBound : busFormulaDegree acc≤d) (bounds : ∀ e∈message,busFormulaDegree e≤d) :
    busFormulaDegree (expandedBusTagged alpha tag weight acc message)≤d := by
  induction message generalizing weight acc with
  | nil => simpa only [expandedBusTagged,busFormulaDegree,Nat.max_zero] using accBound
  | cons x xs ih =>
    apply ih (weight*alpha) (.add acc (.mul x (.literal weight)))
    · simpa only [busFormulaDegree,Nat.add_zero] using Nat.max_le.mpr ⟨accBound,bounds x (by simp)⟩
    · intro e he;exact bounds e (List.mem_cons_of_mem _ he)

/-- Public-weight expansion reads only the original message/accumulator columns. -/
theorem expanded_bus_tagged_columns (alpha tag weight : K) (acc : BusProgramFormula K)
    (message : List (BusProgramFormula K)) (width : Nat)
    (accBound : busFormulaColumnBound acc≤width) (bounds : ∀ e∈message,busFormulaColumnBound e≤width) :
    busFormulaColumnBound (expandedBusTagged alpha tag weight acc message)≤width := by
  induction message generalizing weight acc with
  | nil => simpa only [expandedBusTagged,busFormulaColumnBound,Nat.max_zero] using accBound
  | cons x xs ih =>
    apply ih (weight*alpha) (.add acc (.mul x (.literal weight)))
    · simpa only [busFormulaColumnBound,Nat.max_zero] using Nat.max_le.mpr ⟨accBound,bounds x (by simp)⟩
    · intro e he;exact bounds e (List.mem_cons_of_mem _ he)

end NearCompression
