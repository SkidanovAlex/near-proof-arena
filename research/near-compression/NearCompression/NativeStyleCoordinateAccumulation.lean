import NearCompression.BusCoordinateCoverage
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

/-- Model the native loop: start from zero and append coordinate*basis terms.
This is an Ext8 candidate model, not an assertion that native Ext4 code is Ext8. -/
def nativeStyleCoordinateColumn (width column : Nat) (next : Bool) : BusProgramFormula Fp8 :=
  let read := fun c=>if next then BusProgramFormula.next c else .current c
  if column<width then read column else
    ((List.range 8).map (fun i=>
      .mul (read (width+8*(column-width)+i)) (.literal (ext8OperandBasis i)))).foldl
      BusProgramFormula.add (.literal 0)

theorem bus_formula_foldl_value (env : TerminalProgramEnvironment Fp8)
    (xs : List (BusProgramFormula Fp8)) (initial : BusProgramFormula Fp8) :
    busProgramFormulaValue env (xs.foldl BusProgramFormula.add initial)=
      busProgramFormulaValue env initial+(xs.map (busProgramFormulaValue env)).sum := by
  induction xs generalizing initial with
  | nil => simp only [List.foldl_nil,List.map_nil,List.sum_nil];grind
  | cons x xs ih =>
    simp only [List.foldl_cons,ih,busProgramFormulaValue,List.map_cons,List.sum_cons]
    grind

/-- Association and multiplication order differ, but evaluation agrees for
all environments, not just honest witness values. -/
theorem native_style_coordinate_value (width column : Nat) (next : Bool)
    (env : TerminalProgramEnvironment Fp8) :
    busProgramFormulaValue env (nativeStyleCoordinateColumn width column next)=
      busProgramFormulaValue env (busCoordinateColumnFormula width column next) := by
  by_cases hc : column<width
  · simp only [nativeStyleCoordinateColumn,busCoordinateColumnFormula,hc,ite_true]
  · simp only [nativeStyleCoordinateColumn,busCoordinateColumnFormula,hc,ite_false,
      bus_formula_foldl_value,bus_formula_sum_value,List.map_map,Function.comp_def,busProgramFormulaValue]
    have same : ((List.range 8).map (fun i=>
        busProgramFormulaValue env (if next then BusProgramFormula.next (width+8*(column-width)+i) else .current (width+8*(column-width)+i))*ext8OperandBasis i))=
      (List.range 8).map (fun i=>ext8OperandBasis i*
        busProgramFormulaValue env (if next then BusProgramFormula.next (width+8*(column-width)+i) else .current (width+8*(column-width)+i))) := by
      apply List.map_congr_left
      intro i hi
      grind
    rw [same]
    grind

theorem bus_formula_foldl_bounds (xs : List (BusProgramFormula Fp8))
    (initial : BusProgramFormula Fp8) (degree width : Nat)
    (initialBounds : busFormulaDegree initial≤degree ∧ busFormulaColumnBound initial≤width)
    (bounds : ∀ e∈xs,busFormulaDegree e≤degree ∧ busFormulaColumnBound e≤width) :
    busFormulaDegree (xs.foldl BusProgramFormula.add initial)≤degree ∧
      busFormulaColumnBound (xs.foldl BusProgramFormula.add initial)≤width := by
  induction xs generalizing initial with
  | nil => exact initialBounds
  | cons x xs ih =>
    apply ih (.add initial x)
    · have h := bounds x (by simp)
      exact ⟨Nat.max_le.mpr ⟨initialBounds.1,h.1⟩,Nat.max_le.mpr ⟨initialBounds.2,h.2⟩⟩
    · exact fun e he=>bounds e (by simp [he])

theorem native_style_coordinate_bounds (width auxiliaries column : Nat) (next : Bool)
    (bound : column<width+auxiliaries) :
    busFormulaDegree (nativeStyleCoordinateColumn width column next)≤1 ∧
      busFormulaColumnBound (nativeStyleCoordinateColumn width column next)≤width+8*auxiliaries := by
  by_cases hc : column<width
  · cases next <;> simp only [nativeStyleCoordinateColumn,hc,ite_true,Bool.false_eq_true,ite_false,
      busFormulaDegree,busFormulaColumnBound] <;> omega
  · simp only [nativeStyleCoordinateColumn,hc,ite_false]
    apply bus_formula_foldl_bounds
    · exact ⟨Nat.zero_le _,Nat.zero_le _⟩
    · intro e he
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
      have ib := List.mem_range.mp hi
      cases next <;> simp only [Bool.false_eq_true,ite_false,ite_true,busFormulaDegree,busFormulaColumnBound] <;> omega

def lowerNativeStyleCoordinates (width : Nat) : BusProgramFormula Fp8 → BusProgramFormula Fp8
  | .literal x => .literal x
  | .current c => nativeStyleCoordinateColumn width c false
  | .next c => nativeStyleCoordinateColumn width c true
  | .first => .first | .last => .last | .transition => .transition
  | .add a b => .add (lowerNativeStyleCoordinates width a) (lowerNativeStyleCoordinates width b)
  | .sub a b => .sub (lowerNativeStyleCoordinates width a) (lowerNativeStyleCoordinates width b)
  | .mul a b => .mul (lowerNativeStyleCoordinates width a) (lowerNativeStyleCoordinates width b)

theorem native_style_lowering_value (width : Nat) (env : TerminalProgramEnvironment Fp8)
    (e : BusProgramFormula Fp8) :
    busProgramFormulaValue env (lowerNativeStyleCoordinates width e)=
      busProgramFormulaValue env (lowerBusCoordinates width e) := by
  induction e with
  | literal x | first | last | transition => rfl
  | current c => exact native_style_coordinate_value width c false env
  | next c => exact native_style_coordinate_value width c true env
  | add a b ha hb | sub a b ha hb | mul a b ha hb =>
    simp only [lowerNativeStyleCoordinates,lowerBusCoordinates,busProgramFormulaValue,ha,hb]

theorem native_style_lowering_bounds (width auxiliaries : Nat) (e : BusProgramFormula Fp8)
    (bound : busFormulaColumnBound e≤width+auxiliaries) :
    busFormulaDegree (lowerNativeStyleCoordinates width e)≤busFormulaDegree e ∧
      busFormulaColumnBound (lowerNativeStyleCoordinates width e)≤width+8*auxiliaries := by
  induction e with
  | literal x | first | last | transition => exact ⟨Nat.le_refl _,Nat.zero_le _⟩
  | current c => exact native_style_coordinate_bounds width auxiliaries c false (by change c+1≤_ at bound;omega)
  | next c => exact native_style_coordinate_bounds width auxiliaries c true (by change c+1≤_ at bound;omega)
  | add a b ha hb | sub a b ha hb =>
    have left := ha (Nat.le_trans (Nat.le_max_left _ _) bound)
    have right := hb (Nat.le_trans (Nat.le_max_right _ _) bound)
    exact ⟨Nat.max_le.mpr ⟨Nat.le_trans left.1 (Nat.le_max_left _ _),Nat.le_trans right.1 (Nat.le_max_right _ _)⟩,
      Nat.max_le.mpr ⟨left.2,right.2⟩⟩
  | mul a b ha hb =>
    have left := ha (Nat.le_trans (Nat.le_max_left _ _) bound)
    have right := hb (Nat.le_trans (Nat.le_max_right _ _) bound)
    exact ⟨Nat.add_le_add left.1 right.1,Nat.max_le.mpr ⟨left.2,right.2⟩⟩

end NearCompression
