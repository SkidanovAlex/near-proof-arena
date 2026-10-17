import NearCompression.AirCombinedResidualRows
import NearCompression.Ext8OperandPacking

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra

/-- One base-coordinate trace: source columns first, then eight consecutive
BabyBear columns per extension-valued auxiliary. Width is table-specific. -/
def airAuxCoordinateTrace (raw : Trace Fp) (sourceWidth : Nat→Nat) : Trace Fp8 where
  log:=raw.log
  cell:=fun t r c=>if c<sourceWidth t then Fp8.ofBase (raw.cell t r c) else
    Fp8.ofCoeffs (fun i=>raw.cell t r (sourceWidth t+8*(c-sourceWidth t)+i))

private theorem coordinate_mle (n : Nat) (coordinates : Nat→Nat→Fp) (point : Nat→Fp8) :
    ((List.range 8).map (fun i=>ext8OperandBasis i*
      genericRowMLE n (fun r=>Fp8.ofBase (coordinates r i)) point)).sum=
      genericRowMLE n (fun r=>Fp8.ofCoeffs (coordinates r)) point := by
  have h:=ext8_operand_column_functional n (fun r=>Fp8.ofCoeffs (coordinates r)) point 1
  have same : ((List.range 8).map (fun i=>(1*ext8OperandBasis i)*
      genericRowMLE n (fun r=>Fp8.ofBase (Fp8.coeff (Fp8.ofCoeffs (coordinates r)) i)) point))=
      (List.range 8).map (fun i=>ext8OperandBasis i*
        genericRowMLE n (fun r=>Fp8.ofBase (coordinates r i)) point) := by
    apply List.map_congr_left
    intro i hi
    simp only [Fp8.coeff_ofCoeffs _ i (List.mem_range.mp hi)]
    grind
  rw [same] at h
  grind

/-- Reconstruction applied to the PCS-authenticated coordinate MLEs, using
cyclic next rows before interpolation when next=true. -/
noncomputable def airAuxCoordinateInput (raw : Trace Fp) (sourceWidth : Nat→Nat)
    (t c : Nat) (next : Bool) (point : List Fp8) : Fp8 :=
  let atRow:=fun r=>if next then (r+1)%raw.height t else r
  if c<sourceWidth t then
    packedGridEval (raw.log t) (fun r=>Fp8.ofBase (raw.cell t (atRow r) c)) point
  else ((List.range 8).map (fun i=>ext8OperandBasis i*
    packedGridEval (raw.log t) (fun r=>Fp8.ofBase (raw.cell t (atRow r)
      (sourceWidth t+8*(c-sourceWidth t)+i))) point)).sum

/-- Coordinate reconstruction commutes with both current and cyclic-next
column interpolation, using exactly one explicitly constructed trace. -/
theorem air_aux_coordinate_column (raw : Trace Fp) (sourceWidth : Nat→Nat)
    (t c : Nat) (next : Bool) (point : List Fp8) :
    airAuxCoordinateInput raw sourceWidth t c next point=
      (airProductSelectorEnv (airAuxCoordinateTrace raw sourceWidth) t [] point).col c next := by
  unfold airAuxCoordinateInput airProductSelectorEnv airRowMLEEnv
  simp only [airAuxCoordinateTrace,Trace.height]
  by_cases source : c<sourceWidth t
  · simp only [source,ite_true]
  · simp only [source,ite_false]
    exact coordinate_mle (raw.log t)
      (fun r i=>raw.cell t (if next then (r+1)%(2^raw.log t) else r)
        (sourceWidth t+8*(c-sourceWidth t)+i)) (fun i=>point.getD i 0)

noncomputable def airAuxCoordinateEnv (raw : Trace Fp) (sourceWidth : Nat→Nat)
    (t : Nat) (point : List Fp8) : TerminalProgramEnvironment Fp8 where
  current:=fun c=>airAuxCoordinateInput raw sourceWidth t c false point
  next:=fun c=>airAuxCoordinateInput raw sourceWidth t c true point
  first:=(point.map (fun x=>1-x)).prod
  last:=point.prod
  transition:=1-point.prod

/-- The coordinate-opening environment is the formula model's environment
for the same reconstructed trace at every point. Authentication is separate. -/
theorem air_aux_coordinate_environment (raw : Trace Fp) (sourceWidth : Nat→Nat)
    (t : Nat) (point : List Fp8) :
    airAuxCoordinateEnv raw sourceWidth t point=
      busMLEProgramEnv (airAuxCoordinateTrace raw sourceWidth) t point := by
  unfold airAuxCoordinateEnv busMLEProgramEnv
  congr 1
  · funext c;exact air_aux_coordinate_column raw sourceWidth t c false point
  · funext c;exact air_aux_coordinate_column raw sourceWidth t c true point

/-- Auxiliary formulas on reconstructed coordinate inputs agree with direct
rows of the same semantic trace, not an independently supplied witness. -/
theorem air_aux_coordinate_formula_boolean (raw : Trace Fp) (sourceWidth : Nat→Nat)
    (t : Nat) (point : List Fp8) (length : point.length=raw.log t)
    (boolean : ∀ x∈point,x=0 ∨ x=1) (formula : BusProgramFormula Fp8) :
    busProgramFormulaValue (airAuxCoordinateEnv raw sourceWidth t point) formula=
      busProgramFormulaValue (busRowProgramEnv (airAuxCoordinateTrace raw sourceWidth) t
        (airBooleanIndex point)) formula := by
  rw [air_aux_coordinate_environment]
  exact bus_formula_boolean_row (airAuxCoordinateTrace raw sourceWidth) t point length boolean formula

/-- Source constraints cannot read reconstructed auxiliaries when their
checked column bound is within sourceWidth. Their values are exactly the
embedded original BabyBear evaluations on the common coordinate trace. -/
theorem air_aux_coordinate_source_eval (raw : Trace Fp) (sourceWidth : Nat→Nat)
    (t r : Nat) (pub : List Fp) (e : Expr) (bound : e.colBound≤sourceWidth t) :
    e.eval (airAuxCoordinateTrace raw sourceWidth) t r (pub.map Fp8.ofBase)=
      Fp8.ofBase (e.eval raw t r pub) := by
  have same : e.eval (airAuxCoordinateTrace raw sourceWidth) t r (pub.map Fp8.ofBase)=
      e.eval (airExt8Trace raw) t r (pub.map Fp8.ofBase) := by
    induction e with
    | const n => rfl
    | pub i => rfl
    | isFirst => rfl
    | isLast => rfl
    | isTransition => rfl
    | col c next =>
      have hc : c<sourceWidth t := by change c+1≤sourceWidth t at bound;omega
      simp [Expr.eval,Expr.evalWith,rowEnv,airAuxCoordinateTrace,airExt8Trace,Trace.height,hc]
    | add a b ha hb =>
      have ba : a.colBound≤sourceWidth t:=Nat.le_trans (Nat.le_max_left _ _) bound
      have bb : b.colBound≤sourceWidth t:=Nat.le_trans (Nat.le_max_right _ _) bound
      change _+_=_+_
      simp only [Expr.eval] at ha hb
      rw [ha ba,hb bb]
    | mul a b ha hb =>
      have ba : a.colBound≤sourceWidth t:=Nat.le_trans (Nat.le_max_left _ _) bound
      have bb : b.colBound≤sourceWidth t:=Nat.le_trans (Nat.le_max_right _ _) bound
      change _*_= _*_
      simp only [Expr.eval] at ha hb
      rw [ha ba,hb bb]
    | neg a ha => exact congrArg Neg.neg (ha bound)
  exact same.trans (air_expression_ext8_lift raw t r pub e)

end NearCompression
