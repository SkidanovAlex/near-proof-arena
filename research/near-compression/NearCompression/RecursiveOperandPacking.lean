import NearCompression.RecursiveOperandCoordinates
import NearCompression.DualMobiusWeights
import NearCompression.GenericPackingIdentity
import NearCompression.SparseLiftMLE
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Low row bits and high group bits, in the actual natural index order. -/
theorem recursive_operand_weight_split (n p row group : Nat) (point : Nat → K)
    (bound : row<2^n) :
    rowEqualityWeight (n+p) point (row+2^n*group)=
      rowEqualityWeight n point row*rowEqualityWeight p (fun i=>point (n+i)) group := by
  induction n generalizing row point with
  | zero =>
    have hr : row=0 := by simpa using bound
    simp only [hr,Nat.zero_add,Nat.pow_zero,Nat.one_mul,rowEqualityWeight]
    grind
  | succ n ih =>
    have hp : 2^(n+1)*group=2*(2^n*group) := by
      simp [Nat.pow_succ,Nat.mul_comm,Nat.mul_left_comm]
    have hm : (row+2^(n+1)*group)%2=row%2 := by rw [hp];omega
    have hd : (row+2^(n+1)*group)/2=row/2+2^n*group := by rw [hp];omega
    have hb : row/2<2^n := by rw [Nat.pow_succ] at bound;omega
    rw [Nat.succ_add,rowEqualityWeight,hm,hd,ih _ _ hb,rowEqualityWeight]
    have same : (fun i=>point (n+i+1))=(fun i=>point (n+1+i)) := by funext i;congr 1;omega
    rw [same]
    grind

theorem recursive_operand_zero_weight (n : Nat) (point : Nat → K) :
    rowEqualityWeight n point 0=lowZeroFactor n point := by
  induction n generalizing point with
  | zero => rfl
  | succ n ih => simp [rowEqualityWeight,lowZeroFactor,ih]

/-- All additional input bits are fixed to zero, never silently dropped. -/
theorem recursive_operand_weight_high_zero (n p h row group : Nat) (point : Nat → K)
    (hr : row<2^n) (hg : group<2^p) :
    rowEqualityWeight (n+(p+h)) point (row+2^n*group)=
      rowEqualityWeight n point row *
        (rowEqualityWeight p (fun i=>point (n+i)) group *
          lowZeroFactor h (fun i=>point (n+p+i))) := by
  rw [recursive_operand_weight_split n (p+h) row group point hr]
  have split := recursive_operand_weight_split p h group 0 (fun i=>point (n+i)) hg
  simp only [Nat.mul_zero,Nat.add_zero] at split
  rw [split,recursive_operand_zero_weight]
  have same : (fun i=>point (n+(p+i)))=(fun i=>point (n+p+i)) := by funext i;congr 1;omega
  rw [same]

private theorem zero_support_mle (n : Nat) (v : K) (point : Nat → K) :
    genericRowMLE n (fun i=>if i=0 then v else 0) point=lowZeroFactor n point*v := by
  induction n generalizing point with
  | zero => simp [genericRowMLE,lowZeroFactor];grind
  | succ n ih =>
    rw [genericRowMLE]
    have even : (fun i=>if 2*i=0 then v else (0:K))=(fun i=>if i=0 then v else 0) := by
      funext i
      have h : 2*i=0 ↔ i=0 := by omega
      simp only [h]
    have odd : (fun i=>if 2*i+1=0 then v else (0:K))=(fun _=>0) := by funext i;simp
    rw [even,odd,ih,generic_row_mle_zero]
    simp only [lowZeroFactor];grind

/-- Exact private envelope zero padding, valid even when a factor vanishes. -/
theorem recursive_operand_padded_mle (n h : Nat) (values point : Nat → K) :
    genericRowMLE (n+h) (fun i=>if i<2^n then values i else 0) point=
      lowZeroFactor h (fun i=>point (n+i))*genericRowMLE n values point := by
  rw [generic_row_mle_split_axes]
  have inner : (fun col=>genericRowMLE n (fun row=>if row+2^n*col<2^n then values (row+2^n*col) else 0) point)=
      (fun col=>if col=0 then genericRowMLE n values point else 0) := by
    funext col
    by_cases hc : col=0
    · subst col;simp only [Nat.mul_zero,Nat.add_zero,ite_true]
      apply generic_row_mle_congr
      intro row hr;simp only [hr,ite_true]
    · simp only [hc,ite_false]
      calc
        _ = genericRowMLE n (fun _=>0) point := by
          apply generic_row_mle_congr
          intro row _
          have ge : 2^n≤2^n*col := by simpa using Nat.mul_le_mul_left (2^n) (show 1≤col by omega)
          have hn : ¬row+2^n*col<2^n := by omega
          simp only [hn,ite_false]
        _ = 0 := generic_row_mle_zero n point
  rw [inner,zero_support_mle]

private theorem cube_scale_packing (n : Nat) (a : K) (v : Nat → K) :
    cubeSum n (fun i=>a*v i)=a*cubeSum n v := by
  unfold cubeSum
  generalize List.range (2^n)=xs
  induction xs with
  | nil => simp;grind
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih];grind

/-- Full input MLE equals the row MLEs with the branch group weights. -/
theorem recursive_operand_group_mle (n p h : Nat) (values point : Nat → K) :
    genericRowMLE ((n+p)+h) (fun i=>if i<2^(n+p) then values i else 0) point=
      cubeSum p (fun group=>
        (rowEqualityWeight p (fun i=>point (n+i)) group *
          lowZeroFactor h (fun i=>point (n+p+i))) *
        genericRowMLE n (fun row=>values (row+2^n*group)) point) := by
  rw [recursive_operand_padded_mle,generic_row_mle_split_axes,←row_equality_dot]
  rw [←cube_scale_packing]
  unfold cubeSum
  congr 1
  apply List.map_congr_left
  intro group _
  grind

/-- Actual 4096-row, four-group coordinate contribution; no inverse factors. -/
theorem recursive_operand_packed_slot (h row group : Nat) (point : Nat → Fp4)
    (scale : Fp4) (value : DiagnosticExt4) (hr : row<4096) (hg : group<4) :
    ((List.range 4).map (fun coordinate=>
      (((scale*(rowEqualityWeight 2 (fun i=>point (12+i)) group *
          lowZeroFactor h (fun i=>point (14+i)))) * rowEqualityWeight 12 point row) *
        recursiveOperandBasis coordinate) *
      diagnosticExt4Embed (diagnosticExt4Get value coordinate))).sum=
      (scale*rowEqualityWeight (12+(2+h)) point (row+4096*group))*
        diagnosticExt4ToTower value := by
  rw [recursive_operand_weighted]
  rw [recursive_operand_weight_high_zero 12 2 h row group point (by simpa using hr) (by simpa using hg)]
  grind

private theorem mle_list_sum_packing (indices : List Nat) (n : Nat)
    (values : Nat → Nat → K) (point : Nat → K) :
    genericRowMLE n (fun row=>(indices.map (fun i=>values i row)).sum) point=
      (indices.map (fun i=>genericRowMLE n (values i) point)).sum := by
  induction indices with
  | nil => simp only [List.map_nil,List.sum_nil];exact generic_row_mle_zero n point
  | cons i indices ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [generic_row_mle_add,ih]

/-- Four PCS base-coordinate column MLEs reconstruct the extension operand MLE. -/
theorem recursive_operand_column_functional (n : Nat) (values : Nat → DiagnosticExt4)
    (point : Nat → Fp4) (weight : Fp4) :
    ((List.range 4).map (fun coordinate=>(weight*recursiveOperandBasis coordinate)*
      genericRowMLE n (fun row=>diagnosticExt4Embed
        (diagnosticExt4Get (values row) coordinate)) point)).sum=
      weight*genericRowMLE n (fun row=>diagnosticExt4ToTower (values row)) point := by
  calc
    _ = ((List.range 4).map (fun coordinate=>genericRowMLE n
        (fun row=>(weight*recursiveOperandBasis coordinate)*
          diagnosticExt4Embed (diagnosticExt4Get (values row) coordinate)) point)).sum := by
      simp only [generic_row_mle_scale]
    _ = genericRowMLE n (fun row=>((List.range 4).map (fun coordinate=>
        (weight*recursiveOperandBasis coordinate)*
          diagnosticExt4Embed (diagnosticExt4Get (values row) coordinate))).sum) point :=
      (mle_list_sum_packing _ _ _ _).symm
    _ = _ := by simp only [recursive_operand_weighted,generic_row_mle_scale]

/-- Exact one-query branches functional: 16 base columns, four groups,
4096 rows, and any number of high zero-padding coordinates. Summing two
queries is then ordinary addition; no supplied whole-map equality is used. -/
theorem recursive_operand_branches_functional (h : Nat) (values : Nat → DiagnosticExt4)
    (point : Nat → Fp4) (scale : Fp4) :
    cubeSum 2 (fun group=>((List.range 4).map (fun coordinate=>
      ((scale*(rowEqualityWeight 2 (fun i=>point (12+i)) group *
        lowZeroFactor h (fun i=>point (14+i))))*recursiveOperandBasis coordinate)*
      genericRowMLE 12 (fun row=>diagnosticExt4Embed
        (diagnosticExt4Get (values (row+4096*group)) coordinate)) point)).sum)=
      scale*genericRowMLE (14+h)
        (fun i=>if i<16384 then diagnosticExt4ToTower (values i) else 0) point := by
  simp only [recursive_operand_column_functional]
  rw [recursive_operand_group_mle 12 2 h]
  rw [←cube_scale_packing]
  apply congrArg (cubeSum 2)
  funext group
  grind

end NearCompression
