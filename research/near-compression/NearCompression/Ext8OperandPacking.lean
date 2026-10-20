import NearCompression.RecursiveOperandPacking
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

/-- Certified Fp8 flat basis, in the same order as the executable adapter. -/
def ext8OperandBasis (i : Nat) : Fp8 := Fp8.ofCoeffs (fun j=>if j=i then 1 else 0)

theorem ext8_operand_reconstruct (a : Fp8) :
    ((List.range 8).map (fun i=>Fp8.ofBase (Fp8.coeff a i)*ext8OperandBasis i)).sum=a := by
  simp only [←Fp8.smulBase_eq]
  apply Fp8.ext <;>
    simp [List.range_succ,ext8OperandBasis,Fp8.ofCoeffs,Fp8.coeff,Fp8.smulBase,show (0:Fp8)=Fp8.ofBase 0 from rfl,Fp8.ofBase] <;> grind

private theorem scale_sum (xs : List Fp8) (w : Fp8) :
    (xs.map (fun x=>w*x)).sum=w*xs.sum := by
  induction xs with
  | nil=>simp only [List.map_nil,List.sum_nil];grind
  | cons x xs ih=>simp only [List.map_cons,List.sum_cons,ih];grind

theorem ext8_operand_weighted (a w : Fp8) :
    ((List.range 8).map (fun i=>(w*ext8OperandBasis i)*Fp8.ofBase (Fp8.coeff a i))).sum=w*a := by
  have same : (fun i=>(w*ext8OperandBasis i)*Fp8.ofBase (Fp8.coeff a i))=
      (fun i=>w*(Fp8.ofBase (Fp8.coeff a i)*ext8OperandBasis i)) := by funext i;grind
  rw [same]
  calc
    _ = w*((List.range 8).map (fun i=>Fp8.ofBase (Fp8.coeff a i)*ext8OperandBasis i)).sum := by
      simpa only [List.map_map,Function.comp_def] using
        scale_sum ((List.range 8).map (fun i=>Fp8.ofBase (Fp8.coeff a i)*ext8OperandBasis i)) w
    _ = w*a := by rw [ext8_operand_reconstruct]

private theorem mle_sum (indices : List Nat) (n : Nat)
    (values : Nat→Nat→Fp8) (point : Nat→Fp8) :
    genericRowMLE n (fun row=>(indices.map (fun i=>values i row)).sum) point=
      (indices.map (fun i=>genericRowMLE n (values i) point)).sum := by
  induction indices with
  | nil=>simp only [List.map_nil,List.sum_nil];exact generic_row_mle_zero n point
  | cons i indices ih=>simp only [List.map_cons,List.sum_cons];rw [generic_row_mle_add,ih]

/-- Eight base-coordinate column MLEs equal the weighted Ext8 operand MLE. -/
theorem ext8_operand_column_functional (n : Nat) (values point : Nat→Fp8) (weight : Fp8) :
    ((List.range 8).map (fun i=>(weight*ext8OperandBasis i)*
      genericRowMLE n (fun row=>Fp8.ofBase (Fp8.coeff (values row) i)) point)).sum=
      weight*genericRowMLE n values point := by
  calc
    _ = ((List.range 8).map (fun i=>genericRowMLE n
      (fun row=>(weight*ext8OperandBasis i)*Fp8.ofBase (Fp8.coeff (values row) i)) point)).sum := by
        simp only [generic_row_mle_scale]
    _ = genericRowMLE n (fun row=>((List.range 8).map
      (fun i=>(weight*ext8OperandBasis i)*Fp8.ofBase (Fp8.coeff (values row) i))).sum) point :=
        (mle_sum _ _ _ _).symm
    _ = _ := by simp only [ext8_operand_weighted,generic_row_mle_scale]

private theorem cube_scale (n : Nat) (w : Fp8) (values : Nat→Fp8) :
    cubeSum n (fun i=>w*values i)=w*cubeSum n values := by
  unfold cubeSum
  generalize List.range (2^n)=xs
  simpa only [List.map_map,Function.comp_def] using scale_sum (xs.map values) w

/-- General row/group split with eight coordinate columns per group. Padding
bits retain their zero-coordinate factors. This is algebra, not PCS binding. -/
theorem ext8_operand_branches_functional (n p h : Nat) (values point : Nat→Fp8) (scale : Fp8) :
    cubeSum p (fun group=>((List.range 8).map (fun coordinate=>
      ((scale*(rowEqualityWeight p (fun i=>point (n+i)) group *
        lowZeroFactor h (fun i=>point (n+p+i))))*ext8OperandBasis coordinate)*
      genericRowMLE n (fun row=>Fp8.ofBase (Fp8.coeff (values (row+2^n*group)) coordinate)) point)).sum)=
      scale*genericRowMLE ((n+p)+h)
        (fun i=>if i<2^(n+p) then values i else 0) point := by
  simp only [ext8_operand_column_functional]
  rw [recursive_operand_group_mle n p h,←cube_scale]
  apply congrArg (cubeSum p)
  funext group
  grind
end NearCompression
