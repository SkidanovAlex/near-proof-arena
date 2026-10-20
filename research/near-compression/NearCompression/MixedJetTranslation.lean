import NearCompression.JetCoefficientMatrix

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Synthetic jets of the Horner constructor, in positive order. -/
theorem synthetic_jet_cons_succ (c : K) (cs : List K) (a : K) (r : Nat) :
    syntheticJet (Poly.mk (c::cs)) a (r+1)=
      syntheticJet (Poly.mk cs) a r+a*syntheticJet (Poly.mk cs) a (r+1) := by
  change syntheticJet ((Poly.mk cs)+Poly.smul a ((Poly.mk cs).quot a)) a r=_
  rw [synthetic_jet_add,synthetic_jet_scale]
  rfl

private theorem zero_coeff (i : Nat) : (Poly.zero : Poly K).coeff i=0 := by
  simp [Poly.zero,Poly.coeff]

private theorem zero_jet (a : K) (i : Nat) : syntheticJet (Poly.zero : Poly K) a i=0 := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih

private theorem add_rows_coefficient (xs ys : List (Poly K)) (i j : Nat) :
    ((bivariateAddRows xs ys).getD j Poly.zero).coeff i=
      (xs.getD j Poly.zero).coeff i+(ys.getD j Poly.zero).coeff i := by
  induction xs generalizing ys j with
  | nil => simp only [bivariateAddRows,List.getD_nil,zero_coeff];grind
  | cons x xs ih =>
    cases ys with
    | nil => simp only [bivariateAddRows,List.getD_nil,zero_coeff];grind
    | cons y ys =>
      cases j with
      | zero => exact Poly.coeff_add x y i
      | succ j => exact ih ys j

private theorem scale_rows_coefficient (rows : List (Poly K)) (b : K) (i j : Nat) :
    ((rows.map (Poly.smul b)).getD j Poly.zero).coeff i=b*(rows.getD j Poly.zero).coeff i := by
  induction rows generalizing j with
  | nil => simp only [List.map_nil,List.getD_nil,zero_coeff];grind
  | cons row rest ih =>
    cases j with
    | zero => exact Poly.coeff_smul b row i
    | succ j => exact ih j

/-- Row-Horner translation in Y has exactly the successive-quotient jets of
the coefficient polynomial. No field-size or distinct evaluation-domain guard. -/
theorem bivariate_translate_y_coefficient (rows : List (Poly K)) (b : K) (i j : Nat) :
    ((bivariateTranslateY rows b).getD j Poly.zero).coeff i=
      syntheticJet (Poly.mk (rows.map (fun row=>row.coeff i))) b j := by
  induction rows generalizing j with
  | nil =>
    change (Poly.zero : Poly K).coeff i=syntheticJet Poly.zero b j
    rw [zero_coeff,zero_jet]
  | cons row rest ih =>
    simp only [bivariateTranslateY,add_rows_coefficient,scale_rows_coefficient]
    cases j with
    | zero =>
      change row.coeff i+(b*((bivariateTranslateY rest b).getD 0 Poly.zero).coeff i+(Poly.zero.coeff i))=
        (Poly.mk (row.coeff i::rest.map (fun p=>p.coeff i))).eval b
      rw [ih,zero_coeff]
      change row.coeff i+(b*(Poly.mk (rest.map (fun p=>p.coeff i))).eval b+0)=
        row.coeff i+b*(Poly.mk (rest.map (fun p=>p.coeff i))).eval b
      grind
    | succ j =>
      change (Poly.zero.coeff i)+(b*((bivariateTranslateY rest b).getD (j+1) Poly.zero).coeff i+
        ((bivariateTranslateY rest b).getD j Poly.zero).coeff i)=
        syntheticJet (Poly.mk (row.coeff i::rest.map (fun p=>p.coeff i))) b (j+1)
      rw [zero_coeff,ih,ih,synthetic_jet_cons_succ]
      grind

def syntheticMixedJet (rows : List (Poly K)) (a b : K) (r s : Nat) : K :=
  syntheticJet (Poly.mk (rows.map (fun row=>syntheticJet row a r))) b s

/-- Actual mixed coefficients of Q(X+a,Y+b) equal nested synthetic jets.
This is formal coefficient algebra in every characteristic, including small
fields where equality of evaluation functions would not suffice. -/
theorem bivariate_translate_mixed_jet (rows : List (Poly K)) (a b : K) (r s : Nat) :
    ((bivariateTranslate rows a b).getD s Poly.zero).coeff r=syntheticMixedJet rows a b r s := by
  unfold bivariateTranslate
  rw [bivariate_translate_y_coefficient]
  simp only [List.map_map,Function.comp_def,polynomial_translate_coeff,syntheticMixedJet]

/-- The interpolation constraints are precisely the mixed jets of total
order below m, not only the pure X and Y derivatives. -/
theorem bivariate_order_mixed_jets (rows : List (Poly K)) (a b : K) (m : Nat) :
    BivariateOrder (bivariateTranslate rows a b) m ↔
      ∀ r s,r+s<m→syntheticMixedJet rows a b r s=0 := by
  simp only [BivariateOrder,bivariate_translate_mixed_jet]
end NearCompression
