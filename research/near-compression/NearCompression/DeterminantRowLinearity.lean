import NearCompression.PolynomialDeterminantDegree

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem sum_linear (xs : List Nat) (f g h : Nat→K) (a b : K)
    (same : ∀ i∈xs,h i=a*f i+b*g i) :
    (xs.map h).foldr (·+·) 0=a*(xs.map f).foldr (·+·) 0+b*(xs.map g).foldr (·+·) 0 := by
  induction xs with
  | nil => change (0:K)=a*0+b*0;grind
  | cons i xs ih =>
    have head:=same i (by simp)
    have tail:=ih (fun j hj=>same j (by simp [hj]))
    simp only [List.map_cons,List.foldr_cons,head,tail]
    grind

/-- Only entries on the selected rows affect the Laplace minor. -/
theorem scalar_minor_rows_congr (M N : Nat→Nat→K) (rows columns : List Nat)
    (same : ∀ i∈rows,∀ j,M i j=N i j) :
    scalarMinorDeterminant M rows columns=scalarMinorDeterminant N rows columns := by
  induction rows generalizing columns with
  | nil => rfl
  | cons row rows ih =>
    simp only [scalarMinorDeterminant]
    congr 2
    funext j
    rw [same row (by simp),ih (columns.eraseIdx j) (fun i hi=>same i (by simp [hi]))]

def replaceDeterminantRow (M : Nat→Nat→K) (row : Nat) (values : Nat→K) : Nat→Nat→K :=
  fun i j=>if i=row then values j else M i j

private theorem replacement_off_rows (M : Nat→Nat→K) (r : Nat) (v : Nat→K)
    (rows columns : List Nat) (outside : r∉rows) :
    scalarMinorDeterminant (replaceDeterminantRow M r v) rows columns=scalarMinorDeterminant M rows columns := by
  apply scalar_minor_rows_congr
  intro i hi j
  have different : i≠r := by intro same;subst i;exact outside hi
  simp [replaceDeterminantRow,different]

/-- The determinant is linear in any selected row, provided row labels are
distinct. Column order and the resulting signs are unchanged. -/
theorem scalar_minor_row_linear (M : Nat→Nat→K) (rows columns : List Nat)
    (distinct : rows.Nodup) (r : Nat) (member : r∈rows) (u v : Nat→K) (a b : K) :
    scalarMinorDeterminant (replaceDeterminantRow M r (fun j=>a*u j+b*v j)) rows columns=
      a*scalarMinorDeterminant (replaceDeterminantRow M r u) rows columns+
      b*scalarMinorDeterminant (replaceDeterminantRow M r v) rows columns := by
  induction rows generalizing columns with
  | nil => simp at member
  | cons row rows ih =>
    have nodup:=List.nodup_cons.mp distinct
    simp only [scalarMinorDeterminant]
    apply sum_linear
    intro j hj
    by_cases equal : row=r
    · subst row
      rw [replacement_off_rows M r _ rows _ nodup.1,
        replacement_off_rows M r u rows _ nodup.1,
        replacement_off_rows M r v rows _ nodup.1]
      simp only [replaceDeterminantRow,ite_true]
      grind
    · have inside : r∈rows := by simp only [List.mem_cons] at member;rcases member with h|h;exact False.elim (equal h.symm);exact h
      rw [ih (columns.eraseIdx j) nodup.2 inside]
      simp only [replaceDeterminantRow,ite_eq_right equal]
      grind

/-- A zero selected row gives zero determinant; no nonsingularity is assumed. -/
theorem scalar_minor_zero_row (M : Nat→Nat→K) (rows columns : List Nat)
    (distinct : rows.Nodup) (r : Nat) (member : r∈rows) :
    scalarMinorDeterminant (replaceDeterminantRow M r (fun _=>0)) rows columns=0 := by
  have linear:=scalar_minor_row_linear M rows columns distinct r member (fun _=>0) (fun _=>0) 0 0
  have same : (fun _ : Nat=>(0:K)*0+0*0)=(fun _=>0) := by funext i;grind
  rw [same] at linear
  grind

private theorem rational_smul (c : K) (p : Poly K) :
    polynomialRationalOfPolynomial (Poly.smul c p)=
      polynomialRationalCoefficientMap.toFun c*polynomialRationalOfPolynomial p := by
  change polynomialRationalOfPolynomial (Poly.smul c p)=polynomialRationalOfPolynomial (Poly.C c)*polynomialRationalOfPolynomial p
  rw [←polynomial_rational_of_polynomial_mul]
  apply (polynomial_rational_of_polynomial_eq_iff _ _).mpr
  intro i
  change (Poly.smul c p).coeff i=(Poly.smul c p+Poly.mk [0]).coeff i
  rw [Poly.coeff_add]
  have zero : (Poly.mk [0] : Poly K).coeff i=0 := by cases i <;> rfl
  rw [zero];grind

private theorem rational_zero : polynomialRationalOfPolynomial (Poly.zero : Poly K)=0 := by
  apply (polynomial_rational_of_polynomial_eq_iff _ _).mpr
  intro i;cases i <;> rfl

private theorem rational_sum (ps : List (Poly K)) :
    polynomialRationalOfPolynomial (Poly.sum ps)=
      (ps.map polynomialRationalOfPolynomial).foldr (·+·) 0 := by
  induction ps with
  | nil => exact rational_zero
  | cons p ps ih =>
    change polynomialRationalOfPolynomial (p+Poly.sum ps)=_
    rw [polynomial_rational_of_polynomial_add,ih]
    rfl

/-- The polynomial determinant embeds as the determinant over the actual
rational-function field; no evaluation at finitely many base points is used. -/
theorem polynomial_minor_determinant_rational_transport (M : Nat→Nat→Poly K)
    (rows columns : List Nat) :
    polynomialRationalOfPolynomial (polynomialMinorDeterminant M rows columns)=
      scalarMinorDeterminant (fun i j=>polynomialRationalOfPolynomial (M i j)) rows columns := by
  induction rows generalizing columns with
  | nil => rfl
  | cons row rows ih =>
    simp only [polynomialMinorDeterminant,scalarMinorDeterminant,rational_sum,List.map_map,Function.comp_def]
    congr 2
    funext j
    rw [rational_smul,polynomial_rational_of_polynomial_mul,ih]
    have negative : (polynomialRationalCoefficientMap (K:=K)).toFun (-1)= -1 := by
      have eq:=(polynomialRationalCoefficientMap (K:=K)).add (-1) 1
      have zero : (-1:K)+1=0 := by grind
      rw [zero,polynomialRationalCoefficientMap.zero,polynomialRationalCoefficientMap.one] at eq
      grind
    by_cases even : j%2=0
    · simp only [ite_eq_left even,polynomialRationalCoefficientMap.one];grind
    · simp only [ite_eq_right even,negative];grind

/-- Formal determinant nonzeroness is equivalent to nonzero determinant over
the constructed rational-function field. Invertibility must still supply it. -/
theorem polynomial_minor_determinant_nonzero_iff (M : Nat→Nat→Poly K)
    (rows columns : List Nat) :
    ¬(polynomialMinorDeterminant M rows columns).IsZero ↔
      scalarMinorDeterminant (fun i j=>polynomialRationalOfPolynomial (M i j)) rows columns≠0 := by
  rw [←polynomial_minor_determinant_rational_transport]
  constructor
  · intro nonzero zero
    have formal:=polynomial_rational_polynomial_injective _ _ zero
    exact nonzero ((formal_polynomial_zero_iff _).mp formal)
  · intro nonzero zero
    apply nonzero
    have formal:=(formal_polynomial_zero_iff _).mpr zero
    exact congrArg (fun p=>polynomialRationalClass (.ofPolynomial p)) formal
end NearCompression
