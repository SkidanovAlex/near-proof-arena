import NearCompression.DeterminantRowLinearity

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Signed selection of one column, carrying the remaining ordered columns. -/
def determinantCofactorFold : List Nat → (Nat → List Nat → K) → K
  | [], _ => 0
  | c::cs, f => f c cs-determinantCofactorFold cs (fun d rest=>f d (c::rest))

theorem determinant_cofactor_fold_linear (cs : List Nat) (f g : Nat→List Nat→K) (a b : K) :
    determinantCofactorFold cs (fun c rest=>a*f c rest+b*g c rest)=
      a*determinantCofactorFold cs f+b*determinantCofactorFold cs g := by
  induction cs generalizing f g with
  | nil => change (0:K)=a*0+b*0;grind
  | cons c cs ih =>
    simp only [determinantCofactorFold,ih]
    grind

private theorem fold_congr (cs : List Nat) (f g : Nat→List Nat→K)
    (same : ∀ c rest,f c rest=g c rest) : determinantCofactorFold cs f=determinantCofactorFold cs g := by
  have eq : f=g := by funext c rest;exact same c rest
  rw [eq]

private theorem sum_neg (xs : List Nat) (f g : Nat→K) (same : ∀ i,g i= -f i) :
    (xs.map g).foldr (·+·) 0= -(xs.map f).foldr (·+·) 0 := by
  induction xs with
  | nil => change (0:K)= -0;grind
  | cons i xs ih => simp only [List.map_cons,List.foldr_cons,same,ih];grind

private theorem parity_sign (j : Nat) :
    (if (j+1)%2=0 then (1:K) else -1)= -(if j%2=0 then (1:K) else -1) := by
  by_cases even : j%2=0
  · have odd : (j+1)%2≠0 := by omega
    rw [ite_eq_right odd,ite_eq_left even]
  · have evenNext : (j+1)%2=0 := by omega
    rw [ite_eq_left evenNext,ite_eq_right even]
    grind

/-- The fold is exactly the indexed alternating Laplace sum. -/
theorem determinant_cofactor_fold_indexed (cs : List Nat) (f : Nat→List Nat→K) :
    determinantCofactorFold cs f=
      ((List.range cs.length).map (fun j=>(if j%2=0 then (1:K) else -1)*
        f (cs.getD j 0) (cs.eraseIdx j))).foldr (·+·) 0 := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    rw [determinantCofactorFold,ih]
    simp only [List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,
      List.foldr_cons,Function.comp_def]
    change f c cs-((List.range cs.length).map (fun j=>(if j%2=0 then (1:K) else -1)*
      f (cs.getD j 0) (c::cs.eraseIdx j))).foldr (·+·) 0=
      1*f c cs+((List.range cs.length).map (fun j=>(if (j+1)%2=0 then (1:K) else -1)*
      f (cs.getD j 0) (c::cs.eraseIdx j))).foldr (·+·) 0
    have negsum:=sum_neg (List.range cs.length)
      (fun j=>(if j%2=0 then (1:K) else -1)*f (cs.getD j 0) (c::cs.eraseIdx j))
      (fun j=>(if (j+1)%2=0 then (1:K) else -1)*f (cs.getD j 0) (c::cs.eraseIdx j))
      (fun j=>by rw [parity_sign];grind)
    rw [negsum]
    grind

/-- Re-express the existing determinant, rather than introduce an unrelated one. -/
theorem scalar_minor_cofactor_fold (M : Nat→Nat→K) (row : Nat) (rows columns : List Nat) :
    scalarMinorDeterminant M (row::rows) columns=
      determinantCofactorFold columns (fun c rest=>M row c*scalarMinorDeterminant M rows rest) := by
  rw [determinant_cofactor_fold_indexed]
  simp only [scalarMinorDeterminant]
  congr 2
  funext j
  grind

private theorem fold_sub (cs : List Nat) (f g : Nat→List Nat→K) :
    determinantCofactorFold cs (fun c rest=>f c rest-g c rest)=
      determinantCofactorFold cs f-determinantCofactorFold cs g := by
  have linear:=determinant_cofactor_fold_linear cs f g 1 (-1)
  have same : (fun c rest=>(1:K)*f c rest+(-1)*g c rest)=(fun c rest=>f c rest-g c rest) := by
    funext c rest;grind
  rw [same] at linear
  grind

/-- Symmetric paired selections cancel without division by two. -/
theorem determinant_double_cofactor_symmetric_zero (cs : List Nat)
    (f : Nat→Nat→List Nat→K) (symmetric : ∀ c d rest,f c d rest=f d c rest) :
    determinantCofactorFold cs (fun c rest=>determinantCofactorFold rest (fun d rem=>f c d rem))=0 := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change determinantCofactorFold cs (fun d rest=>f c d rest)-
      determinantCofactorFold cs (fun d rest=>f d c rest-
        determinantCofactorFold rest (fun e rem=>f d e (c::rem)))=0
    rw [fold_sub]
    have zero:=ih (fun d e rem=>f d e (c::rem)) (fun d e rem=>symmetric d e (c::rem))
    have same:=fold_congr cs (fun d rest=>f c d rest) (fun d rest=>f d c rest)
      (fun d rest=>symmetric c d rest)
    rw [zero,same]
    grind

/-- Exchanging the order of two selected columns negates the double fold. -/
theorem determinant_double_cofactor_swap (cs : List Nat) (f : Nat→Nat→List Nat→K) :
    determinantCofactorFold cs (fun c rest=>determinantCofactorFold rest (fun d rem=>f c d rem))=
      -determinantCofactorFold cs (fun c rest=>determinantCofactorFold rest (fun d rem=>f d c rem)) := by
  induction cs generalizing f with
  | nil => change (0:K)= -0;grind
  | cons c cs ih =>
    change determinantCofactorFold cs (fun d rest=>f c d rest)-
      determinantCofactorFold cs (fun d rest=>f d c rest-
        determinantCofactorFold rest (fun e rem=>f d e (c::rem)))=
      -(determinantCofactorFold cs (fun d rest=>f d c rest)-
      determinantCofactorFold cs (fun d rest=>f c d rest-
        determinantCofactorFold rest (fun e rem=>f e d (c::rem))))
    rw [fold_sub,fold_sub]
    have tail:=ih (fun d e rem=>f d e (c::rem))
    grind

private theorem fold_scale (cs : List Nat) (f : Nat→List Nat→K) (a : K) :
    determinantCofactorFold cs (fun c rest=>a*f c rest)=a*determinantCofactorFold cs f := by
  have linear:=determinant_cofactor_fold_linear cs f f a 0
  have same : (fun c rest=>a*f c rest+(0:K)*f c rest)=(fun c rest=>a*f c rest) := by
    funext c rest;grind
  rw [same] at linear
  grind

private theorem two_row_expansion (M : Nat→Nat→K) (r s : Nat) (rows cs : List Nat) :
    scalarMinorDeterminant M (r::s::rows) cs=
      determinantCofactorFold cs (fun c rest=>determinantCofactorFold rest
        (fun d rem=>M r c*M s d*scalarMinorDeterminant M rows rem)) := by
  rw [scalar_minor_cofactor_fold]
  apply fold_congr
  intro c rest
  rw [scalar_minor_cofactor_fold,←fold_scale]
  apply fold_congr
  intro d rem
  grind

/-- Swapping the first two rows reverses the determinant sign. -/
theorem scalar_minor_swap_first_rows (M : Nat→Nat→K) (r s : Nat) (rows cs : List Nat) :
    scalarMinorDeterminant M (r::s::rows) cs= -scalarMinorDeterminant M (s::r::rows) cs := by
  rw [two_row_expansion,two_row_expansion,determinant_double_cofactor_swap]
  congr 1
  apply fold_congr
  intro c rest
  apply fold_congr
  intro d rem
  grind

/-- Equal first rows force determinant zero, valid even in characteristic two. -/
theorem scalar_minor_equal_first_rows (M : Nat→Nat→K) (r s : Nat) (rows cs : List Nat)
    (same : ∀ j,M r j=M s j) : scalarMinorDeterminant M (r::s::rows) cs=0 := by
  rw [two_row_expansion]
  apply determinant_double_cofactor_symmetric_zero
  intro c d rem
  rw [same c,same d]
  grind

/-- Adjacent row transpositions reverse sign at every position. -/
theorem scalar_minor_swap_adjacent_rows (M : Nat→Nat→K) (before : List Nat)
    (r s : Nat) (suffix columns : List Nat) :
    scalarMinorDeterminant M (before++r::s::suffix) columns=
      -scalarMinorDeterminant M (before++s::r::suffix) columns := by
  induction before generalizing columns with
  | nil => exact scalar_minor_swap_first_rows M r s suffix columns
  | cons row before ih =>
    simp only [List.cons_append]
    rw [scalar_minor_cofactor_fold,scalar_minor_cofactor_fold]
    have scale:=fold_scale columns
      (fun c rest=>M row c*scalarMinorDeterminant M (before++s::r::suffix) rest) (-1)
    have same:=fold_congr columns
      (fun c rest=>M row c*scalarMinorDeterminant M (before++r::s::suffix) rest)
      (fun c rest=>(-1)* (M row c*scalarMinorDeterminant M (before++s::r::suffix) rest))
      (fun c rest=>by rw [ih];grind)
    rw [same,scale]
    grind

private theorem fold_zero (columns : List Nat) (f : Nat→List Nat→K)
    (zero : ∀ c rest,f c rest=0) : determinantCofactorFold columns f=0 := by
  induction columns generalizing f with
  | nil => rfl
  | cons c cs ih =>
    rw [determinantCofactorFold,zero,ih _ (fun d rest=>zero d (c::rest))]
    grind

private theorem separated_equal_rows (M : Nat→Nat→K) (r s : Nat) (middle suffix columns : List Nat)
    (same : ∀ j,M r j=M s j) : scalarMinorDeterminant M (r::middle++s::suffix) columns=0 := by
  induction middle generalizing columns with
  | nil => exact scalar_minor_equal_first_rows M r s suffix columns same
  | cons row middle ih =>
    change scalarMinorDeterminant M (r::row::(middle++s::suffix)) columns=0
    rw [scalar_minor_swap_first_rows,scalar_minor_cofactor_fold]
    have zero : determinantCofactorFold columns
        (fun c rest=>M row c*scalarMinorDeterminant M (r::middle++s::suffix) rest)=0 := by
      apply fold_zero
      intro c rest
      rw [ih];grind
    simp only [List.cons_append] at zero
    rw [zero];grind

/-- Any two equal selected rows force zero, even when separated by other rows
and even in characteristic two. -/
theorem scalar_minor_equal_rows (M : Nat→Nat→K) (before middle suffix columns : List Nat)
    (r s : Nat) (same : ∀ j,M r j=M s j) :
    scalarMinorDeterminant M (before++r::middle++s::suffix) columns=0 := by
  induction before generalizing columns with
  | nil => exact separated_equal_rows M r s middle suffix columns same
  | cons row before ih =>
    simp only [List.cons_append]
    rw [scalar_minor_cofactor_fold]
    apply fold_zero
    intro c rest
    rw [ih];grind
end NearCompression
