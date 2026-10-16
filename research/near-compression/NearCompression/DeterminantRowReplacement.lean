import NearCompression.DeterminantCofactorFold

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem fold_zero (cs : List Nat) (f : Nat→List Nat→K) (zero : ∀ c rest,f c rest=0) :
    determinantCofactorFold cs f=0 := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih => rw [determinantCofactorFold,zero,ih _ (fun d rest=>zero d (c::rest))];grind

/-- Two distinct selected row labels with equal entries force zero. -/
theorem scalar_minor_duplicate_row_values (M : Nat→Nat→K) (rows columns : List Nat)
    (r s : Nat) (different : r≠s) (rm : r∈rows) (sm : s∈rows)
    (same : ∀ j,M r j=M s j) : scalarMinorDeterminant M rows columns=0 := by
  induction rows generalizing columns with
  | nil => simp at rm
  | cons row rows ih =>
    by_cases rr : row=r
    · subst row
      have inside : s∈rows := by simp only [List.mem_cons] at sm;rcases sm with h|h;exact False.elim (different h.symm);exact h
      obtain ⟨middle,after,eq⟩:=List.append_of_mem inside
      rw [eq]
      exact scalar_minor_equal_rows M [] middle after columns r s same
    · by_cases ss : row=s
      · subst row
        have inside : r∈rows := by simp only [List.mem_cons] at rm;rcases rm with h|h;exact False.elim (different h);exact h
        obtain ⟨middle,after,eq⟩:=List.append_of_mem inside
        rw [eq]
        exact scalar_minor_equal_rows M [] middle after columns s r (fun j=>(same j).symm)
      · have rin : r∈rows := by simp only [List.mem_cons] at rm;rcases rm with h|h;exact False.elim (rr h.symm);exact h
        have sin : s∈rows := by simp only [List.mem_cons] at sm;rcases sm with h|h;exact False.elim (ss h.symm);exact h
        rw [scalar_minor_cofactor_fold]
        apply fold_zero
        intro c rest
        rw [ih rest rin sin];grind

/-- Replacing a selected row by another selected row kills the determinant. -/
theorem scalar_minor_replace_other_row (M : Nat→Nat→K) (rows columns : List Nat)
    (r s : Nat) (different : r≠s) (rm : r∈rows) (sm : s∈rows) :
    scalarMinorDeterminant (replaceDeterminantRow M r (M s)) rows columns=0 := by
  apply scalar_minor_duplicate_row_values _ rows columns r s different rm sm
  intro j
  simp [replaceDeterminantRow,Ne.symm different]

private theorem replacement_own (M : Nat→Nat→K) (rows columns : List Nat) (r : Nat) :
    scalarMinorDeterminant (replaceDeterminantRow M r (M r)) rows columns=scalarMinorDeterminant M rows columns := by
  apply scalar_minor_rows_congr
  intro i hi j
  by_cases eq : i=r
  · subst i;simp [replaceDeterminantRow]
  · simp [replaceDeterminantRow,eq]

/-- Expand a replaced row expressed as a finite linear combination. -/
theorem scalar_minor_replace_row_sum (M : Nat→Nat→K) (rows columns indices : List Nat)
    (distinct : rows.Nodup) (r : Nat) (member : r∈rows) (weights : Nat→K) (vectors : Nat→Nat→K) :
    scalarMinorDeterminant (replaceDeterminantRow M r (fun j=>kernelDot indices weights (fun i=>vectors i j))) rows columns=
      kernelDot indices weights (fun i=>scalarMinorDeterminant (replaceDeterminantRow M r (vectors i)) rows columns) := by
  induction indices with
  | nil => exact scalar_minor_zero_row M rows columns distinct r member
  | cons i indices ih =>
    change scalarMinorDeterminant (replaceDeterminantRow M r
      (fun j=>weights i*vectors i j+kernelDot indices weights (fun k=>vectors k j))) rows columns=_
    have linear:=scalar_minor_row_linear M rows columns distinct r member (vectors i)
      (fun j=>kernelDot indices weights (fun k=>vectors k j)) (weights i) 1
    have functionEq : (fun j=>weights i*vectors i j+(1:K)*kernelDot indices weights (fun k=>vectors k j))=
      (fun j=>weights i*vectors i j+kernelDot indices weights (fun k=>vectors k j)) := by funext j;grind
    rw [functionEq,ih] at linear
    change _=weights i*scalarMinorDeterminant (replaceDeterminantRow M r (vectors i)) rows columns+
      kernelDot indices weights (fun k=>scalarMinorDeterminant (replaceDeterminantRow M r (vectors k)) rows columns)
    grind

private theorem dot_congr (xs : List Nat) (weights f g : Nat→K) (same : ∀ i∈xs,f i=g i) :
    kernelDot xs weights f=kernelDot xs weights g := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp only [kernelDot,same i (by simp),ih (fun j hj=>same j (by simp [hj]))]

private theorem dot_zero (xs : List Nat) (weights f : Nat→K) (zero : ∀ i∈xs,f i=0) :
    kernelDot xs weights f=0 := by
  induction xs with
  | nil => rfl
  | cons i xs ih => rw [kernelDot,zero i (by simp),ih (fun j hj=>zero j (by simp [hj]))];grind

private theorem dot_single (xs : List Nat) (weights : Nat→K) (r : Nat) (c : K)
    (distinct : xs.Nodup) (member : r∈xs) : kernelDot xs weights (fun i=>if i=r then c else 0)=weights r*c := by
  induction xs with
  | nil => simp at member
  | cons i xs ih =>
    have nd:=List.nodup_cons.mp distinct
    by_cases eq : i=r
    · subst i
      have zero:=dot_zero xs weights (fun i=>if i=r then c else 0)
        (fun i hi=>by rw [ite_eq_right (by intro eq;subst i;exact nd.1 hi)])
      rw [kernelDot,ite_eq_left rfl,zero];grind
    · have inside : r∈xs := by simp only [List.mem_cons] at member;rcases member with h|h;exact False.elim (eq h.symm);exact h
      rw [kernelDot,ite_eq_right eq,ih nd.2 inside];grind

/-- Row form of Cramer's identity: replacing row r by a combination of all
selected rows multiplies the determinant by precisely the coefficient of r. -/
theorem scalar_minor_row_cramer_identity (M : Nat→Nat→K) (rows columns : List Nat)
    (distinct : rows.Nodup) (r : Nat) (member : r∈rows) (weights : Nat→K) :
    scalarMinorDeterminant (replaceDeterminantRow M r (fun j=>kernelDot rows weights (fun i=>M i j))) rows columns=
      weights r*scalarMinorDeterminant M rows columns := by
  rw [scalar_minor_replace_row_sum M rows columns rows distinct r member weights M]
  have same : ∀ i∈rows,scalarMinorDeterminant (replaceDeterminantRow M r (M i)) rows columns=
      if i=r then scalarMinorDeterminant M rows columns else 0 := by
    intro i hi
    by_cases eq : i=r
    · subst i;rw [ite_eq_left rfl,replacement_own]
    · rw [ite_eq_right eq]
      exact scalar_minor_replace_other_row M rows columns r i (Ne.symm eq) member hi
  rw [dot_congr rows weights _ _ same]
  exact dot_single rows weights r _ distinct member

/-- A solved row system has Cramer numerators over the common determinant.
Nonzeroness is explicit until the invertibility bridge is completed. -/
theorem scalar_minor_cramer_denominator (M : Nat→Nat→K) (rows columns : List Nat)
    (distinct : rows.Nodup) (r : Nat) (member : r∈rows) (weights target : Nat→K)
    (solved : ∀ j,kernelDot rows weights (fun i=>M i j)=target j)
    (nonzero : scalarMinorDeterminant M rows columns≠0) :
    weights r=scalarMinorDeterminant (replaceDeterminantRow M r target) rows columns*
      (scalarMinorDeterminant M rows columns)⁻¹ := by
  have cramer:=scalar_minor_row_cramer_identity M rows columns distinct r member weights
  have functionEq : (fun j=>kernelDot rows weights (fun i=>M i j))=target := by funext j;exact solved j
  rw [functionEq] at cramer
  have inverse:=Field.mul_inv_cancel nonzero
  grind

/-- A row dependence with a nonzero selected coefficient forces singularity. -/
theorem scalar_minor_row_dependence_zero (M : Nat→Nat→K) (rows columns : List Nat)
    (distinct : rows.Nodup) (r : Nat) (member : r∈rows) (weights : Nat→K)
    (nonzero : weights r≠0) (dependence : ∀ j,kernelDot rows weights (fun i=>M i j)=0) :
    scalarMinorDeterminant M rows columns=0 := by
  have cramer:=scalar_minor_row_cramer_identity M rows columns distinct r member weights
  have functionEq : (fun j=>kernelDot rows weights (fun i=>M i j))=(fun _=>0) := by funext j;exact dependence j
  rw [functionEq,scalar_minor_zero_row M rows columns distinct r member] at cramer
  rcases Field.of_mul_eq_zero cramer.symm with zero|zero
  · exact False.elim (nonzero zero)
  · exact zero
end NearCompression
