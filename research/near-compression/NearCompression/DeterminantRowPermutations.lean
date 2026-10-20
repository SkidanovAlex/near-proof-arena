import NearCompression.DeterminantRowReplacement

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem fold_scale (cs : List Nat) (f : Nat→List Nat→K) (a : K) :
    determinantCofactorFold cs (fun c rest=>a*f c rest)=a*determinantCofactorFold cs f := by
  induction cs generalizing f with
  | nil => change (0:K)=a*0;grind
  | cons c cs ih => simp only [determinantCofactorFold,ih];grind

private theorem fold_congr (cs : List Nat) (f g : Nat→List Nat→K)
    (same : ∀ c rest,f c rest=g c rest) : determinantCofactorFold cs f=determinantCofactorFold cs g := by
  have eq : f=g := by funext c rest;exact same c rest
  rw [eq]

/-- Every row permutation scales all column minors by one common nonzero
factor. This avoids choosing a sign representation in characteristic two. -/
theorem scalar_minor_row_permutation_factor (M : Nat→Nat→K) (xs ys : List Nat) (perm : xs.Perm ys) :
    ∃ s : K,s≠0 ∧ ∀ columns,scalarMinorDeterminant M xs columns=s*scalarMinorDeterminant M ys columns := by
  induction perm with
  | nil => exact ⟨1,(fun zero=>Field.zero_ne_one zero.symm),by intro columns;change (1:K)=1*1;grind⟩
  | @cons row xs ys perm ih =>
    obtain ⟨s,sn,equation⟩:=ih
    refine ⟨s,sn,?_⟩
    intro columns
    rw [scalar_minor_cofactor_fold,scalar_minor_cofactor_fold,←fold_scale]
    apply fold_congr
    intro c rest
    rw [equation];grind
  | swap a b rows =>
    refine ⟨-1,?_,?_⟩
    · intro zero
      have impossible : (0:K)=1 := by grind
      exact Field.zero_ne_one impossible
    · intro columns;rw [scalar_minor_swap_first_rows];grind
  | @trans xs ys zs xy yz ihxy ihyz =>
    obtain ⟨s,sn,se⟩:=ihxy
    obtain ⟨t,tn,te⟩:=ihyz
    refine ⟨s*t,?_,?_⟩
    · intro zero;rcases Field.of_mul_eq_zero zero with zero|zero
      · exact sn zero
      · exact tn zero
    · intro columns;rw [se,te];grind

/-- Singularity is invariant under any row permutation. -/
theorem scalar_minor_row_permutation_zero (M : Nat→Nat→K) (xs ys columns : List Nat)
    (perm : xs.Perm ys) : scalarMinorDeterminant M xs columns=0 ↔ scalarMinorDeterminant M ys columns=0 := by
  obtain ⟨s,sn,equation⟩:=scalar_minor_row_permutation_factor M xs ys perm
  rw [equation]
  constructor
  · intro zero;rcases Field.of_mul_eq_zero zero with zero|zero
    · exact False.elim (sn zero)
    · exact zero
  · intro zero;rw [zero];grind

/-- Repeated row labels force zero without requiring their positions up front. -/
theorem scalar_minor_nonnodup_zero (M : Nat→Nat→K) (rows columns : List Nat)
    (repeated : ¬rows.Nodup) : scalarMinorDeterminant M rows columns=0 := by
  induction rows generalizing columns with
  | nil => exact False.elim (repeated (by simp))
  | cons r rows ih =>
    by_cases inside : r∈rows
    · obtain ⟨middle,after,eq⟩:=List.append_of_mem inside
      rw [eq]
      exact scalar_minor_equal_rows M [] middle after columns r r (fun _=>rfl)
    · have tail : ¬rows.Nodup := fun nd=>repeated (List.nodup_cons.mpr ⟨inside,nd⟩)
      rw [scalar_minor_cofactor_fold]
      have zero : determinantCofactorFold columns (fun _ _=>(0:K))=0 := by
        induction columns with
        | nil => rfl
        | cons c cs ih => change 0-determinantCofactorFold cs (fun _ _=>(0:K))=0;rw [ih];grind
      rw [←zero]
      apply fold_congr
      intro c rest
      rw [ih rest tail];grind

private theorem full_subset_perm (xs ys : List Nat) (xd : xs.Nodup) (yd : ys.Nodup)
    (subset : ∀ i∈xs,i∈ys) (length : xs.length=ys.length) : xs.Perm ys := by
  apply (List.perm_ext_iff_of_nodup xd yd).mpr
  intro i
  constructor
  · exact subset i
  · intro member
    apply Classical.byContradiction
    intro absent
    have extra : (i::xs).Nodup := List.nodup_cons.mpr ⟨absent,xd⟩
    have inclusion : ∀ j∈i::xs,j∈ys := by
      intro j hj
      simp only [List.mem_cons] at hj
      rcases hj with eq|inside
      · subst j;exact member
      · exact subset j inside
    have impossible:=extra.length_le_of_subset inclusion
    simp only [List.length_cons] at impossible
    omega

/-- If the original square row family has zero determinant, any equally
long selection from those rows also has zero determinant: it either repeats
rows or is a permutation of the original family. -/
theorem scalar_minor_selected_rows_zero (M : Nat→Nat→K) (rows selected columns : List Nat)
    (distinct : rows.Nodup) (length : selected.length=rows.length)
    (subset : ∀ i∈selected,i∈rows) (zero : scalarMinorDeterminant M rows columns=0) :
    scalarMinorDeterminant M selected columns=0 := by
  by_cases sd : selected.Nodup
  · exact (scalar_minor_row_permutation_zero M selected rows columns (full_subset_perm selected rows sd distinct subset length)).mpr zero
  · exact scalar_minor_nonnodup_zero M selected columns sd

/-- Reindexing rows in the entry function is exactly selection of row labels. -/
theorem scalar_minor_row_reindex (M : Nat→Nat→K) (select : Nat→Nat) (rows columns : List Nat) :
    scalarMinorDeterminant (fun i j=>M (select i) j) rows columns=
      scalarMinorDeterminant M (rows.map select) columns := by
  induction rows generalizing columns with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.map_cons]
    rw [scalar_minor_cofactor_fold,scalar_minor_cofactor_fold]
    apply fold_congr
    intro c rest
    rw [ih]
end NearCompression
