import NearCompression.BivariateWeightedDegree

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K I : Type} [Field K]

/-- Finite homogeneous equation with explicitly indexed unknowns. -/
def kernelDot (variables : List I) (row values : I→K) : K :=
  match variables with
  | [] => 0
  | i::rest => row i*values i+kernelDot rest row values

private theorem dot_permutation (xs ys : List I) (perm : xs.Perm ys) (row values : I→K) :
    kernelDot xs row values=kernelDot ys row values := by
  induction perm with
  | nil => rfl
  | cons a perm ih => simp only [kernelDot,ih]
  | swap a b rest => simp only [kernelDot];grind
  | trans ab bc ihab ihbc => exact ihab.trans ihbc

private theorem dot_values (xs : List I) (row left right : I→K)
    (same : ∀ i∈xs,left i=right i) : kernelDot xs row left=kernelDot xs row right := by
  induction xs with
  | nil => rfl
  | cons i rest ih =>
    have head:=same i (by simp)
    have tail:=ih (fun j hj=>same j (by simp [hj]))
    simp only [kernelDot,head,tail]

private theorem dot_zero_row (xs : List I) (row values : I→K)
    (zero : ∀ i∈xs,row i=0) : kernelDot xs row values=0 := by
  induction xs with
  | nil => rfl
  | cons i rest ih =>
    have head:=zero i (by simp)
    have tail:=ih (fun j hj=>zero j (by simp [hj]))
    simp only [kernelDot,head,tail];grind

/-- Exact row elimination identity, not a rank or solver assumption. -/
theorem kernel_dot_elimination (xs : List I) (row pivot values : I→K) (factor : K) :
    kernelDot xs (fun i=>row i-factor*pivot i) values=
      kernelDot xs row values-factor*kernelDot xs pivot values := by
  induction xs with
  | nil => simp only [kernelDot];grind
  | cons i rest ih => simp only [kernelDot,ih];grind

private theorem kernel_aux (n : Nat) (rows : List (I→K)) (variables : List I)
    (shape : rows.length=n) (distinct : variables.Nodup) (short : n<variables.length) :
    ∃ values : I→K,(∃ i∈variables,values i≠0) ∧ ∀ row∈rows,kernelDot variables row values=0 := by
  classical
  induction n generalizing rows variables with
  | zero =>
    have empty : rows=[] := List.eq_nil_of_length_eq_zero shape
    subst rows
    cases variables with
    | nil => simp at short
    | cons i rest =>
      refine ⟨fun j=>if j=i then 1 else 0,⟨i,by simp,?_⟩,?_⟩
      · simp only [ite_true];exact fun h=>Field.zero_ne_one h.symm
      · simp
  | succ n ih =>
    cases rows with
    | nil => simp at shape
    | cons pivot rest =>
      have rshape : rest.length=n := by simpa using shape
      by_cases existsPivot : ∃ a∈variables,pivot a≠0
      · obtain ⟨a,ha,nonzero⟩:=existsPivot
        let remaining:=variables.erase a
        let reduced:=rest.map (fun row i=>row i-(row a*(pivot a)⁻¹)*pivot i)
        have len : remaining.length=variables.length-1 := List.length_erase_of_mem ha
        obtain ⟨u,⟨b,hb,ub⟩,solves⟩:=ih reduced remaining (by simp [reduced,rshape])
          (distinct.erase a) (by omega)
        let va:= -(pivot a)⁻¹*kernelDot remaining pivot u
        let values:=fun i=>if i=a then va else u i
        have inverse:=Field.mul_inv_cancel nonzero
        have same : ∀ i∈remaining,values i=u i := by
          intro i hi
          have ne : i≠a := (distinct.mem_erase_iff.mp hi).1
          simp only [values,ite_eq_right (by exact ne)]
        have split (row : I→K) : kernelDot variables row values=
            row a*va+kernelDot remaining row u := by
          rw [dot_permutation variables (a::remaining) (List.perm_cons_erase ha) row values]
          simp only [kernelDot,values,ite_true]
          rw [dot_values remaining row values u same]
        refine ⟨values,⟨b,List.mem_of_mem_erase hb,?_⟩,?_⟩
        · rw [same b hb];exact ub
        · intro row member
          rcases List.mem_cons.mp member with equal | tail
          · subst row
            rw [split]
            dsimp only [va]
            grind
          · have equation:=solves (fun i=>row i-(row a*(pivot a)⁻¹)*pivot i)
              (List.mem_map.mpr ⟨row,tail,rfl⟩)
            rw [kernel_dot_elimination] at equation
            rw [split]
            dsimp only [va]
            grind
      · have zero : ∀ i∈variables,pivot i=0 := by
          intro i hi
          apply Classical.byContradiction
          intro ne
          exact existsPivot ⟨i,hi,ne⟩
        obtain ⟨values,nonzero,solves⟩:=ih rest variables rshape distinct (by omega)
        refine ⟨values,nonzero,?_⟩
        intro row member
        rcases List.mem_cons.mp member with equal | tail
        · subst row;exact dot_zero_row variables pivot values zero
        · exact solves row tail

/-- Any homogeneous system with fewer rows than DISTINCT unknown indices has
a solution nonzero on those indices. Valid over every field; no finiteness,
rank computation, Gaussian solver, or interpolation axiom is assumed. -/
theorem homogeneous_nonzero_kernel (rows : List (I→K)) (variables : List I)
    (distinct : variables.Nodup) (short : rows.length<variables.length) :
    ∃ values : I→K,(∃ i∈variables,values i≠0) ∧ ∀ row∈rows,kernelDot variables row values=0 :=
  kernel_aux rows.length rows variables rfl distinct short
end NearCompression
