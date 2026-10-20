import NearCompression.DeterminantRowPermutations

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Row-vector form used to expand finite combinations; linked to the existing determinant below. -/
def rowVectorDeterminant : List (Nat→K) → List Nat → K
  | [], _ => 1
  | row::rows, columns => determinantCofactorFold columns
      (fun c rest=>row c*rowVectorDeterminant rows rest)

private theorem fold_congr (cs : List Nat) (f g : Nat→List Nat→K)
    (same : ∀ c rest,f c rest=g c rest) : determinantCofactorFold cs f=determinantCofactorFold cs g := by
  have eq : f=g := by funext c rest;exact same c rest
  rw [eq]

private theorem fold_zero (cs : List Nat) (f : Nat→List Nat→K)
    (zero : ∀ c∈cs,∀ rest,f c rest=0) : determinantCofactorFold cs f=0 := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    rw [determinantCofactorFold,zero c (by simp),ih _ (fun d hd rest=>zero d (by simp [hd]) (c::rest))]
    grind

/-- The vector-list determinant is exactly the previously defined minor. -/
theorem scalar_minor_row_vectors (M : Nat→Nat→K) (rows columns : List Nat) :
    scalarMinorDeterminant M rows columns=rowVectorDeterminant (rows.map M) columns := by
  induction rows generalizing columns with
  | nil => rfl
  | cons row rows ih =>
    rw [scalar_minor_cofactor_fold]
    change _=determinantCofactorFold columns (fun c rest=>M row c*rowVectorDeterminant (rows.map M) rest)
    apply fold_congr
    intro c rest
    rw [ih]

private theorem vector_slot_linear (before after : List (Nat→K)) (u v : Nat→K) (a b : K) (columns : List Nat) :
    rowVectorDeterminant (before++(fun j=>a*u j+b*v j)::after) columns=
      a*rowVectorDeterminant (before++u::after) columns+b*rowVectorDeterminant (before++v::after) columns := by
  induction before generalizing columns with
  | nil =>
    simp only [List.nil_append,rowVectorDeterminant]
    have same:=fold_congr columns
      (fun c rest=>(a*u c+b*v c)*rowVectorDeterminant after rest)
      (fun c rest=>a*(u c*rowVectorDeterminant after rest)+b*(v c*rowVectorDeterminant after rest))
      (fun c rest=>by grind)
    rw [same,determinant_cofactor_fold_linear]
  | cons row before ih =>
    simp only [List.cons_append,rowVectorDeterminant]
    have same:=fold_congr columns
      (fun c rest=>row c*rowVectorDeterminant (before++(fun j=>a*u j+b*v j)::after) rest)
      (fun c rest=>a*(row c*rowVectorDeterminant (before++u::after) rest)+
        b*(row c*rowVectorDeterminant (before++v::after) rest))
      (fun c rest=>by rw [ih];grind)
    rw [same,determinant_cofactor_fold_linear]

private theorem vector_zero_slot (before after : List (Nat→K)) (columns : List Nat) :
    rowVectorDeterminant (before++(fun _=>0)::after) columns=0 := by
  have linear:=vector_slot_linear before after (fun _=>0) (fun _=>0) 0 0 columns
  have same : (fun _ : Nat=>(0:K)*0+0*0)=(fun _=>0) := by funext j;grind
  rw [same] at linear
  grind

private theorem vector_slot_sum (before after : List (Nat→K)) (indices columns : List Nat)
    (weights : Nat→K) (M : Nat→Nat→K) :
    rowVectorDeterminant (before++(fun j=>kernelDot indices weights (fun i=>M i j))::after) columns=
      kernelDot indices weights (fun i=>rowVectorDeterminant (before++M i::after) columns) := by
  induction indices with
  | nil => exact vector_zero_slot before after columns
  | cons i indices ih =>
    have linear:=vector_slot_linear before after (M i) (fun j=>kernelDot indices weights (fun k=>M k j)) (weights i) 1 columns
    have same : (fun j=>weights i*M i j+(1:K)*kernelDot indices weights (fun k=>M k j))=
      (fun j=>kernelDot (i::indices) weights (fun k=>M k j)) := by funext j;rw [kernelDot];grind
    rw [same,ih] at linear
    change _=weights i*rowVectorDeterminant (before++M i::after) columns+
      kernelDot indices weights (fun k=>rowVectorDeterminant (before++M k::after) columns)
    grind

private theorem dot_zero (xs : List Nat) (weights f : Nat→K) (zero : ∀ i∈xs,f i=0) :
    kernelDot xs weights f=0 := by
  induction xs with
  | nil => rfl
  | cons i xs ih => rw [kernelDot,zero i (by simp),ih (fun j hj=>zero j (by simp [hj]))];grind

private theorem combinations_zero (M : Nat→Nat→K) (base labels columns : List Nat)
    (weights : Nat→Nat→K) (before : List (Nat→K))
    (zero : ∀ selected : List Nat,selected.length=labels.length → (∀ i∈selected,i∈base) →
      rowVectorDeterminant (before++selected.map M) columns=0) :
    rowVectorDeterminant (before++labels.map (fun r j=>kernelDot base (weights r) (fun i=>M i j))) columns=0 := by
  induction labels generalizing before with
  | nil => exact zero [] rfl (by simp)
  | cons r labels ih =>
    let row:=fun j=>kernelDot base (weights r) (fun i=>M i j)
    have tail : ∀ selected : List Nat,selected.length=labels.length → (∀ i∈selected,i∈base) →
        rowVectorDeterminant ((before++[row])++selected.map M) columns=0 := by
      intro selected length subset
      simp only [List.append_assoc,List.singleton_append]
      rw [vector_slot_sum]
      apply dot_zero
      intro i member
      have result:=zero (i::selected) (by simp [length]) (by
        intro j hj;simp only [List.mem_cons] at hj;rcases hj with eq|inside
        · subst j;exact member
        · exact subset j inside)
      exact result
    have result:=ih (before++[row]) tail
    simpa only [List.map_cons,List.append_assoc,List.singleton_append] using result

/-- A singular full row family makes every equally large family of linear
combinations singular. This is the determinant side of the spanning argument. -/
theorem scalar_minor_row_span_zero (M : Nat→Nat→K) (rows columns : List Nat)
    (distinct : rows.Nodup) (weights : Nat→Nat→K)
    (zero : scalarMinorDeterminant M rows columns=0) :
    scalarMinorDeterminant (fun r j=>kernelDot rows (weights r) (fun i=>M i j)) rows columns=0 := by
  rw [scalar_minor_row_vectors]
  apply combinations_zero M rows rows columns weights []
  intro selected length subset
  rw [List.nil_append,←scalar_minor_row_vectors]
  exact scalar_minor_selected_rows_zero M rows selected columns distinct length subset zero

/-- The ordered identity minor has determinant one. -/
theorem scalar_minor_identity (rows : List Nat) (distinct : rows.Nodup) :
    scalarMinorDeterminant (fun i j=>if i=j then (1:K) else 0) rows rows=1 := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    have nd:=List.nodup_cons.mp distinct
    rw [scalar_minor_cofactor_fold,determinantCofactorFold]
    have zero : determinantCofactorFold rows (fun c rest=>(if r=c then (1:K) else 0)*
        scalarMinorDeterminant (fun i j=>if i=j then (1:K) else 0) rows (r::rest))=0 := by
      apply fold_zero
      intro c member rest
      have different : r≠c := by intro eq;subst c;exact nd.1 member
      rw [ite_eq_right different];grind
    rw [zero,ite_eq_left rfl,ih nd.2]
    grind

/-- A row inverse producing identity forces the determinant nonzero.
This closes the nonzeroness implication without assuming a determinant law. -/
theorem scalar_minor_nonzero_of_row_inverse (M weights : Nat→Nat→K) (rows : List Nat)
    (distinct : rows.Nodup)
    (inverse : ∀ r∈rows,∀ j,kernelDot rows (weights r) (fun i=>M i j)=if r=j then 1 else 0) :
    scalarMinorDeterminant M rows rows≠0 := by
  intro zero
  have transformed:=scalar_minor_row_span_zero M rows rows distinct weights zero
  have same:=scalar_minor_rows_congr
    (fun r j=>kernelDot rows (weights r) (fun i=>M i j))
    (fun r j=>if r=j then (1:K) else 0) rows rows inverse
  rw [same,scalar_minor_identity rows distinct] at transformed
  exact Field.zero_ne_one transformed.symm
end NearCompression
