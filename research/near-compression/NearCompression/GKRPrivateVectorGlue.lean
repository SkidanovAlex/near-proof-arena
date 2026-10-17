import NearCompression.GKRBooleanLaneSeparator
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Compiler-indexed scatter with zero in every unassigned private slot. -/
def gkrScatter : List (Nat × K) → Nat → K
  | [],_ => 0
  | (slot,value)::rest,i => (if i=slot then value else 0)+gkrScatter rest i

private theorem sum_append (a b : List K) : (a++b).sum=a.sum+b.sum := by
  induction a with
  | nil => simp; grind
  | cons x xs ih => simp only [List.cons_append,List.sum_cons,ih]; grind

private theorem range_delta_sum (N slot : Nat) (f : Nat → K) :
    ((List.range N).map (fun i => if i=slot then f i else 0)).sum=
      if slot<N then f slot else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ,List.map_append,sum_append,ih]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    by_cases a : slot<N <;> by_cases b : N=slot <;> by_cases c : slot<N+1 <;> simp_all <;> grind

theorem row_mle_slot_delta (m slot : Nat) (bound : slot<2^m) (value : K) (point : Nat → K) :
    genericRowMLE m (fun i => if i=slot then value else 0) point=rowEqualityWeight m point slot*value := by
  rw [←row_equality_dot]
  have same : (fun i => rowEqualityWeight m point i*(if i=slot then value else 0))=
      (fun i => if i=slot then rowEqualityWeight m point i*value else 0) := by
    funext i
    split <;> grind
  rw [same]
  unfold cubeSum
  rw [range_delta_sum,ite_eq_left bound]

/-- Functional identity for the entire compiler-indexed private vector.
No assertion of per-slot ownership is hidden in this algebraic theorem. -/
theorem gkr_scatter_functional (m : Nat) (entries : List (Nat × K))
    (bounds : ∀ entry∈entries,entry.1<2^m) (left right : Nat → K) (gamma : K) :
    gkrInputFunctional m left right gamma (gkrScatter entries)=
      (entries.map (fun entry => (rowEqualityWeight m left entry.1+gamma*rowEqualityWeight m right entry.1)*entry.2)).sum := by
  induction entries with
  | nil => simp only [gkrScatter,gkrInputFunctional,generic_row_mle_zero,List.map_nil,List.sum_nil]; grind
  | cons entry entries ih =>
    have head := bounds entry (by simp)
    have tail := ih (by intro e he; exact bounds e (by simp [he]))
    have scatter : gkrScatter (entry::entries)=(fun i => (if i=entry.1 then entry.2 else 0)+gkrScatter entries i) := by
      cases entry; rfl
    rw [scatter]
    unfold gkrInputFunctional at tail ⊢
    rw [generic_row_mle_add,generic_row_mle_add,row_mle_slot_delta _ _ head,row_mle_slot_delta _ _ head]
    simp only [List.map_cons,List.sum_cons]
    grind

/-- Every slot outside the covered support has the compiler's zero value. -/
theorem gkr_scatter_unassigned (entries : List (Nat × K)) (slot : Nat)
    (absent : slot∉entries.map Prod.fst) : gkrScatter entries slot=0 := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    have different : slot≠entry.1 := by intro eq; apply absent; simp [eq]
    have tail : slot∉entries.map Prod.fst := by intro h; apply absent; simp [h]
    cases entry
    simp only [gkrScatter,different,ite_false,ih tail]
    grind

/-- Coverage (membership) and nonoverlap (distinct keys) recover the exact
claimed value at every live slot, preventing hidden contributor sums. -/
theorem gkr_scatter_owned (entries : List (Nat × K))
    (disjoint : (entries.map Prod.fst).Nodup) (slot : Nat) (value : K)
    (covered : (slot,value)∈entries) : gkrScatter entries slot=value := by
  induction entries with
  | nil => simp at covered
  | cons entry entries ih =>
    simp only [List.map_cons,List.nodup_cons] at disjoint
    simp only [List.mem_cons] at covered
    rcases covered with same | tail
    · subst entry
      simp only [gkrScatter,ite_true,gkr_scatter_unassigned entries slot disjoint.1]
      grind
    · have different : slot≠entry.1 := by
        intro eq
        apply disjoint.1
        exact eq ▸ List.mem_map.mpr ⟨(slot,value),tail,rfl⟩
      cases entry
      simp only [gkrScatter,different,ite_false,ih disjoint.2 tail]
      grind
end NearCompression
