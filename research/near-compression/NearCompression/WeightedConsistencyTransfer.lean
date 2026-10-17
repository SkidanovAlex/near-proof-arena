import NearCompression.GenericRSPairRepresentation

/-! Natural numerator representation of global-chain consistency measures.
Projection sums both fiber weights, doubling their common denominator. Gating
by the actual fold check can only remove mass. No correlated-agreement
existence theorem is assumed or claimed. -/
namespace NearCompression
open Lean.Grind

noncomputable def consistencyMass {A : Type} (domain : List A) (weight : A → Nat)
    (event : A → Prop) : Nat := by
  classical
  exact (domain.map (fun x => if event x then weight x else 0)).sum

theorem consistency_mass_mono {A : Type} (domain : List A) (weight : A → Nat)
    (p q : A → Prop) (implies : ∀ x∈domain,p x → q x) :
    consistencyMass domain weight p≤consistencyMass domain weight q := by
  classical
  induction domain with
  | nil => simp [consistencyMass]
  | cons x xs ih =>
    have tail := ih (fun y hy => implies y (by simp [hy]))
    have head := implies x (by simp)
    simp only [consistencyMass,List.map_cons,List.sum_cons] at tail ⊢
    by_cases hp : p x <;> by_cases hq : q x <;> simp_all <;> omega

/-- The next oracle is allowed to depend on the challenge. The fixed projected
weight and the fold oracle do not depend on that next-oracle choice. -/
theorem consistency_gated_agreement {A K : Type} [DecidableEq K] (domain : List A) (weight : A → Nat)
    (fold next candidate : A → K) :
    consistencyMass domain (fun x => if next x=fold x then weight x else 0)
      (fun x => next x=candidate x) ≤
    consistencyMass domain weight (fun x => fold x=candidate x) := by
  classical
  induction domain with
  | nil => simp [consistencyMass]
  | cons x xs ih =>
    simp only [consistencyMass,List.map_cons,List.sum_cons] at ih ⊢
    by_cases check : next x=fold x <;> by_cases close : next x=candidate x <;>
      by_cases target : fold x=candidate x <;> simp_all <;> omega

/-- Exact numerator conservation on the inverse image of a fiber set.
For old denominator B and domain size 2N, the new denominator is 2B and
size N, so the normalized measures also coincide. -/
theorem consistency_projected_mass {K : Type} [Neg K] (reps : List K)
    (weight : K → Nat) (selected : K → Prop)
    (symmetric : ∀ x∈reps,selected (-x)↔selected x) :
    consistencyMass (reps.flatMap (fun x => [x,-x])) weight selected =
    consistencyMass reps (fun x => weight x+weight (-x)) selected := by
  classical
  induction reps with
  | nil => simp [consistencyMass]
  | cons x xs ih =>
    have tail := ih (fun y hy => symmetric y (by simp [hy]))
    have head := symmetric x (by simp)
    simp only [consistencyMass,List.flatMap_cons,List.cons_append,List.nil_append,
      List.map_cons,List.sum_cons] at tail ⊢
    rw [tail]
    by_cases h : selected x <;> simp_all <;> omega

/-- Joint decoded-coordinate agreement lifts to BOTH original source values,
so its entire projected mass survives in the previous candidate relation. -/
theorem consistency_pair_pullback {K : Type} [Field K] (reps : List K)
    (weight : K → Nat) (source candidate : K → K) (joint : K → Prop)
    (recover : ∀ x∈reps,joint x → source x=candidate x ∧ source (-x)=candidate (-x)) :
    consistencyMass reps (fun x => weight x+weight (-x)) joint ≤
    consistencyMass (reps.flatMap (fun x => [x,-x])) weight
      (fun x => source x=candidate x) := by
  classical
  induction reps with
  | nil => simp [consistencyMass]
  | cons x xs ih =>
    have tail := ih (fun y hy => recover y (by simp [hy]))
    have head := recover x (by simp)
    simp only [consistencyMass,List.flatMap_cons,List.cons_append,List.nil_append,
      List.map_cons,List.sum_cons] at tail ⊢
    by_cases hj : joint x <;> by_cases hp : source x=candidate x <;>
      by_cases hm : source (-x)=candidate (-x) <;> simp_all <;> omega

theorem consistency_projected_bound {K : Type} [Neg K] (weight : K → Nat)
    (B : Nat) (x : K) (left : weight x≤B) (right : weight (-x)≤B) :
    weight x+weight (-x)≤2*B := by omega

end NearCompression
