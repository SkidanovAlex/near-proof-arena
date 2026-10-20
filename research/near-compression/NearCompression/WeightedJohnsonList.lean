import NearCompression.FiniteRSJohnsonList
import NearCompression.WeightedThreeCandidate

/-! Finite weighted Johnson counting for global-chain numerator weights.
Replication is a proof device, not a proposed enumeration or decoder. This
bounds fixed candidate families, not correlated-agreement transfer. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]
attribute [local instance] Classical.propDecidable

private theorem replicate_count {A : Type} (n : Nat) (x : A) (event : A → Prop) :
    count (List.replicate n x) event=(if event x then n else 0) := by
  classical
  induction n with
  | zero => simp [count]
  | succ n ih =>
    simp only [List.replicate_succ,count,List.countP_cons] at ih ⊢
    by_cases h : event x <;> simp_all

private theorem expanded_count {A : Type} (domain : List A) (weight : A → Nat)
    (event : A → Prop) :
    count (domain.flatMap (fun x => List.replicate (weight x) x)) event=
      consistencyMass domain weight event := by
  classical
  induction domain with
  | nil => simp [count,consistencyMass]
  | cons x xs ih =>
    simp only [List.flatMap_cons,count,List.countP_append,consistencyMass,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih]
    change count (List.replicate (weight x) x) event+_= _
    rw [replicate_count]

/-- Integer weights reduce exactly to finite agreement counting, including
zero weights and repeated domain entries. -/
theorem weighted_agreement_list_bound {A B : Type} (domain : List A)
    (weight : A → Nat) (family : List B) (rel : B → A → Prop) (T overlap : Nat)
    (close : ∀ b∈family,T≤consistencyMass domain weight (rel b))
    (pairs : family.Pairwise (fun a b =>
      consistencyMass domain weight (fun x => rel a x ∧ rel b x)≤overlap)) :
    family.length*T*T≤(domain.map weight).sum*(domain.map weight).sum+
      family.length*(domain.map weight).sum*overlap := by
  have bound := finite_agreement_list_bound
    (domain.flatMap (fun x => List.replicate (weight x) x)) family rel T overlap
    (by intro b hb; rw [expanded_count]; exact close b hb)
    (by simpa only [expanded_count] using pairs)
  simpa only [List.length_flatMap,List.length_replicate] using bound

/-- Arbitrary bounded natural weights, with the actual surviving total mass. -/
theorem weighted_rs_johnson_list_bound (domain : List K) (distinct : domain.Nodup)
    (weight : K → Nat) (B D T : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (family : List (Poly K)) (received : K → K)
    (degrees : ∀ p∈family,p.DegLt D)
    (close : ∀ p∈family,T≤consistencyMass domain weight (fun x => p.eval x=received x))
    (different : family.Pairwise (fun a b => ¬(a-b).IsZero)) :
    family.length*T*T≤(domain.map weight).sum*(domain.map weight).sum+
      family.length*(domain.map weight).sum*(B*(D-1)) := by
  apply weighted_agreement_list_bound domain weight family
    (fun p x => p.eval x=received x) T (B*(D-1)) close
  apply List.Pairwise.imp_of_mem ?_ different
  intro a b ha hb ne
  apply Nat.le_trans (consistency_mass_mono domain weight _ _ (by
    intro x hx h; exact h.1.trans h.2.symm))
  exact weighted_distinct_polynomial_agreement domain distinct weight B D bounded
    a b (degrees a ha) (degrees b hb) ne

/-- A joint even/odd curve list has the same overlap bound: two different
pairs differ in at least one polynomial component. No squared list penalty. -/
theorem weighted_curve_johnson_list_bound (domain : List K) (distinct : domain.Nodup)
    (weight : K → Nat) (B D T : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (family : List (Poly K × Poly K)) (sourceEven sourceOdd : K → K)
    (degrees : ∀ p∈family,p.1.DegLt D ∧ p.2.DegLt D)
    (close : ∀ p∈family,T≤consistencyMass domain weight
      (fun x => sourceEven x=p.1.eval x ∧ sourceOdd x=p.2.eval x))
    (different : family.Pairwise (fun a b => ¬(a.1-b.1).IsZero ∨ ¬(a.2-b.2).IsZero)) :
    family.length*T*T≤(domain.map weight).sum*(domain.map weight).sum+
      family.length*(domain.map weight).sum*(B*(D-1)) := by
  apply weighted_agreement_list_bound domain weight family
    (fun p x => sourceEven x=p.1.eval x ∧ sourceOdd x=p.2.eval x) T (B*(D-1)) close
  apply List.Pairwise.imp_of_mem ?_ different
  intro a b ha hb ne
  cases ne with
  | inl h =>
    apply Nat.le_trans (consistency_mass_mono domain weight _ _ (by
      intro x hx eq; exact eq.1.1.symm.trans eq.2.1))
    exact weighted_distinct_polynomial_agreement domain distinct weight B D bounded
      a.1 b.1 (degrees a ha).1 (degrees b hb).1 h
  | inr h =>
    apply Nat.le_trans (consistency_mass_mono domain weight _ _ (by
      intro x hx eq; exact eq.1.2.symm.trans eq.2.2))
    exact weighted_distinct_polynomial_agreement domain distinct weight B D bounded
      a.2 b.2 (degrees a ha).2 (degrees b hb).2 h

/-- Positive-gap form suitable for the two-roots-per-curve extraction penalty.
The gap uses surviving mass M and the history-dependent point cap B. -/
theorem weighted_curve_johnson_gap_bound (domain : List K) (distinct : domain.Nodup)
    (weight : K → Nat) (B D T : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (family : List (Poly K × Poly K)) (sourceEven sourceOdd : K → K)
    (degrees : ∀ p∈family,p.1.DegLt D ∧ p.2.DegLt D)
    (close : ∀ p∈family,T≤consistencyMass domain weight
      (fun x => sourceEven x=p.1.eval x ∧ sourceOdd x=p.2.eval x))
    (different : family.Pairwise (fun a b => ¬(a.1-b.1).IsZero ∨ ¬(a.2-b.2).IsZero))
    (gap : (domain.map weight).sum*(B*(D-1))≤T*T) :
    family.length*(T*T-(domain.map weight).sum*(B*(D-1)))≤
      (domain.map weight).sum*(domain.map weight).sum := by
  have bound := weighted_curve_johnson_list_bound domain distinct weight B D T bounded
    family sourceEven sourceOdd degrees close different
  have eq := Nat.sub_add_cancel gap
  have rearranged : family.length*(T*T)≤(domain.map weight).sum*(domain.map weight).sum+
      family.length*((domain.map weight).sum*(B*(D-1))) := by
    simpa only [Nat.mul_assoc] using bound
  rw [←eq,Nat.mul_add] at rearranged
  exact Nat.le_of_add_le_add_right rearranged

end NearCompression
