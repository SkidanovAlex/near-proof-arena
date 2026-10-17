import NearCompression.FiniteRSUniqueDecoding
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]
attribute [local instance] Classical.propDecidable

private theorem sum_zero {A : Type} (xs : List A) : (xs.map (fun _=>0 : A→Nat)).sum=0 := by
  induction xs <;> simp_all


private theorem twice (a b : Nat) : 2*a*b≤a*a+b*b := by
  by_cases h : a≤b
  · have eq : b=a+(b-a) := by omega
    rw [eq]
    grind
  · have eq : a=b+(a-b) := by omega
    rw [eq]
    grind
private theorem cross (xs : List Nat) (a : Nat) :
    2*a*xs.sum≤xs.length*a*a+(xs.map (fun x=>x*x)).sum := by
  induction xs with
  | nil=>simp
  | cons b xs ih=>
    have h:=twice a b
    simp only [List.sum_cons,List.length_cons,List.map_cons]
    grind
private theorem cauchy (xs : List Nat) : xs.sum*xs.sum≤xs.length*(xs.map (fun x=>x*x)).sum := by
  induction xs with
  | nil=>simp
  | cons a xs ih=>
    have h:=cross xs a
    simp only [List.sum_cons,List.length_cons,List.map_cons]
    grind

private noncomputable def mass {A B : Type} (domain : List A) (family : List B) (rel : B→A→Prop) : Nat :=
  (domain.map (fun x=>count family (fun b=>rel b x))).sum

private theorem mass_cons {A B : Type} (domain : List A) (family : List B) (a : B) (rel : B→A→Prop) :
    mass domain (a::family) rel=count domain (rel a)+mass domain family rel := by
  classical
  induction domain with
  | nil=>simp [mass,count]
  | cons x xs ih=>
    simp only [mass,List.map_cons,List.sum_cons,count,List.countP_cons] at ih ⊢
    by_cases h : rel a x <;> simp_all <;> grind

private theorem cross_cons {A B : Type} (domain : List A) (family : List B) (a b : B) (rel : B→A→Prop) :
    (domain.map (fun x=>if rel a x then count (b::family) (fun c=>rel c x) else 0)).sum=
    count domain (fun x=>rel a x ∧ rel b x)+
      (domain.map (fun x=>if rel a x then count family (fun c=>rel c x) else 0)).sum := by
  classical
  induction domain with
  | nil=>simp [count]
  | cons x xs ih=>
    simp only [List.map_cons,List.sum_cons,count,List.countP_cons] at ih ⊢
    by_cases ha : rel a x <;> by_cases hb : rel b x <;> simp_all <;> grind

private theorem cross_bound {A B : Type} (domain : List A) (family : List B) (a : B) (rel : B→A→Prop)
    (K : Nat) (pairs : ∀ b∈family,count domain (fun x=>rel a x ∧ rel b x)≤K) :
    (domain.map (fun x=>if rel a x then count family (fun b=>rel b x) else 0)).sum≤family.length*K := by
  classical
  induction family with
  | nil=>simp [count,sum_zero]
  | cons b bs ih=>
    rw [cross_cons]
    have head:=pairs b (by simp)
    have tail:=ih (fun c hc=>pairs c (by simp [hc]))
    simp only [List.length_cons]
    grind

private theorem square_cons {A B : Type} (domain : List A) (family : List B) (a : B) (rel : B→A→Prop) :
    (domain.map (fun x=>(count (a::family) (fun b=>rel b x))^2)).sum=
      (domain.map (fun x=>(count family (fun b=>rel b x))^2)).sum+
      2*(domain.map (fun x=>if rel a x then count family (fun b=>rel b x) else 0)).sum+
      count domain (rel a) := by
  classical
  induction domain with
  | nil=>simp [count]
  | cons x xs ih=>
    simp only [List.map_cons,List.sum_cons,count,List.countP_cons] at ih ⊢
    by_cases h : rel a x <;> simp_all <;> grind

private theorem square_bound {A B : Type} (domain : List A) (family : List B) (rel : B→A→Prop)
    (K : Nat) (pairs : family.Pairwise (fun a b=>count domain (fun x=>rel a x ∧ rel b x)≤K)) :
    (domain.map (fun x=>(count family (fun b=>rel b x))^2)).sum≤
      family.length*domain.length+family.length*family.length*K := by
  classical
  induction family with
  | nil=>simp [count,sum_zero]
  | cons a bs ih=>
    have facts:=List.pairwise_cons.mp pairs
    have tail:=ih facts.2
    have cross:=cross_bound domain bs a rel K facts.1
    have maximum : count domain (rel a)≤domain.length := List.countP_le_length
    rw [square_cons]
    simp only [List.length_cons]
    grind

/-- Conservative finite Johnson bound for a family of agreement sets. A
positive gap T^2-N*K yields a list bound; no decoding or finiteness axiom. -/
theorem finite_agreement_list_bound {A B : Type} (domain : List A) (family : List B)
    (rel : B→A→Prop) (T K : Nat)
    (close : ∀ b∈family,T≤count domain (rel b))
    (pairs : family.Pairwise (fun a b=>count domain (fun x=>rel a x ∧ rel b x)≤K)) :
    family.length*T*T≤domain.length*domain.length+family.length*domain.length*K := by
  classical
  have lower : family.length*T≤mass domain family rel := by
    induction family with
    | nil=>simp [mass,count]
    | cons a bs ih=>
      rw [mass_cons]
      have head:=close a (by simp)
      have tail:=ih (fun b hb=>close b (by simp [hb])) (List.pairwise_cons.mp pairs).2
      simp only [List.length_cons]
      grind
  have lowerSq:=Nat.mul_le_mul lower lower
  have cauchyBound:=cauchy (domain.map (fun x=>count family (fun b=>rel b x)))
  simp only [List.length_map,List.map_map,Function.comp_def] at cauchyBound
  have upper:=square_bound domain family rel K pairs
  have scaledUpper:=Nat.mul_le_mul_left domain.length upper
  have squares : mass domain family rel*mass domain family rel≤
      domain.length*(domain.map (fun x=>(count family (fun b=>rel b x))^2)).sum := by
    simpa only [mass,Nat.pow_two] using cauchyBound
  by_cases positive : 0<family.length
  · have scaled : family.length*(family.length*T*T)≤
        family.length*(domain.length*domain.length+family.length*domain.length*K) := by
      grind
    exact Nat.le_of_mul_le_mul_left scaled positive
  · have zero : family.length=0 := by omega
    simp [zero]

/-- Polynomial version: distinct coefficient functions agree in at most D-1
positions. The received word is arbitrary and the family is fixed. -/
theorem finite_rs_johnson_list_bound (domain : List K) (distinct : domain.Nodup)
    (family : List (Poly K)) (received : K→K) (D T : Nat)
    (degrees : ∀ p∈family,p.DegLt D)
    (close : ∀ p∈family,T≤count domain (fun x=>p.eval x=received x))
    (different : family.Pairwise (fun a b=>¬(a-b).IsZero)) :
    family.length*T*T≤domain.length*domain.length+family.length*domain.length*(D-1) := by
  apply finite_agreement_list_bound domain family (fun p x=>p.eval x=received x) T (D-1) close
  apply List.Pairwise.imp_of_mem ?_ different
  intro a b ha hb ne
  have roots:=finite_rs_distinct_agreement domain distinct a b D (degrees a ha) (degrees b hb) ne
  have overlap : count domain (fun x=>a.eval x=received x ∧ b.eval x=received x)≤
      count domain (fun x=>a.eval x=b.eval x) := by
    apply count_mono
    intro x h
    exact h.1.trans h.2.symm
  omega

/-- Positive Johnson gap gives an explicit bound on any finite candidate list.
This conservative form is L*(T^2-N*(D-1)) <= N^2. -/
theorem finite_rs_johnson_gap_bound (domain : List K) (distinct : domain.Nodup)
    (family : List (Poly K)) (received : K→K) (D T : Nat)
    (degrees : ∀ p∈family,p.DegLt D)
    (close : ∀ p∈family,T≤count domain (fun x=>p.eval x=received x))
    (different : family.Pairwise (fun a b=>¬(a-b).IsZero))
    (gap : domain.length*(D-1)≤T*T) :
    family.length*(T*T-domain.length*(D-1))≤domain.length*domain.length := by
  have bound:=finite_rs_johnson_list_bound domain distinct family received D T degrees close different
  have eq:=Nat.sub_add_cancel gap
  have rearranged : family.length*(T*T)≤domain.length*domain.length+
      family.length*(domain.length*(D-1)) := by
    simpa only [Nat.mul_assoc] using bound
  rw [←eq,Nat.mul_add] at rearranged
  exact Nat.le_of_add_le_add_right rearranged

end NearCompression
