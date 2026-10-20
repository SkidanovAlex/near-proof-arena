import NearCompression.GeneralListCurveExtraction

/-! Exact-support exceptional event needed for weighted fold transfer.
No bound on this event is asserted: the published MCA theorem's proof is
still a separate formalization obligation. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- A mixed polynomial agrees on a sufficiently large support, but the two
source words cannot BOTH be interpolated on that very support. -/
def AffineSupportException (domain : List K) (D minimum : Nat)
    (sourceEven sourceOdd : K→K) (r : K) : Prop :=
  ∃ support : List K,support.Sublist domain ∧ minimum≤support.length ∧
    (∃ p : Poly K,p.DegLt D ∧ ∀ x∈support,
      p.eval x=(1-r)*sourceEven x+r*sourceOdd x) ∧
    ¬∃ even odd : Poly K,even.DegLt D ∧ odd.DegLt D ∧
      ∀ x∈support,sourceEven x=even.eval x ∧ sourceOdd x=odd.eval x

private theorem mass_support_cap {A : Type} (domain : List A) (weight : A→Nat)
    (event : A→Prop) [DecidablePred event] (B : Nat)
    (bounded : ∀ x∈domain,weight x≤B) :
    consistencyMass domain weight event≤(domain.filter (fun x=>decide (event x))).length*B := by
  classical
  induction domain with
  | nil => simp [consistencyMass]
  | cons x xs ih =>
    have head:=bounded x (by simp)
    have tail:=ih (fun y hy=>bounded y (by simp [hy]))
    by_cases h : event x <;> simp_all [consistencyMass] <;> grind

/-- Outside the exact-support exception, bounded integer weights preserve
ALL agreeing mass and the candidate identity. Ordinary existential correlated
agreement on some other support would not suffice for this conclusion. -/
theorem support_preserving_weighted_lift (domain : List K) (distinct : domain.Nodup)
    (D minimum T B : Nat) (enough : D≤minimum) (threshold : B*(minimum-1)<T)
    (weight : K→Nat) (bounded : ∀ x∈domain,weight x≤B)
    (sourceEven sourceOdd : K→K) (r : K)
    (outside : ¬AffineSupportException domain D minimum sourceEven sourceOdd r)
    (p : Poly K) (degree : p.DegLt D)
    (agreement : T≤consistencyMass domain weight
      (fun x=>p.eval x=(1-r)*sourceEven x+r*sourceOdd x)) :
    ∃ even odd : Poly K,even.DegLt D ∧ odd.DegLt D ∧
      T≤consistencyMass domain weight
        (fun x=>sourceEven x=even.eval x ∧ sourceOdd x=odd.eval x) ∧
      (p-(Poly.smul (1-r) even+Poly.smul r odd)).IsZero := by
  classical
  let event:=fun x=>p.eval x=(1-r)*sourceEven x+r*sourceOdd x
  let support:=domain.filter (fun x=>decide (event x))
  have cap:=mass_support_cap domain weight event B bounded
  have size : minimum≤support.length := by
    apply Classical.byContradiction
    intro small
    have short : support.length≤minimum-1 := by omega
    have scaled:=Nat.mul_le_mul_right B short
    change consistencyMass domain weight event≤support.length*B at cap
    change T≤consistencyMass domain weight event at agreement
    have comm : (minimum-1)*B=B*(minimum-1) := Nat.mul_comm _ _
    omega
  have atSupport : ∀ x∈support,event x := by
    intro x hx
    exact of_decide_eq_true (List.mem_filter.mp hx).2
  have pair : ∃ even odd : Poly K,even.DegLt D ∧ odd.DegLt D ∧
      ∀ x∈support,sourceEven x=even.eval x ∧ sourceOdd x=odd.eval x := by
    apply Classical.byContradiction
    intro missing
    exact outside ⟨support,List.filter_sublist,size,⟨p,degree,atSupport⟩,missing⟩
  obtain ⟨even,odd,de,do_,joint⟩:=pair
  refine ⟨even,odd,de,do_,?_,?_⟩
  · apply Nat.le_trans agreement
    apply consistency_mass_mono
    intro x hx mixed
    exact joint x (List.mem_filter.mpr ⟨hx,by simp only [event,mixed,decide_true]⟩)
  · apply list_curve_candidate_identity support
      (List.Sublist.nodup List.filter_sublist distinct) D (Nat.le_trans enough size)
      p even odd r degree de do_
    intro x hx
    have equal:=atSupport x hx
    have both:=joint x hx
    change p.eval x=(1-r)*sourceEven x+r*sourceOdd x at equal
    rw [both.1,both.2] at equal
    exact equal
end NearCompression
