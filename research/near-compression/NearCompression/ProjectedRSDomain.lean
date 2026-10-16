import NearCompression.GlobalChainGeometry
import NearCompression.GKRProjectedRepresentative
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def naturalRSDomain (omega : K) (N : Nat) : List K := (List.range N).map (fun i => omega^i)

/-- Natural cyclic index rotation, before any field interpretation. -/
theorem range_rotation_permutation (N shift : Nat) (bound : shift≤N) :
    ((List.range N).map (fun i => (shift+i)%N)).Perm (List.range N) := by
  have split : N=(N-shift)+shift := by omega
  have left : (List.range (N-shift)).map (fun i => (shift+i)%N)=
      (List.range (N-shift)).map (fun i => shift+i) := by
    apply List.map_congr_left
    intro i hi
    exact Nat.mod_eq_of_lt (by have h := List.mem_range.mp hi; omega)
  have right : (List.range shift).map (fun i => (shift+(N-shift+i))%N)=List.range shift := by
    have same : (List.range shift).map (fun i => (shift+(N-shift+i))%N)=
        (List.range shift).map (fun i => i) := by
      apply List.map_congr_left
      intro i hi
      have h := List.mem_range.mp hi
      have eq : shift+(N-shift+i)=N+i := by omega
      rw [eq,Nat.add_mod,Nat.mod_self,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]
    simpa using same
  have rangeSplit : List.range N=List.range (N-shift)++(List.range shift).map (fun i => N-shift+i) := by
    conv => lhs; rw [split,List.range_add]
  rw [rangeSplit,List.map_append,List.map_map]
  rw [←rangeSplit]
  change (((List.range (N-shift)).map (fun i => (shift+i)%N))++
    ((List.range shift).map (fun i => (shift+(N-shift+i))%N))).Perm (List.range N)
  rw [left,right]
  have split2 : N=shift+(N-shift) := by omega
  conv => rhs; rw [split2,List.range_add]
  exact List.perm_append_comm

/-- Rotation by ANY domain power is a permutation of the natural FFT domain;
no honest polynomial or oracle appears in this geometry theorem. -/
theorem natural_rs_rotation (omega : K) (N shift : Nat) (bound : shift≤N)
    (period : omega^N=1) :
    ((naturalRSDomain omega N).map (fun x => omega^shift*x)).Perm (naturalRSDomain omega N) := by
  have perm := (range_rotation_permutation N shift bound).map (fun i => omega^i)
  simp only [List.map_map,Function.comp_def] at perm
  have eq : (fun i => omega^((shift+i)%N))=(fun i => omega^shift*omega^i) := by
    funext i
    rw [global_chain_pow_mod omega N _ period,Semiring.pow_add]
  rw [eq] at perm
  simpa only [naturalRSDomain,List.map_map,Function.comp_def] using perm

/-- Exact order of the per-branch symmetry root, derived from one original
root-order certificate. N=L*step, so z=omega^step. -/
theorem projected_root_order (omega : K) (L step : Nat) (stepPositive : 0<step)
    (rootOrder : ∀ j,omega^j=1 ↔ L*step∣j) :
    (omega^step)^L=1 ∧ (∀ j,¬L∣j → (omega^step)^j≠1) := by
  constructor
  · rw [←pow_mul_eq]
    apply (rootOrder _).mpr
    rw [Nat.mul_comm step L]
    exact Nat.dvd_refl _
  · intro j notDiv equality
    rw [←pow_mul_eq] at equality
    have divides := (rootOrder _).mp equality
    have h : step*L∣step*j := by simpa only [Nat.mul_comm L step] using divides
    exact notDiv (Nat.dvd_of_mul_dvd_mul_left stepPositive h)

private theorem map_nodup_on {A B : Type} (xs : List A) (f : A → B)
    (distinct : xs.Nodup) (injective : ∀ a∈xs,∀ b∈xs,f a=f b → a=b) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.nodup_cons] at distinct
    rw [List.map_cons,List.nodup_cons]
    constructor
    · intro member
      obtain ⟨b,hb,eq⟩ := List.mem_map.mp member
      have same := injective b (by simp [hb]) a (by simp) eq
      subst b
      exact distinct.1 hb
    · exact ih distinct.2 (by intro a ha b hb eq; exact injective a (by simp [ha]) b (by simp [hb]) eq)

/-- The same single primitive-root certificate proves distinctness of the
actual natural-order evaluation domain. -/
theorem natural_rs_distinct (omega : K) (N : Nat)
    (rootOrder : ∀ j,omega^j=1 ↔ N∣j) : (naturalRSDomain omega N).Nodup := by
  apply map_nodup_on _ _ List.nodup_range
  intro a ha b hb equal
  have ba := List.mem_range.mp ha
  have bb := List.mem_range.mp hb
  have period := (rootOrder N).mpr (Nat.dvd_refl N)
  have ordered (i j : Nat) (hi : i<N) (hj : j<N) (order : i≤j)
      (same : omega^i=omega^j) : i=j := by
    have inverse : omega^i*omega^(N-i)=1 := by
      rw [←Semiring.pow_add,show i+(N-i)=N by omega,period]
    have shifted : omega^i*omega^(j-i)=omega^j := by
      rw [←Semiring.pow_add,show i+(j-i)=j by omega]
    have one : omega^(j-i)=1 := by grind
    have zero := Nat.eq_zero_of_dvd_of_lt ((rootOrder _).mp one) (show j-i<N by omega)
    omega
  by_cases order : a≤b
  · exact ordered a b ba bb order equal
  · exact (ordered b a bb ba (by omega) equal.symm).symm

/-- All per-branch finite-domain certificates follow from the original
root's order, N=L*step. This includes L=1, whose rotation is the identity. -/
theorem projected_rs_domain_certificates (omega : K) (L step : Nat)
    (positiveL : 0<L) (positiveStep : 0<step)
    (rootOrder : ∀ j,omega^j=1 ↔ L*step∣j) :
    (naturalRSDomain omega (L*step)).Nodup ∧
    (omega^step)^L=1 ∧
    (∀ j,¬L∣j → (omega^step)^j≠1) ∧
    ((naturalRSDomain omega (L*step)).map (fun x => omega^step*x)).Perm
      (naturalRSDomain omega (L*step)) := by
  have order := projected_root_order omega L step positiveStep rootOrder
  refine ⟨natural_rs_distinct omega (L*step) rootOrder,order.1,order.2,?_⟩
  apply natural_rs_rotation omega (L*step) step
  · have h := Nat.mul_le_mul_right step positiveL
    simpa using h
  · exact (rootOrder _).mpr (Nat.dvd_refl _)

/-- Actual rate-1/4 natural RS domain: one original root-order certificate
replaces all per-branch order, distinctness and permutation premises. -/
theorem natural_rs_joint_projected_recovery (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (geometry : CanonicalLaneSelectors layout metadata)
    (L d T : Nat) (positiveL : 0<L) (positiveD : 0<d)
    (omega : K) (rootOrder : ∀ j,omega^j=1 ↔ L*(4*d)∣j)
    (sources : List (K → K)) (polys : List (Poly K))
    (sourceShape : sources.length=metadata.length) (polyShape : polys.length=metadata.length)
    (representative : JointBetaRepresentative (naturalRSDomain omega (L*(4*d))) (fun _ => 1)
      (heterogeneousJointDimension layout) (L*d) T
      (metadata.map (heterogeneousJointBeta layout)) sources polys)
    (i : Nat) (hi : i<metadata.length)
    (source : K → K) (projection : ∀ x,sources[i] x=source (x^L))
    (separation : (L*(4*d)-T)+(L*(4*d)-T)+L*d≤L*(4*d)) :
    let recovered := recoverProjectedPolynomial L d polys[i]
    recovered.DegLt d ∧
      (∀ j,polys[i].coeff j=if L∣j then recovered.coeff (j/L) else 0) := by
  have cert := projected_rs_domain_certificates omega L (4*d) positiveL (by omega) rootOrder
  apply joint_representative_projected_recovery layout metadata valid geometry
    (naturalRSDomain omega (L*(4*d))) cert.1 (L*d) T sources polys sourceShape polyShape
    representative i hi L d positiveL rfl source projection (omega^(4*d)) cert.2.1 cert.2.2.1 cert.2.2.2
  simpa only [naturalRSDomain,List.length_map,List.length_range] using separation
end NearCompression
