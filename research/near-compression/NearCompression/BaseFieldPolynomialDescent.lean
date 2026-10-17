import NearCompression.FiniteRSUniqueDecoding
import ZkFormal.Algebra.Fp8
import NearCompression.RecoveredSymbolicEnvironment
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

def projectPolynomial {K : Type} (project : K → K) (p : Poly K) : Poly K :=
  ⟨p.coeffs.map project⟩

theorem project_polynomial_coefficient {K : Type} [Field K]
    (project : K → K) (zero : project 0=0) (p : Poly K) (i : Nat) :
    (projectPolynomial project p).coeff i=project (p.coeff i) := by
  rcases p with ⟨cs⟩
  unfold projectPolynomial Poly.coeff
  induction cs generalizing i with
  | nil => simpa using zero.symm
  | cons c cs ih => cases i <;> simp_all

theorem project_polynomial_evaluation {K : Type} [Field K]
    (project : K → K) (zero : project 0=0)
    (additive : ∀ a b,project (a+b)=project a+project b)
    (x : K) (scalar : ∀ a,project (x*a)=x*project a) (p : Poly K) :
    (projectPolynomial project p).eval x=project (p.eval x) := by
  rcases p with ⟨cs⟩
  unfold projectPolynomial Poly.eval
  induction cs with
  | nil => simpa only [List.map_nil,Poly.evalL] using zero.symm
  | cons c cs ih => simp only [List.map_cons,Poly.evalL,additive,scalar,ih]

/-- Agreement at D distinct points with projection-fixed oracle values forces
every coefficient of a degree-<D polynomial to be projection-fixed. The
projection need only commute with multiplication by domain points. -/
theorem polynomial_descent_from_agreement {K : Type} [Field K]
    (domain : List K) (distinct : domain.Nodup) (received : K → K)
    (project : K → K) (zero : project 0=0)
    (additive : ∀ a b,project (a+b)=project a+project b)
    (scalar : ∀ x∈domain,∀ a,project (x*a)=x*project a)
    (fixed : ∀ x∈domain,project (received x)=received x)
    (p : Poly K) (D : Nat) (degree : p.DegLt D)
    (agreement : D≤count domain (fun x => received x=p.eval x)) :
    ∀ i,project (p.coeff i)=p.coeff i := by
  let q := projectPolynomial project p
  have qdegree : q.DegLt D := by
    intro i hi
    rw [project_polynomial_coefficient project zero p i,degree i hi,zero]
  have agrees : count domain (fun x => received x=p.eval x)≤count domain (fun x => p.eval x=q.eval x) := by
    apply count_mono_mem
    intro x hx h
    change p.eval x=(projectPolynomial project p).eval x
    rw [project_polynomial_evaluation project zero additive x (scalar x hx) p,←h,fixed x hx]
  have same : (p-q).IsZero := by
    apply Classical.byContradiction
    intro different
    have roots := finite_rs_distinct_agreement domain distinct p q D degree qdegree different
    omega
  intro i
  have h := same i
  rw [Poly.coeff_sub,project_polynomial_coefficient project zero p i] at h
  grind

/-- Projection onto the base coordinate of the concrete eight-dimensional
extension. This is linear over Fp, not a ring homomorphism on all Fp8. -/
def fp8BaseProjection (x : Fp8) : Fp8 := Fp8.ofBase x.c0

theorem fp8_base_projection_linear :
    fp8BaseProjection 0=0 ∧
    (∀ a b,fp8BaseProjection (a+b)=fp8BaseProjection a+fp8BaseProjection b) ∧
    (∀ x : Fp,∀ a : Fp8,fp8BaseProjection (Fp8.ofBase x*a)=Fp8.ofBase x*fp8BaseProjection a) := by
  refine ⟨rfl,?_,?_⟩
  · intro a b
    exact Fp8.ofBase_add a.c0 b.c0
  · intro x a
    rw [←Fp8.smulBase_eq]
    change Fp8.ofBase (x*a.c0)=Fp8.ofBase x*Fp8.ofBase a.c0
    exact Fp8.ofBase_mul x a.c0

/-- A recovered polynomial sufficiently agreeing with a base-valued source
on distinct base points has base-valued coefficients. This applies only when
the actual committed source oracle's base-valuedness is established. -/
theorem fp8_polynomial_base_descent (domain : List Fp8) (distinct : domain.Nodup)
    (received : Fp8 → Fp8) (basePoints : ∀ x∈domain,Fp8.IsBase x)
    (baseValues : ∀ x∈domain,Fp8.IsBase (received x))
    (p : Poly Fp8) (D : Nat) (degree : p.DegLt D)
    (agreement : D≤count domain (fun x => received x=p.eval x)) :
    ∀ i,Fp8.IsBase (p.coeff i) := by
  have linear := fp8_base_projection_linear
  have fixed := polynomial_descent_from_agreement domain distinct received fp8BaseProjection linear.1 linear.2.1
    (by
      intro x hx a
      obtain ⟨b,rfl⟩ := (Fp8.isBase_iff x).mp (basePoints x hx)
      exact linear.2.2 b a)
    (by
      intro x hx
      obtain ⟨b,hb⟩ := (Fp8.isBase_iff (received x)).mp (baseValues x hx)
      rw [hb]
      rfl) p D degree agreement
  intro i
  apply (Fp8.isBase_iff _).mpr
  exact ⟨(p.coeff i).c0,(fixed i).symm⟩

theorem fp8_projected_coefficients_base (L d : Nat) (p : Poly Fp8)
    (base : ∀ i,Fp8.IsBase (p.coeff i)) :
    ∀ i,Fp8.IsBase ((recoverProjectedPolynomial L d p).coeff i) := by
  intro i
  by_cases bound : i<d
  · simpa [recoverProjectedPolynomial,Poly.coeff,List.getD,bound] using base (L*i)
  · have zero : (recoverProjectedPolynomial L d p).coeff i=0 :=
      recovered_projected_degree L d p i (by omega)
    rw [zero]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem fp8_lower_zeta_base (n : Nat) (coefficients : Nat → Fp8)
    (base : ∀ i,Fp8.IsBase (coefficients i)) (i : Nat) :
    Fp8.IsBase (lowerZeta n coefficients i) := by
  induction n generalizing coefficients i with
  | zero => exact base 0
  | succ n ih =>
    unfold lowerZeta
    split
    · exact ih _ (fun j => base (2*j)) _
    · apply ih
      intro j
      obtain ⟨a,ha⟩ := (Fp8.isBase_iff _).mp (base (2*j))
      obtain ⟨b,hb⟩ := (Fp8.isBase_iff _).mp (base (2*j+1))
      apply (Fp8.isBase_iff _).mpr
      exact ⟨a+b,by rw [ha,hb,Fp8.ofBase_add]⟩

/-- Descent survives projected-coefficient recovery and inverse Mobius
reconstruction: every recovered source table cell is base-valued. -/
theorem fp8_recovered_column_base (C : Nat) (lane : GKRSourceLane) (offset : Nat)
    (p : Poly Fp8) (base : ∀ i,Fp8.IsBase (p.coeff i)) (row : Nat) :
    Fp8.IsBase (recoveredColumnValues C lane offset p row) := by
  unfold recoveredColumnValues recoveredGKRTable
  apply fp8_lower_zeta_base
  exact fp8_projected_coefficients_base _ _ p base

end NearCompression
