import NearCompression.SelectedFactorSmoothness

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

private theorem unit_transport (i : Nat) :
    polynomialRationalOfPolynomial (unitCoefficientPolynomials (K:=K) i)=
      (Poly.C (1:PolynomialRational K)).coeff i := by
  cases i with
  | zero => rfl
  | succ i =>
    change polynomialRationalOfPolynomial (Poly.zero : Poly K)=0
    apply (polynomial_rational_of_polynomial_eq_iff _ _).mpr
    intro j;cases j <;> rfl

/-- A single Bezout determinant protects a bounded certificate between two
arbitrary polynomial parameter families, including a constant complement. -/
theorem bounded_bezout_shared_certificate_specializes
    (ps qs : Nat→Poly K) (p q A B : Poly (PolynomialRational K)) (m n : Nat)
    (pc : ∀ i,polynomialRationalOfPolynomial (ps i)=p.coeff i)
    (qc : ∀ i,polynomialRationalOfPolynomial (qs i)=q.coeff i)
    (positive : 0<m) (pd : p.DegLt (m+1)) (qd : q.DegLt (n+1)) (ql : q.coeff n≠0)
    (certificate : PolynomialCoeffEq (A*p+B*q) (Poly.C 1))
    (z : K) (safe : (bezoutSharedDenominator ps qs m n).eval z≠0) :
    ∃ (U V : Poly (PolynomialRational K)) (C D : Poly K),
      PolynomialCoeffEq (U*p+V*q) (Poly.C 1) ∧
      RationalPolynomialSpecializes U C z ∧ RationalPolynomialSpecializes V D z := by
  obtain ⟨U,V,ud,vd,cert⟩:=polynomial_bezout_degree_reduction p q A B m n positive pd qd ql certificate
  have values : ∀ r,r<n+m → ∃ v,PolynomialRationalValueAt (bezoutCoefficientVector U V n r) z v := by
    intro r inside
    rw [bezout_polynomial_cramer_formula ps qs unitCoefficientPolynomials p q A B U V (Poly.C 1)
      m n r pc qc unit_transport pd qd ql certificate ud vd cert inside]
    exact ⟨_,polynomial_rational_quotient_specializes _ _ z safe⟩
  have uv : ∀ i,∃ v,PolynomialRationalValueAt (U.coeff i) z v := by
    intro i
    by_cases inside : i<n
    · simpa only [bezoutCoefficientVector,ite_eq_left inside] using values i (by omega)
    · rw [ud i (by omega)];exact ⟨0,rational_coefficient_specializes 0 z⟩
  have vv : ∀ i,∃ v,PolynomialRationalValueAt (V.coeff i) z v := by
    intro i
    by_cases inside : i<m
    · have outside : ¬n+i<n := by omega
      simpa only [bezoutCoefficientVector,ite_eq_right outside,Nat.add_sub_cancel_left] using values (n+i) (by omega)
    · rw [vd i (by omega)];exact ⟨0,rational_coefficient_specializes 0 z⟩
  obtain ⟨C,cs⟩:=rational_polynomial_specialization_exists U z uv
  obtain ⟨D,ds⟩:=rational_polynomial_specialization_exists V z vv
  exact ⟨U,V,C,D,cert,cs,ds⟩

/-- Safely specializing a unit certificate excludes a common root. -/
theorem rational_bezout_specialized_noncollision
    (p q A B : Poly (PolynomialRational K)) (h g C D : Poly K) (z a : K)
    (certificate : PolynomialCoeffEq (A*p+B*q) (Poly.C 1))
    (ps : RationalPolynomialSpecializes p h z) (qs : RationalPolynomialSpecializes q g z)
    (aspec : RationalPolynomialSpecializes A C z) (bspec : RationalPolynomialSpecializes B D z)
    (root : h.eval a=0) : g.eval a≠0 := by
  have identity:=synthetic_jet_congr _ _ certificate (polynomialRationalCoefficientMap.toFun a) 0
  change (A*p+B*q).eval (polynomialRationalCoefficientMap.toFun a)=(Poly.C 1).eval _ at identity
  rw [Poly.eval_add,Poly.eval_mul,Poly.eval_mul,Poly.eval_C] at identity
  have specialized:=polynomial_rational_value_add _ _ z _ _
    (polynomial_rational_value_mul _ _ z _ _ (rational_polynomial_eval_specializes A C z a aspec)
      (rational_polynomial_eval_specializes p h z a ps))
    (polynomial_rational_value_mul _ _ z _ _ (rational_polynomial_eval_specializes B D z a bspec)
      (rational_polynomial_eval_specializes q g z a qs))
  rw [identity] at specialized
  have numeric:=polynomial_rational_value_unique _ z _ _ specialized (rational_coefficient_specializes 1 z)
  intro collision
  rw [root,collision] at numeric
  have impossible : (0:K)=1 := by grind
  exact Field.zero_ne_one impossible

/-- Explicit source lists have no common specialized root outside their
shared determinant guard. Formal coprimality is expressed by a unit certificate. -/
theorem parameter_factors_noncollision (hs gs : List (Poly K))
    (A B : Poly (PolynomialRational K)) (m n : Nat)
    (positive : 0<m) (hd : (polynomialParameterFamily hs).DegLt (m+1))
    (gd : (polynomialParameterFamily gs).DegLt (n+1))
    (gl : (polynomialParameterFamily gs).coeff n≠0)
    (certificate : PolynomialCoeffEq
      (A*polynomialParameterFamily hs+B*polynomialParameterFamily gs) (Poly.C 1))
    (z a : K)
    (safe : (bezoutSharedDenominator (fun i=>hs.getD i Poly.zero) (fun i=>gs.getD i Poly.zero) m n).eval z≠0)
    (root : (polynomialParameterSpecialize hs z).eval a=0) :
    (polynomialParameterSpecialize gs z).eval a≠0 := by
  obtain ⟨U,V,C,D,cert,cs,ds⟩:=bounded_bezout_shared_certificate_specializes
    (fun i=>hs.getD i Poly.zero) (fun i=>gs.getD i Poly.zero)
    (polynomialParameterFamily hs) (polynomialParameterFamily gs) A B m n
    (polynomial_parameter_family_coefficient hs) (polynomial_parameter_family_coefficient gs)
    positive hd gd gl certificate z safe
  exact rational_bezout_specialized_noncollision _ _ U V _ _ C D z a cert
    (polynomial_parameter_family_specializes hs z) (polynomial_parameter_family_specializes gs z) cs ds root

/-- At most (m+n)*D distinct parameter values admit a common root of the
selected factor and its complement. No coefficient-presentation budget remains. -/
theorem parameter_factor_collision_count (hs gs : List (Poly K))
    (A B : Poly (PolynomialRational K)) (m n D : Nat)
    (positive : 0<m) (hd : (polynomialParameterFamily hs).DegLt (m+1))
    (gd : (polynomialParameterFamily gs).DegLt (n+1))
    (gl : (polynomialParameterFamily gs).coeff n≠0)
    (certificate : PolynomialCoeffEq
      (A*polynomialParameterFamily hs+B*polynomialParameterFamily gs) (Poly.C 1))
    (hsd : ∀ i,(hs.getD i Poly.zero).DegLt (D+1))
    (gsd : ∀ i,(gs.getD i Poly.zero).DegLt (D+1))
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun z=>∃ a : K,(polynomialParameterSpecialize hs z).eval a=0 ∧
      (polynomialParameterSpecialize gs z).eval a=0)≤(n+m)*D := by
  apply Nat.le_trans _ (bezout_shared_denominator_exception_count
    (fun i=>hs.getD i Poly.zero) (fun i=>gs.getD i Poly.zero)
    (polynomialParameterFamily hs) (polynomialParameterFamily gs) A B m n D
    (polynomial_parameter_family_coefficient hs) (polynomial_parameter_family_coefficient gs)
    hd gd gl certificate hsd gsd sample distinct)
  apply count_mono
  intro z bad
  obtain ⟨a,root,collision⟩:=bad
  apply Classical.byContradiction
  intro safe
  exact parameter_factors_noncollision hs gs A B m n positive hd gd gl certificate z a safe root collision
/-- The derivative and collision guards jointly supply lifting of the full
source through a selected irreducible initial factor. -/
theorem guarded_selected_factor_hensel_lift
    (characteristic : Nat) [IsCharP K characteristic] (hs gs : List (Poly K))
    (A B : Poly (PolynomialRational K)) (m n : Nat)
    (irreducible : PolynomialIrreducible (polynomialParameterFamily hs))
    (positive : 0<m) (small : m<characteristic)
    (hd : (polynomialParameterFamily hs).DegLt (m+1))
    (hl : (polynomialParameterFamily hs).coeff m≠0)
    (gd : (polynomialParameterFamily gs).DegLt (n+1))
    (gl : (polynomialParameterFamily gs).coeff n≠0)
    (certificate : PolynomialCoeffEq
      (A*polynomialParameterFamily hs+B*polynomialParameterFamily gs) (Poly.C 1))
    (rows : List (Poly K)) (z a : K) (precision : Nat)
    (factorization : PolynomialCoeffEq (initialYPolynomial rows)
      (polynomialParameterSpecialize hs z*polynomialParameterSpecialize gs z))
    (derivativeSafe : (derivativeSharedDenominator (fun i=>hs.getD i Poly.zero) m).eval z≠0)
    (collisionSafe : (bezoutSharedDenominator (fun i=>hs.getD i Poly.zero) (fun i=>gs.getD i Poly.zero) m n).eval z≠0)
    (root : (polynomialParameterSpecialize hs z).eval a=0) :
    (curveHenselLift rows a precision).coeff 0=a ∧ (curveHenselLift rows a precision).DegLt (precision+1) ∧
    PolynomialOrder (bivariateSubstitute rows (curveHenselLift rows a precision)) (precision+1) := by
  apply selected_factor_hensel_lift rows _ _ a precision factorization root
  · exact irreducible_shared_denominator_root_smooth characteristic (fun i=>hs.getD i Poly.zero)
      (polynomialParameterFamily hs) m (polynomial_parameter_family_coefficient hs)
      irreducible hd hl positive small _ z a (polynomial_parameter_family_specializes hs z) derivativeSafe root
  · exact parameter_factors_noncollision hs gs A B m n positive hd gd gl certificate z a collisionSafe root
end NearCompression
