import NearCompression.BezoutPolynomialDenominator

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]
attribute [local instance] Semiring.natCast Ring.intCast

private theorem map_nat (f : PolynomialFieldMap K (PolynomialRational K)) (n : Nat) :
    f.toFun (OfNat.ofNat n)=OfNat.ofNat n := by
  induction n with
  | zero => exact f.zero
  | succ n ih =>
    rw [Semiring.ofNat_succ (α:=K) n,Semiring.ofNat_succ (α:=PolynomialRational K) n,f.add,ih,f.one]

private theorem rational_smul (c : K) (p : Poly K) :
    polynomialRationalOfPolynomial (Poly.smul c p)=
      polynomialRationalCoefficientMap.toFun c*polynomialRationalOfPolynomial p := by
  change polynomialRationalOfPolynomial (Poly.smul c p)=polynomialRationalOfPolynomial (Poly.C c)*polynomialRationalOfPolynomial p
  rw [←polynomial_rational_of_polynomial_mul]
  apply (polynomial_rational_of_polynomial_eq_iff _ _).mpr
  intro i
  change (Poly.smul c p).coeff i=(Poly.smul c p+Poly.mk [0]).coeff i
  rw [Poly.coeff_add]
  have zero : (Poly.mk [0] : Poly K).coeff i=0 := by cases i <;> rfl
  rw [zero];grind

/-- Polynomial parameter entries for the formal Y derivative. -/
def derivativeCoefficientPolynomials (ps : Nat→Poly K) (i : Nat) : Poly K :=
  Poly.smul (OfNat.ofNat (i+1)) (ps (i+1))

theorem derivative_coefficient_polynomials_transport (ps : Nat→Poly K)
    (p : Poly (PolynomialRational K))
    (pc : ∀ i,polynomialRationalOfPolynomial (ps i)=p.coeff i) (i : Nat) :
    polynomialRationalOfPolynomial (derivativeCoefficientPolynomials ps i)=
      (polynomialDerivative p).coeff i := by
  unfold derivativeCoefficientPolynomials
  rw [rational_smul,map_nat,pc,polynomial_derivative_coefficient,Semiring.ofNat_eq_natCast]

/-- Row-oriented derivative denominator; no transpose identity is assumed. -/
def derivativeSharedDenominator (ps : Nat→Poly K) (d : Nat) : Poly K :=
  bezoutSharedDenominator ps (derivativeCoefficientPolynomials ps) d (d-1)

private theorem derivative_leading (characteristic : Nat) [IsCharP K characteristic]
    (p : Poly K) (d : Nat) (leading : p.coeff d≠0) (positive : 0<d) (small : d<characteristic) :
    (polynomialDerivative p).coeff (d-1)≠0 := by
  rw [polynomial_derivative_coefficient]
  have same : d-1+1=d := by omega
  rw [same]
  intro zero
  rcases Field.of_mul_eq_zero zero with scalar|coefficient
  · have modular:=(IsCharP.natCast_eq_zero_iff characteristic d).mp scalar
    rw [Nat.mod_eq_of_lt small] at modular
    omega
  · exact leading coefficient

/-- Irreducibility below the characteristic supplies nonzeroness of the
explicit derivative denominator, without a separate certificate assumption. -/
theorem irreducible_derivative_denominator_nonzero
    (characteristic : Nat) [IsCharP K characteristic]
    (ps : Nat→Poly K) (p : Poly (PolynomialRational K)) (d : Nat)
    (pc : ∀ i,polynomialRationalOfPolynomial (ps i)=p.coeff i)
    (irreducible : PolynomialIrreducible p) (degree : p.DegLt (d+1))
    (leading : p.coeff d≠0) (positive : 0<d) (small : d<characteristic) :
    ¬(derivativeSharedDenominator ps d).IsZero := by
  obtain ⟨A,B,certificate⟩:=irreducible_derivative_bezout characteristic p d irreducible degree leading positive small
  have dd : (polynomialDerivative p).DegLt (d-1+1) := by
    have same : d-1+1=d := by omega
    rw [same];exact polynomial_derivative_degree p d degree
  exact bezout_shared_denominator_nonzero ps (derivativeCoefficientPolynomials ps) p
    (polynomialDerivative p) A B d (d-1) pc (derivative_coefficient_polynomials_transport ps p pc)
    degree dd (derivative_leading characteristic p d leading positive small) certificate

theorem derivative_shared_denominator_degree (ps : Nat→Poly K) (d D : Nat)
    (positive : 0<d) (degree : ∀ i,(ps i).DegLt (D+1)) :
    (derivativeSharedDenominator ps d).DegLt ((2*d-1)*D+1) := by
  have bound:=bezout_shared_denominator_degree ps (derivativeCoefficientPolynomials ps) d (d-1) D
    degree (fun i=>Poly.degLt_smul _ (degree (i+1)))
  have same : d-1+d=2*d-1 := by omega
  simpa only [derivativeSharedDenominator,same] using bound

/-- At most (2d-1)*D distinct points destroy the common derivative-certificate
denominator for an irreducible source polynomial of Y-degree d<char. -/
theorem irreducible_derivative_denominator_exception_count
    (characteristic : Nat) [IsCharP K characteristic]
    (ps : Nat→Poly K) (p : Poly (PolynomialRational K)) (d D : Nat)
    (pc : ∀ i,polynomialRationalOfPolynomial (ps i)=p.coeff i)
    (irreducible : PolynomialIrreducible p) (degree : p.DegLt (d+1))
    (leading : p.coeff d≠0) (positive : 0<d) (small : d<characteristic)
    (sourceDegree : ∀ i,(ps i).DegLt (D+1)) (sample : List K) (distinct : sample.Nodup) :
    count sample (fun z=>(derivativeSharedDenominator ps d).eval z=0)≤(2*d-1)*D := by
  have bound:=PolyRoots.cardRootsLe_of polyEval polyDeg quotFacts isZeroEval K
    (derivativeSharedDenominator ps d) ((2*d-1)*D+1) sample
    (irreducible_derivative_denominator_nonzero characteristic ps p d pc irreducible degree leading positive small)
    (derivative_shared_denominator_degree ps d D positive sourceDegree) distinct
  omega
/-- Polynomial coefficient entries of the unit target in the Y variable. -/
def unitCoefficientPolynomials (i : Nat) : Poly K :=
  if i=0 then Poly.C 1 else Poly.zero

private theorem unit_transport (i : Nat) :
    polynomialRationalOfPolynomial (unitCoefficientPolynomials (K:=K) i)=
      (Poly.C (1:PolynomialRational K)).coeff i := by
  cases i with
  | zero => rfl
  | succ i =>
    change polynomialRationalOfPolynomial (Poly.zero : Poly K)=0
    apply (polynomial_rational_of_polynomial_eq_iff _ _).mpr
    intro j;cases j <;> rfl

/-- A bounded derivative certificate exists and all of its 2d-1 coordinates
share the explicit source-degree-controlled denominator. -/
theorem irreducible_derivative_shared_certificate
    (characteristic : Nat) [IsCharP K characteristic]
    (ps : Nat→Poly K) (p : Poly (PolynomialRational K)) (d : Nat)
    (pc : ∀ i,polynomialRationalOfPolynomial (ps i)=p.coeff i)
    (irreducible : PolynomialIrreducible p) (degree : p.DegLt (d+1))
    (leading : p.coeff d≠0) (positive : 0<d) (small : d<characteristic) :
    ∃ A B : Poly (PolynomialRational K), A.DegLt (d-1) ∧ B.DegLt d ∧
      PolynomialCoeffEq (A*p+B*polynomialDerivative p) (Poly.C 1) ∧
      ∀ r, r<2*d-1 → bezoutCoefficientVector A B (d-1) r=
        polynomialRationalOfPolynomial
          (bezoutCramerNumerator ps (derivativeCoefficientPolynomials ps) unitCoefficientPolynomials d (d-1) r)*
        (polynomialRationalOfPolynomial (derivativeSharedDenominator ps d))⁻¹ := by
  obtain ⟨A,B,ad,bd,certificate⟩:=irreducible_bounded_derivative_bezout characteristic p d
    irreducible degree leading positive small
  refine ⟨A,B,ad,bd,certificate,?_⟩
  intro r inside
  have dd : (polynomialDerivative p).DegLt (d-1+1) := by
    have same : d-1+1=d := by omega
    rw [same];exact polynomial_derivative_degree p d degree
  exact bezout_polynomial_cramer_formula ps (derivativeCoefficientPolynomials ps) unitCoefficientPolynomials
    p (polynomialDerivative p) A B A B (Poly.C 1) d (d-1) r pc
    (derivative_coefficient_polynomials_transport ps p pc) unit_transport degree dd
    (derivative_leading characteristic p d leading positive small) certificate ad bd certificate (by omega)
end NearCompression
