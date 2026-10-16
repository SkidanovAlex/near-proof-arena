import NearCompression.DenseAlgebraicHensel

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- A derivative certificate for P=h*g yields a modular certificate for the
full-source derivative against h, including a proper selected factor. -/
theorem selected_full_source_derivative_certificate (p h g S T : Poly K)
    (factorization : PolynomialCoeffEq p (h*g))
    (certificate : PolynomialCoeffEq (S*p+T*polynomialDerivative p) (Poly.C 1)) :
    PolynomialCoeffEq ((S*g)*h+T*polynomialDerivative p) (Poly.C 1) := by
  have fac:=(formal_polynomial_eq_iff _ _).mpr factorization
  have cert:=(formal_polynomial_eq_iff _ _).mpr certificate
  change formalPolynomial p=formalPolynomial h*formalPolynomial g at fac
  change formalPolynomial S*formalPolynomial p+formalPolynomial T*formalPolynomial (polynomialDerivative p)=1 at cert
  apply (formal_polynomial_eq_iff _ _).mp
  change (formalPolynomial S*formalPolynomial g)*formalPolynomial h+
    formalPolynomial T*formalPolynomial (polynomialDerivative p)=1
  grind

/-- Explicit selected-branch input obligations. The factor must already have
polynomial parameter coefficients; neither that representation nor source
separability is inferred by this record. n is the exact source-derivative degree. -/
structure SelectedSourceSlopeData (K : Type) [Field K] where
  rows : List (List (Poly K))
  factorRows : List (Poly K)
  complement : Poly (PolynomialRational K)
  S : Poly (PolynomialRational K)
  T : Poly (PolynomialRational K)
  m : Nat
  n : Nat
  positive : 0<m
  irreducible : PolynomialIrreducible (polynomialParameterFamily factorRows)
  factorDegree : (polynomialParameterFamily factorRows).DegLt (m+1)
  derivativeDegree : (polynomialDerivative (polynomialParameterFamily (trivariateInitialRows rows))).DegLt (n+1)
  derivativeLeading : (polynomialDerivative (polynomialParameterFamily (trivariateInitialRows rows))).coeff n≠0
  factorization : PolynomialCoeffEq (polynomialParameterFamily (trivariateInitialRows rows))
    (polynomialParameterFamily factorRows*complement)
  certificate : PolynomialCoeffEq
    (S*polynomialParameterFamily (trivariateInitialRows rows)+
      T*polynomialDerivative (polynomialParameterFamily (trivariateInitialRows rows))) (Poly.C 1)

def SelectedSourceSlopeData.guard (data : SelectedSourceSlopeData K) : Poly K :=
  bezoutSharedDenominator (fun i=>data.factorRows.getD i Poly.zero)
    (derivativeCoefficientPolynomials (fun i=>(trivariateInitialRows data.rows).getD i Poly.zero)) data.m data.n

/-- The full-source slope guard is proved nonzero from the source certificate,
not from an unproved nonsingularity assertion. -/
theorem selected_source_slope_guard_nonzero (data : SelectedSourceSlopeData K) : ¬data.guard.IsZero := by
  exact bezout_shared_denominator_nonzero _ _ _ _ (data.S*data.complement) data.T data.m data.n
    (polynomial_parameter_family_coefficient data.factorRows)
    (derivative_coefficient_polynomials_transport _ _ (polynomial_parameter_family_coefficient _))
    data.factorDegree data.derivativeDegree data.derivativeLeading
    (selected_full_source_derivative_certificate _ _ _ _ _ data.factorization data.certificate)

/-- Source and selected-factor parameter degree bounds control a single guard
for every coefficient and every finite lifting precision. -/
theorem selected_source_slope_guard_degree (data : SelectedSourceSlopeData K) (D : Nat)
    (factorDegree : ∀ i,(data.factorRows.getD i Poly.zero).DegLt (D+1))
    (sourceDegree : ∀ i,((trivariateInitialRows data.rows).getD i Poly.zero).DegLt (D+1)) :
    data.guard.DegLt ((data.n+data.m)*D+1) :=
  bezout_shared_denominator_degree _ _ data.m data.n D factorDegree
    (fun i=>Poly.degLt_smul _ (sourceDegree (i+1)))

theorem selected_source_slope_guard_exception_count (data : SelectedSourceSlopeData K) (D : Nat)
    (factorDegree : ∀ i,(data.factorRows.getD i Poly.zero).DegLt (D+1))
    (sourceDegree : ∀ i,((trivariateInitialRows data.rows).getD i Poly.zero).DegLt (D+1))
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun z=>data.guard.eval z=0)≤(data.n+data.m)*D := by
  have bound:=PolyRoots.cardRootsLe_of polyEval polyDeg quotFacts isZeroEval K data.guard
    ((data.n+data.m)*D+1) sample (selected_source_slope_guard_nonzero data)
    (selected_source_slope_guard_degree data D factorDegree sourceDegree) distinct
  omega

/-- A good guard value constructs all needed safe certificate coefficients. -/
theorem selected_source_slope_guard_certificate (data : SelectedSourceSlopeData K) (z : K)
    (safe : data.guard.eval z≠0) :
    ∃ (A B : Poly (PolynomialRational K)) (C E : Poly K),
      PolynomialCoeffEq (A*polynomialParameterFamily data.factorRows+
        B*polynomialDerivative (polynomialParameterFamily (trivariateInitialRows data.rows))) (Poly.C 1) ∧
      RationalPolynomialSpecializes A C z ∧ RationalPolynomialSpecializes B E z := by
  exact bounded_bezout_shared_certificate_specializes _ _ _ _ (data.S*data.complement) data.T data.m data.n
    (polynomial_parameter_family_coefficient data.factorRows)
    (derivative_coefficient_polynomials_transport _ _ (polynomial_parameter_family_coefficient _))
    data.positive data.factorDegree data.derivativeDegree data.derivativeLeading
    (selected_full_source_derivative_certificate _ _ _ _ _ data.factorization data.certificate) z safe

/-- The explicit guard now discharges safe-certificate premises for dense
algebraic-to-numeric Hensel specialization at every precision. -/
theorem selected_source_guarded_hensel_specializes (data : SelectedSourceSlopeData K)
    (z a : K) (safe : data.guard.eval z≠0)
    (root : (polynomialParameterSpecialize data.factorRows z).eval a=0) :
    letI := polynomialResidueField (polynomialParameterFamily data.factorRows) data.irreducible
    ∀ n i,AlgebraicResidueValueAt (polynomialParameterFamily data.factorRows)
      ((curveHenselLift
        ((denseTrivariateRationalRows data.rows).map
          (transportPolynomial (polynomialResidueEmbedding (polynomialParameterFamily data.factorRows) data.irreducible)))
        (polynomialResidueClass (polynomialParameterFamily data.factorRows) Poly.X) n).coeff i) z a
      ((curveHenselLift (denseTrivariateSpecialize data.rows z) a n).coeff i) := by
  obtain ⟨A,B,C,E,cert,cs,es⟩:=selected_source_slope_guard_certificate data z safe
  exact dense_algebraic_hensel_specializes _ A B data.irreducible data.rows
    (polynomialParameterSpecialize data.factorRows z) C E z a cert
    (polynomial_parameter_family_specializes data.factorRows z) cs es root
end NearCompression
