import NearCompression.BezoutCoefficientMatrix

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

private theorem rational_zero : polynomialRationalOfPolynomial (Poly.zero : Poly K)=0 := by
  apply (polynomial_rational_of_polynomial_eq_iff _ _).mpr
  intro i;cases i <;> rfl

/-- The polynomial-entry matrix embeds exactly as the rational coefficient
matrix. This uses formal coefficients, not pointwise function equality. -/
theorem bezout_polynomial_matrix_rational_transport
    (ps qs : Nat→Poly K) (p q : Poly (PolynomialRational K)) (m n : Nat)
    (pc : ∀ i,polynomialRationalOfPolynomial (ps i)=p.coeff i)
    (qc : ∀ i,polynomialRationalOfPolynomial (qs i)=q.coeff i) :
    (fun j i=>polynomialRationalOfPolynomial (bezoutPolynomialMatrix ps qs m n i j))=
      bezoutRowMatrix p q m n := by
  funext j i
  unfold bezoutPolynomialMatrix bezoutRowMatrix bezoutScalarCoefficientMatrix
  split
  · split
    · exact pc _
    · exact rational_zero
  · split
    · exact qc _
    · exact rational_zero

/-- A source-polynomial shared denominator, in the row orientation used by
Cramer's formula. -/
def bezoutSharedDenominator (ps qs : Nat→Poly K) (m n : Nat) : Poly K :=
  polynomialMinorDeterminant (fun j i=>bezoutPolynomialMatrix ps qs m n i j)
    (List.range (n+m)) (List.range (n+m))

/-- A unit certificate over the rational-function field guarantees that this
explicit polynomial denominator is formally nonzero. -/
theorem bezout_shared_denominator_nonzero
    (ps qs : Nat→Poly K) (p q A B : Poly (PolynomialRational K)) (m n : Nat)
    (pc : ∀ i,polynomialRationalOfPolynomial (ps i)=p.coeff i)
    (qc : ∀ i,polynomialRationalOfPolynomial (qs i)=q.coeff i)
    (pd : p.DegLt (m+1)) (qd : q.DegLt (n+1)) (ql : q.coeff n≠0)
    (certificate : PolynomialCoeffEq (A*p+B*q) (Poly.C 1)) :
    ¬(bezoutSharedDenominator ps qs m n).IsZero := by
  apply (polynomial_minor_determinant_nonzero_iff _ _ _).mpr
  rw [bezout_polynomial_matrix_rational_transport ps qs p q m n pc qc]
  exact bezout_coefficient_determinant_nonzero p q A B m n pd qd ql certificate

/-- The denominator degree is bounded directly by the original coefficient
degrees, independently of any Euclidean algorithm or pivot choices. -/
theorem bezout_shared_denominator_degree (ps qs : Nat→Poly K) (m n D : Nat)
    (pd : ∀ i,(ps i).DegLt (D+1)) (qd : ∀ i,(qs i).DegLt (D+1)) :
    (bezoutSharedDenominator ps qs m n).DegLt ((n+m)*D+1) := by
  simpa only [bezoutSharedDenominator,List.length_range] using polynomial_minor_determinant_degree
    (fun j i=>bezoutPolynomialMatrix ps qs m n i j) (List.range (n+m)) (List.range (n+m)) D
    (fun j i=>bezout_polynomial_matrix_degree ps qs m n D pd qd i j)

/-- At most (m+n)*D distinct points annihilate the common denominator. Both
nonzeroness and the source-degree bound are discharged from the inputs. -/
theorem bezout_shared_denominator_exception_count
    (ps qs : Nat→Poly K) (p q A B : Poly (PolynomialRational K)) (m n D : Nat)
    (pc : ∀ i,polynomialRationalOfPolynomial (ps i)=p.coeff i)
    (qc : ∀ i,polynomialRationalOfPolynomial (qs i)=q.coeff i)
    (pd : p.DegLt (m+1)) (qd : q.DegLt (n+1)) (ql : q.coeff n≠0)
    (certificate : PolynomialCoeffEq (A*p+B*q) (Poly.C 1))
    (psd : ∀ i,(ps i).DegLt (D+1)) (qsd : ∀ i,(qs i).DegLt (D+1))
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun z=>(bezoutSharedDenominator ps qs m n).eval z=0)≤(n+m)*D := by
  have bound:=PolyRoots.cardRootsLe_of polyEval polyDeg quotFacts isZeroEval K
    (bezoutSharedDenominator ps qs m n) ((n+m)*D+1) sample
    (bezout_shared_denominator_nonzero ps qs p q A B m n pc qc pd qd ql certificate)
    (bezout_shared_denominator_degree ps qs m n D psd qsd) distinct
  omega

/-- Replacement determinants supply polynomial numerators for the same
shared denominator, including targets with polynomial parameter entries. -/
def bezoutCramerNumerator (ps qs ts : Nat→Poly K) (m n r : Nat) : Poly K :=
  polynomialMinorDeterminant (fun j i=>if j=r then ts i else bezoutPolynomialMatrix ps qs m n i j)
    (List.range (n+m)) (List.range (n+m))

theorem bezout_polynomial_cramer_formula
    (ps qs ts : Nat→Poly K) (p q A B U V target : Poly (PolynomialRational K)) (m n r : Nat)
    (pc : ∀ i,polynomialRationalOfPolynomial (ps i)=p.coeff i)
    (qc : ∀ i,polynomialRationalOfPolynomial (qs i)=q.coeff i)
    (tc : ∀ i,polynomialRationalOfPolynomial (ts i)=target.coeff i)
    (pd : p.DegLt (m+1)) (qd : q.DegLt (n+1)) (ql : q.coeff n≠0)
    (certificate : PolynomialCoeffEq (A*p+B*q) (Poly.C 1))
    (ud : U.DegLt n) (vd : V.DegLt m) (solved : PolynomialCoeffEq (U*p+V*q) target)
    (inside : r<n+m) :
    bezoutCoefficientVector U V n r=
      polynomialRationalOfPolynomial (bezoutCramerNumerator ps qs ts m n r)*
      (polynomialRationalOfPolynomial (bezoutSharedDenominator ps qs m n))⁻¹ := by
  have transport:=bezout_polynomial_matrix_rational_transport ps qs p q m n pc qc
  have numerator : (fun j i=>polynomialRationalOfPolynomial
      (if j=r then ts i else bezoutPolynomialMatrix ps qs m n i j))=
      replaceDeterminantRow (bezoutRowMatrix p q m n) r target.coeff := by
    funext j i
    by_cases same : j=r
    · simp only [same,ite_true,replaceDeterminantRow];exact tc i
    · simp only [same,ite_false,replaceDeterminantRow]
      exact congrFun (congrFun transport j) i
  unfold bezoutCramerNumerator bezoutSharedDenominator
  rw [polynomial_minor_determinant_rational_transport,polynomial_minor_determinant_rational_transport,
    numerator,transport]
  exact bezout_coefficient_cramer p q A B U V target m n r pd qd ql certificate ud vd solved inside

/-- When target entries obey the same parameter-degree bound (in particular
constant targets), numerator and denominator degrees are both at most N*D. -/
theorem bezout_cramer_numerator_degree (ps qs ts : Nat→Poly K) (m n r D : Nat)
    (pd : ∀ i,(ps i).DegLt (D+1)) (qd : ∀ i,(qs i).DegLt (D+1))
    (td : ∀ i,(ts i).DegLt (D+1)) :
    (bezoutCramerNumerator ps qs ts m n r).DegLt ((n+m)*D+1) := by
  have entries : ∀ j i,(if j=r then ts i else bezoutPolynomialMatrix ps qs m n i j).DegLt (D+1) := by
    intro j i
    split
    · exact td i
    · exact bezout_polynomial_matrix_degree ps qs m n D pd qd i j
  simpa only [bezoutCramerNumerator,List.length_range] using polynomial_minor_determinant_degree
    (fun j i=>if j=r then ts i else bezoutPolynomialMatrix ps qs m n i j)
    (List.range (n+m)) (List.range (n+m)) D entries
end NearCompression
