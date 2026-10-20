import NearCompression.SmallCharacteristicDerivative

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]
local instance : NatCast K := Semiring.natCast

def polynomialDerivativeList : List K→Poly K
  | [] => Poly.zero
  | _::cs => Poly.mk cs+Poly.X*polynomialDerivativeList cs

def polynomialDerivative (p : Poly K) : Poly K := polynomialDerivativeList p.coeffs

private theorem cons_product (c : K) (cs : List K) (p : Poly K) (i : Nat) :
    ((Poly.mk (c::cs))*p).coeff i=c*p.coeff i+
      (match i with | 0=>0 | j+1=>((Poly.mk cs)*p).coeff j) := by
  change (Poly.smul c p+Poly.mk (0::Poly.mulL cs p.coeffs)).coeff i=_
  rw [Poly.coeff_add,Poly.coeff_smul]
  cases i <;> rfl

private theorem x_product (p : Poly K) (i : Nat) :
    (Poly.X*p).coeff i=match i with | 0=>0 | j+1=>p.coeff j := by
  change ((Poly.mk (0::[1]))*p).coeff i=_
  rw [cons_product]
  cases i with
  | zero => grind
  | succ i =>
    simp only []
    rw [cons_product]
    cases i <;> change 0*p.coeff _+(1*p.coeff _+0)=p.coeff _ <;> grind

/-- Formal derivative coefficient identity, including all trailing-zero cases. -/
theorem polynomial_derivative_coefficient (p : Poly K) (i : Nat) :
    (polynomialDerivative p).coeff i=(Nat.cast (i+1):K)*p.coeff (i+1) := by
  cases p with | mk cs =>
    induction cs generalizing i with
    | nil => change (0:K)=_*0;grind
    | cons c cs ih =>
      change ((Poly.mk cs)+Poly.X*polynomialDerivative (Poly.mk cs)).coeff i=_
      rw [Poly.coeff_add,x_product]
      cases i with
      | zero => change (Poly.mk cs).coeff 0+0=(Nat.cast 1:K)*(Poly.mk cs).coeff 0;grind
      | succ i =>
        change (Poly.mk cs).coeff (i+1)+(polynomialDerivative (Poly.mk cs)).coeff i=
          (Nat.cast (i+1+1):K)*(Poly.mk cs).coeff (i+1)
        rw [ih]
        grind

theorem polynomial_derivative_degree (p : Poly K) (D : Nat) (degree : p.DegLt (D+1)) :
    (polynomialDerivative p).DegLt D := by
  intro i hi
  rw [polynomial_derivative_coefficient,degree (i+1) (by omega)]
  grind

private theorem quotient_cons_eval (c : K) (cs : List K) (a : K) :
    ((Poly.mk (c::cs)).quot a).eval a=(Poly.mk cs).eval a+a*((Poly.mk cs).quot a).eval a := by
  change ((Poly.mk cs)+Poly.smul a ((Poly.mk cs).quot a)).eval a=_
  rw [Poly.eval_add,Poly.eval_smul]

/-- Evaluating the derivative equals the first synthetic jet; valid in every characteristic. -/
theorem polynomial_derivative_eval_quotient (p : Poly K) (a : K) :
    (polynomialDerivative p).eval a=(p.quot a).eval a := by
  cases p with | mk cs =>
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      change ((Poly.mk cs)+Poly.X*polynomialDerivative (Poly.mk cs)).eval a=_
      rw [Poly.eval_add,Poly.eval_mul,Poly.eval_X,ih,quotient_cons_eval]

def initialYPolynomial (rows : List (Poly K)) : Poly K :=
  Poly.mk (rows.map (fun row=>row.coeff 0))

private theorem product_constant (p q : Poly K) : (p*q).coeff 0=p.coeff 0*q.coeff 0 :=
  polynomial_order_product_coefficient p q 0 0 (by intro i hi;omega) (by intro i hi;omega)

private theorem initial_eval (rows : List (Poly K)) (a : K) :
    (bivariateSubstitute rows (Poly.C a)).coeff 0=(initialYPolynomial rows).eval a := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [bivariateSubstitute,Poly.coeff_add,product_constant]
    change row.coeff 0+a*(bivariateSubstitute rest (Poly.C a)).coeff 0=row.coeff 0+a*(initialYPolynomial rest).eval a
    rw [ih]

private theorem quotient_cons (p q : Poly K) (rest : List (Poly K)) (curve : Poly K) :
    bivariateCurveQuotient (p::q::rest) curve=
      bivariateSubstitute (q::rest) curve::bivariateCurveQuotient (q::rest) curve := by
  simp [bivariateCurveQuotient,List.range_succ_eq_map,List.map_map,Function.comp_def]

/-- Identify the operational Hensel slope with the actual initial Y derivative. -/
theorem hensel_slope_initial_derivative (rows : List (Poly K)) (a : K) :
    curveHenselSlope rows (Poly.C a)=(polynomialDerivative (initialYPolynomial rows)).eval a := by
  rw [polynomial_derivative_eval_quotient]
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    change curveHenselSlope (row::rest) (Poly.C a)=((Poly.mk (row.coeff 0::rest.map (fun p=>p.coeff 0))).quot a).eval a
    rw [quotient_cons_eval]
    cases rest with
    | nil => change (0:K)=0+a*0;grind
    | cons next rest =>
      unfold curveHenselSlope
      rw [quotient_cons]
      change (bivariateSubstitute (next::rest) (Poly.C a)+Poly.C a*bivariateSubstitute (bivariateCurveQuotient (next::rest) (Poly.C a)) (Poly.C a)).coeff 0=_
      rw [Poly.coeff_add,product_constant,initial_eval]
      change (initialYPolynomial (next::rest)).eval a+a*curveHenselSlope (next::rest) (Poly.C a)=_
      rw [ih]
      rfl

private theorem coefficient_equal_eval (p q : Poly K) (same : PolynomialCoeffEq p q) (a : K) : p.eval a=q.eval a := by
  have zero : (p-q).IsZero := by intro i;rw [Poly.coeff_sub,same i];grind
  have h:=Poly.eval_of_isZero zero a
  rw [Poly.eval_sub] at h
  grind

/-- A checked coefficientwise Bezout identity forbids a common root. The
nonzero constant is explicit, allowing denominator-cleared certificates. -/
theorem bezout_no_common_root (p q A B : Poly K) (c a : K)
    (certificate : PolynomialCoeffEq (A*p+B*q) (Poly.C c)) (nonzero : c≠0)
    (root : p.eval a=0) : q.eval a≠0 := by
  have identity:=coefficient_equal_eval _ _ certificate a
  rw [Poly.eval_add,Poly.eval_mul,Poly.eval_mul,Poly.eval_C,root] at identity
  intro other
  rw [other] at identity
  apply nonzero
  grind

/-- The certificate supplies smoothness of every initial root. Nonzero formal
derivative by itself is insufficient; the Bezout identity is checked. -/
theorem bezout_initial_root_smooth (rows : List (Poly K)) (A B : Poly K) (c a : K)
    (certificate : PolynomialCoeffEq
      (A*initialYPolynomial rows+B*polynomialDerivative (initialYPolynomial rows)) (Poly.C c))
    (nonzero : c≠0) (root : (bivariateSubstitute rows (Poly.C a)).coeff 0=0) :
    curveHenselSlope rows (Poly.C a)≠0 := by
  rw [hensel_slope_initial_derivative]
  apply bezout_no_common_root _ _ A B c a certificate nonzero
  rwa [←initial_eval]
end NearCompression
