import NearCompression.GSInterpolation

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- The r-th jet as a formal polynomial in its center. Horner recurrence
avoids factorial inverses and an assumed binomial-coefficient formula. -/
def jetCenterPolynomial : List K→Nat→Poly K
  | [],_ => Poly.zero
  | c::cs,0 => Poly.mk (c::cs)
  | _::cs,r+1 => jetCenterPolynomial cs r+Poly.X*jetCenterPolynomial cs (r+1)

theorem jet_center_polynomial_eval (cs : List K) (r : Nat) (a : K) :
    (jetCenterPolynomial cs r).eval a=syntheticJet (Poly.mk cs) a r := by
  induction cs generalizing r with
  | nil =>
    have zero : ∀ n,syntheticJet (Poly.zero : Poly K) a n=0 := by
      intro n;induction n with
      | zero => rfl
      | succ n ih => exact ih
    exact (zero r).symm
  | cons c cs ih =>
    cases r with
    | zero => rfl
    | succ r =>
      rw [jetCenterPolynomial,Poly.eval_add,Poly.eval_mul,ih,ih,synthetic_jet_cons_succ]
      have x : (Poly.X : Poly K).eval a=a := by simp [Poly.X,Poly.eval,Poly.evalL];grind
      rw [x]

private theorem product_zero (p q : Poly K) (zero : q.IsZero) : (p*q).IsZero := by
  intro i
  exact polynomial_order_mul 0 (i+1) p q (by intro j hj;omega) (fun j _=>zero j) i (by omega)

/-- Differentiation order reduces center degree, with exact zero behavior
beyond the stored degree. This is valid even when characteristic≤r. -/
theorem jet_center_polynomial_degree (cs : List K) (r : Nat) :
    (jetCenterPolynomial cs r).DegLt (cs.length-r) := by
  induction cs generalizing r with
  | nil => intro i hi;simp [jetCenterPolynomial,Poly.zero,Poly.coeff]
  | cons c cs ih =>
    cases r with
    | zero => exact Poly.degLt_length (Poly.mk (c::cs))
    | succ r =>
      have left:=ih r
      have right:=ih (r+1)
      have size : (c::cs).length-(r+1)=cs.length-r := by simp
      rw [size]
      apply Poly.degLt_add left
      by_cases low : r<cs.length
      · have bound : cs.length-(r+1)+1=cs.length-r := by omega
        have xDegree : (Poly.X : Poly K).DegLt (1+1) := Poly.degLt_length _
        by_cases last : cs.length=r+1
        · have zero : (jetCenterPolynomial cs (r+1)).IsZero := fun i=>right i (by omega)
          exact fun i _=>product_zero Poly.X _ zero i
        · have rsize : cs.length-(r+1)=(cs.length-(r+1)-1)+1 := by omega
          rw [rsize] at right
          have product:=Poly.degLt_mul xDegree right
          have degreeSize : 1+(cs.length-(r+1)-1)+1=cs.length-r := by omega
          simpa only [degreeSize] using product
      · have zero : (jetCenterPolynomial cs (r+1)).IsZero := fun i=>right i (by omega)
        exact fun i _=>product_zero Poly.X _ zero i

def polynomialCompose (p q : Poly K) : Poly K :=
  bivariateSubstitute (p.coeffs.map Poly.C) q

theorem polynomial_compose_eval (p q : Poly K) (a : K) :
    (polynomialCompose p q).eval a=p.eval (q.eval a) := by
  cases p with
  | mk cs =>
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      change (Poly.C c+q*polynomialCompose (Poly.mk cs) q).eval a=c+q.eval a*(Poly.mk cs).eval (q.eval a)
      rw [Poly.eval_add,Poly.eval_mul,ih]
      have constant : (Poly.C c).eval a=c := by simp [Poly.C,Poly.eval,Poly.evalL];grind
      rw [constant]

private theorem constant_rows_coefficient (cs : List K) (i j : Nat) :
    ((cs.map Poly.C).getD j Poly.zero).coeff i=if i=0 then (Poly.mk cs).coeff j else 0 := by
  induction cs generalizing j with
  | nil => simp [Poly.coeff,Poly.zero]
  | cons c cs ih =>
    cases j with
    | zero => cases i <;> simp [Poly.C,Poly.coeff,List.getD]
    | succ j => exact ih j

/-- Affine substitution preserves semantic degree bounds, including constant
and zero curves. The bound does not depend on syntactic coefficient lengths. -/
theorem polynomial_compose_affine_degree (p curve : Poly K) (D : Nat)
    (degree : p.DegLt D) (affine : curve.DegLt 2) :
    (polynomialCompose p curve).DegLt D := by
  apply bivariate_substitution_degree _ curve 1 D affine
  intro i j high
  rw [constant_rows_coefficient]
  by_cases zero : i=0
  · subst i
    simp only [ite_true]
    exact degree j (by simpa using high)
  · simp [zero]

/-- Jet of X^j along an affine center u+vZ as a formal Z polynomial. -/
def monomialJetAlongLine (j s : Nat) (u v : K) : Poly K :=
  polynomialCompose (jetCenterPolynomial (jetMonomial j : Poly K).coeffs s) (Poly.mk [u,v])

theorem monomial_jet_line_eval (j s : Nat) (u v z : K) :
    (monomialJetAlongLine j s u v).eval z=syntheticJet (jetMonomial j) (u+z*v) s := by
  rw [monomialJetAlongLine,polynomial_compose_eval,jet_center_polynomial_eval]
  have point : (Poly.mk [u,v]).eval z=u+z*v := by simp [Poly.eval,Poly.evalL];grind
  rw [point]

theorem monomial_jet_line_degree (j s : Nat) (u v : K) :
    (monomialJetAlongLine j s u v).DegLt (j+1-s) := by
  apply polynomial_compose_affine_degree _ _ (j+1-s)
  · have h:=jet_center_polynomial_degree (jetMonomial j : Poly K).coeffs s
    simpa only [jetMonomial,List.length_map,List.length_range] using h
  · exact Poly.degLt_length (Poly.mk [u,v])
/-- One trivariate monomial's mixed (X,Y) jet along (x,u+vZ), as
an actual formal polynomial in Z. -/
def trivariateJetTerm (i j h r s : Nat) (x u v : K) : Poly K :=
  Poly.smul (syntheticJet (jetMonomial i) x r)
    ((jetMonomial h)*monomialJetAlongLine j s u v)

theorem trivariate_jet_term_eval (i j h r s : Nat) (x u v z : K) :
    (trivariateJetTerm i j h r s x u v).eval z=
      (jetMonomial h).eval z*gsMixedRow x (u+z*v) r s (i,j) := by
  rw [trivariateJetTerm,Poly.eval_smul,Poly.eval_mul,monomial_jet_line_eval]
  unfold gsMixedRow
  grind

/-- The coupled Y/Z budget gives fewer than Zcap-s coefficient equations
for each mixed-jet order (r,s). If s>j the term is formally zero. -/
theorem trivariate_jet_term_degree (i j h r s Zcap : Nat) (x u v : K)
    (budget : j+h<Zcap) :
    (trivariateJetTerm i j h r s x u v).DegLt (Zcap-s) := by
  apply Poly.degLt_smul
  have jd:=monomial_jet_line_degree j s u v
  by_cases within : s≤j
  · have size : j+1-s=(j-s)+1 := by omega
    rw [size] at jd
    have hd : (jetMonomial h : Poly K).DegLt (h+1) := by
      have d:=Poly.degLt_length (jetMonomial h : Poly K)
      simpa only [jetMonomial,List.length_map,List.length_range] using d
    exact Poly.DegLt.mono (Poly.degLt_mul hd jd) (by omega)
  · have zero : (monomialJetAlongLine j s u v).IsZero := fun t=>jd t (by omega)
    exact fun t _=>product_zero (jetMonomial h) _ zero t
def trivariateJetPolynomial (indices : List (Nat×Nat×Nat)) (values : (Nat×Nat×Nat)→K)
    (r s : Nat) (x u v : K) : Poly K :=
  match indices with
  | [] => Poly.zero
  | index::rest => Poly.smul (values index)
      (trivariateJetTerm index.1 index.2.1 index.2.2 r s x u v)+
      trivariateJetPolynomial rest values r s x u v

theorem trivariate_jet_polynomial_degree (indices : List (Nat×Nat×Nat))
    (values : (Nat×Nat×Nat)→K) (r s Zcap : Nat) (x u v : K)
    (budget : ∀ index∈indices,index.2.1+index.2.2<Zcap) :
    (trivariateJetPolynomial indices values r s x u v).DegLt (Zcap-s) := by
  induction indices with
  | nil => intro i hi;simp [trivariateJetPolynomial,Poly.zero,Poly.coeff]
  | cons index rest ih =>
    apply Poly.degLt_add
    · apply Poly.degLt_smul
      exact trivariate_jet_term_degree _ _ _ _ _ _ _ _ _ (budget index (by simp))
    · exact ih (fun i hi=>budget i (by simp [hi]))

/-- The finite Z-coefficient equations are exact linear functionals of the
trivariate coefficient vector, not sampled evaluations in Z. -/
theorem trivariate_jet_coefficient_matrix (indices : List (Nat×Nat×Nat))
    (values : (Nat×Nat×Nat)→K) (r s t : Nat) (x u v : K) :
    (trivariateJetPolynomial indices values r s x u v).coeff t=
      kernelDot indices (fun index=>(trivariateJetTerm index.1 index.2.1 index.2.2 r s x u v).coeff t) values := by
  induction indices with
  | nil => simp [trivariateJetPolynomial,Poly.zero,Poly.coeff,kernelDot]
  | cons index rest ih =>
    simp only [trivariateJetPolynomial,Poly.coeff_add,Poly.coeff_smul,kernelDot,ih]
    grind

/-- Checking exactly Zcap-s coefficient equations forces a polynomial
identity in Z. No enumeration of field elements or large-field guard. -/
theorem trivariate_jet_constraints_zero (indices : List (Nat×Nat×Nat))
    (values : (Nat×Nat×Nat)→K) (r s Zcap : Nat) (x u v : K)
    (budget : ∀ index∈indices,index.2.1+index.2.2<Zcap)
    (equations : ∀ t<Zcap-s,kernelDot indices
      (fun index=>(trivariateJetTerm index.1 index.2.1 index.2.2 r s x u v).coeff t) values=0) :
    (trivariateJetPolynomial indices values r s x u v).IsZero := by
  intro t
  by_cases low : t<Zcap-s
  · rw [trivariate_jet_coefficient_matrix]
    exact equations t low
  · exact trivariate_jet_polynomial_degree indices values r s Zcap x u v budget t (by omega)
end NearCompression
