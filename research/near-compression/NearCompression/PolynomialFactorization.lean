import NearCompression.PolynomialFieldTransport

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem cons_product (c : K) (cs : List K) (q : Poly K) (i : Nat) :
    ((Poly.mk (c::cs))*q).coeff i=c*q.coeff i+
      (match i with | 0=>0 | j+1=>((Poly.mk cs)*q).coeff j) := by
  change (Poly.smul c q+Poly.mk (0::Poly.mulL cs q.coeffs)).coeff i=_
  rw [Poly.coeff_add,Poly.coeff_smul]
  cases i <;> rfl

/-- The highest possible coefficient of a product is the product of the
leading coefficients, independently of coefficient-list padding. -/
theorem polynomial_leading_product (p q : Poly K) (m n : Nat)
    (hp : p.DegLt (m+1)) (hq : q.DegLt (n+1)) :
    (p*q).coeff (m+n)=p.coeff m*q.coeff n := by
  induction m generalizing p with
  | zero =>
    have same : PolynomialCoeffEq p (Poly.C (p.coeff 0)) := by
      intro i
      cases i with
      | zero => rfl
      | succ i => exact hp (i+1) (by omega)
    rw [polynomial_mul_congr _ _ q q same (fun _=>rfl)]
    simp only [Nat.zero_add]
    change (Poly.smul (p.coeff 0) q+Poly.mk [0]).coeff n=_
    rw [Poly.coeff_add,Poly.coeff_smul]
    have hz : (Poly.mk [0] : Poly K).coeff n=0 := by cases n <;> rfl
    rw [hz];grind
  | succ m ih =>
    cases p with | mk cs => cases cs with
      | nil => change (0:K)=0*q.coeff n;grind
      | cons c cs =>
        rw [cons_product]
        have index : m+1+n=(m+n)+1 := by omega
        rw [index]
        change c*q.coeff (m+n+1)+((Poly.mk cs)*q).coeff (m+n)=_
        rw [hq (m+n+1) (by omega),ih (Poly.mk cs) (by intro i hi;exact hp (i+1) (by omega))]
        change c*0+(Poly.mk cs).coeff m*q.coeff n=(Poly.mk cs).coeff m*q.coeff n
        grind

/-- Any decomposition into two nonconstant factors strictly decreases degree
on both sides. Nonzeroness of factors follows from the input, not an oracle. -/
theorem polynomial_proper_factor_degrees (p a b : Poly K) (D : Nat)
    (nonzero : ¬p.IsZero) (degree : p.DegLt (D+1))
    (identity : PolynomialCoeffEq p (a*b))
    (ac : ¬a.DegLt 1) (bc : ¬b.DegLt 1) :
    ∃ m n, a.DegLt (m+1) ∧ b.DegLt (n+1) ∧
      a.coeff m≠0 ∧ b.coeff n≠0 ∧ 0<m ∧ 0<n ∧ m<D ∧ n<D := by
  have product : ¬(a*b).IsZero := by
    intro zero;apply nonzero;intro i;rw [identity i,zero i]
  have an : ¬a.IsZero := by intro zero;exact product ((polynomial_product_zero_iff a b).mpr (Or.inl zero))
  have bn : ¬b.IsZero := by intro zero;exact product ((polynomial_product_zero_iff a b).mpr (Or.inr zero))
  obtain ⟨m,_,_,ad,al,_⟩:=polynomial_division_exists Poly.zero a an
  obtain ⟨n,_,_,bd,bl,_⟩:=polynomial_division_exists Poly.zero b bn
  have mp : 0<m := by cases m with | zero => exact False.elim (ac ad) | succ m => omega
  have np : 0<n := by cases n with | zero => exact False.elim (bc bd) | succ n => omega
  have bound : m+n<D+1 := by
    apply Classical.byContradiction
    intro bad
    have h:=degree (m+n) (by omega)
    rw [identity,polynomial_leading_product a b m n ad bd] at h
    rcases Field.of_mul_eq_zero h with h|h
    · exact al h
    · exact bl h
  exact ⟨m,n,ad,bd,al,bl,mp,np,by omega,by omega⟩

/-- A finite factorization tree retaining every irreducible factor and scalar.
Coefficient equality permits arbitrary trailing zeros in the input. -/
inductive PolynomialFactorTree (K : Type) [Field K] where
  | scalar : K → PolynomialFactorTree K
  | factor : Poly K → PolynomialFactorTree K
  | product : PolynomialFactorTree K → PolynomialFactorTree K → PolynomialFactorTree K

def PolynomialFactorTree.value : PolynomialFactorTree K → Poly K
  | .scalar c => Poly.C c
  | .factor p => p
  | .product a b => a.value*b.value

def PolynomialFactorTree.Valid : PolynomialFactorTree K → Prop
  | .scalar c => c≠0
  | .factor p => PolynomialIrreducible p
  | .product a b => a.Valid ∧ b.Valid

/-- Every nonzero polynomial factors into nonzero scalars and irreducibles.
Classical existence only; this does not claim an efficient factoring algorithm. -/
theorem polynomial_irreducible_factorization (p : Poly K) (nonzero : ¬p.IsZero) :
    ∃ t : PolynomialFactorTree K, t.Valid ∧ PolynomialCoeffEq p t.value := by
  have bounded : ∀ D : Nat, ∀ p : Poly K, ¬p.IsZero → p.DegLt (D+1) →
      ∃ t : PolynomialFactorTree K, t.Valid ∧ PolynomialCoeffEq p t.value := by
    intro D
    induction D using Nat.strongRecOn with
    | ind D ih =>
      intro p pn pd
      by_cases constant : p.DegLt 1
      · refine ⟨.scalar (p.coeff 0),?_,?_⟩
        · change p.coeff 0≠0
          intro zero;apply pn;intro i
          cases i with | zero => exact zero | succ i => exact constant (i+1) (by omega)
        · intro i
          cases i with | zero => rfl | succ i => exact constant (i+1) (by omega)
      · by_cases irreducible : PolynomialIrreducible p
        · exact ⟨.factor p,irreducible,fun _=>rfl⟩
        · have split : ∃ a b : Poly K, PolynomialCoeffEq p (a*b) ∧ ¬a.DegLt 1 ∧ ¬b.DegLt 1 := by
            apply Classical.byContradiction
            intro no
            apply irreducible
            refine ⟨pn,constant,?_⟩
            intro a b identity
            by_cases ac : a.DegLt 1
            · exact Or.inl ac
            · apply Or.inr
              apply Classical.byContradiction
              intro bc
              exact no ⟨a,b,identity,ac,bc⟩
          obtain ⟨a,b,identity,ac,bc⟩:=split
          obtain ⟨m,n,ad,bd,al,bl,_,_,ml,nl⟩:=polynomial_proper_factor_degrees p a b D pn pd identity ac bc
          obtain ⟨ta,va,ea⟩:=ih m ml a (fun zero=>al (zero m)) ad
          obtain ⟨tb,vb,eb⟩:=ih n nl b (fun zero=>bl (zero n)) bd
          exact ⟨.product ta tb,⟨va,vb⟩,fun i=>(identity i).trans (polynomial_mul_congr a ta.value b tb.value ea eb i)⟩
  exact bounded p.coeffs.length p nonzero (Poly.DegLt.mono (Poly.degLt_length p) (by omega))

private theorem divisor_product_left (q a b : Poly K) (divides : PolynomialDivides q a) :
    PolynomialDivides q (a*b) := by
  obtain ⟨s,hs⟩:=divides
  refine ⟨b*s,?_⟩
  intro i
  rw [polynomial_mul_comm a b,polynomial_mul_congr b b a (s*q) (fun _=>rfl) hs,
    ←polynomial_mul_assoc]

/-- Extract an irreducible divisor from any nonconstant input. This supplies
the modulus needed for a root extension; the quotient field is still separate. -/
theorem polynomial_irreducible_divisor_exists (p : Poly K)
    (nonzero : ¬p.IsZero) (nonconstant : ¬p.DegLt 1) :
    ∃ q : Poly K, PolynomialIrreducible q ∧ PolynomialDivides q p := by
  obtain ⟨t,valid,equal⟩:=polynomial_irreducible_factorization p nonzero
  have extract : ∀ t : PolynomialFactorTree K, t.Valid → ¬t.value.DegLt 1 →
      ∃ q : Poly K, PolynomialIrreducible q ∧ PolynomialDivides q t.value := by
    intro t
    induction t with
    | scalar c =>
      intro _ nc
      exact False.elim (nc (Poly.degLt_length (Poly.C c)))
    | factor q =>
      intro valid _
      refine ⟨q,valid,Poly.C 1,?_⟩
      intro i
      change q.coeff i=(Poly.mk (1::[])*q).coeff i
      rw [cons_product]
      cases i <;> change q.coeff _=1*q.coeff _+0 <;> grind
    | product a b ia ib =>
      intro valid nc
      by_cases ac : a.value.DegLt 1
      · have bc : ¬b.value.DegLt 1 := by
          intro bc
          exact nc (Poly.degLt_mul ac bc)
        obtain ⟨q,qi,qd⟩:=ib valid.2 bc
        obtain ⟨s,eq⟩:=divisor_product_left q b.value a.value qd
        exact ⟨q,qi,s,fun i=>(polynomial_mul_comm a.value b.value i).trans (eq i)⟩
      · obtain ⟨q,qi,qd⟩:=ia valid.1 ac
        exact ⟨q,qi,divisor_product_left q a.value b.value qd⟩
  have nc : ¬t.value.DegLt 1 := by
    intro degree;apply nonconstant;intro i hi;rw [equal i];exact degree i hi
  obtain ⟨q,qi,s,eq⟩:=extract t valid nc
  exact ⟨q,qi,s,fun i=>(equal i).trans (eq i)⟩

/-- A divisor of a nonzero polynomial inherits its degree bound. This links
interpolation degree budgets to every selected irreducible factor. -/
theorem polynomial_divisor_degree (p q : Poly K) (D : Nat)
    (nonzero : ¬p.IsZero) (degree : p.DegLt D) (divides : PolynomialDivides q p) :
    q.DegLt D := by
  obtain ⟨s,identity⟩:=divides
  have product : ¬(s*q).IsZero := by intro zero;apply nonzero;intro i;rw [identity i,zero i]
  have sn : ¬s.IsZero := by intro zero;exact product ((polynomial_product_zero_iff s q).mpr (Or.inl zero))
  have qn : ¬q.IsZero := by intro zero;exact product ((polynomial_product_zero_iff s q).mpr (Or.inr zero))
  obtain ⟨m,_,_,sd,sl,_⟩:=polynomial_division_exists Poly.zero s sn
  obtain ⟨n,_,_,qd,ql,_⟩:=polynomial_division_exists Poly.zero q qn
  have bound : m+n<D := by
    apply Classical.byContradiction
    intro bad
    have h:=degree (m+n) (by omega)
    rw [identity,polynomial_leading_product s q m n sd qd] at h
    rcases Field.of_mul_eq_zero h with h|h
    · exact sl h
    · exact ql h
  exact Poly.DegLt.mono qd (by omega)

/-- Every irreducible factor under the characteristic budget has a unit
certificate against its derivative, even when the original has repeated factors. -/
theorem small_degree_irreducible_divisor_bezout (characteristic : Nat)
    [IsCharP K characteristic] (p q : Poly K)
    (nonzero : ¬p.IsZero) (degree : p.DegLt characteristic)
    (irreducible : PolynomialIrreducible q) (divides : PolynomialDivides q p) :
    ∃ A B : Poly K, PolynomialCoeffEq (A*q+B*polynomialDerivative q) (Poly.C 1) := by
  have bound:=polynomial_divisor_degree p q characteristic nonzero degree divides
  obtain ⟨d,_,_,qd,ql,_⟩:=polynomial_division_exists Poly.zero q irreducible.1
  have positive : 0<d := by
    cases d with | zero => exact False.elim (irreducible.2.1 qd) | succ d => omega
  have small : d<characteristic := by
    apply Classical.byContradiction
    intro bad
    exact ql (bound d (by omega))
  exact irreducible_derivative_bezout characteristic q d irreducible qd ql positive small
end NearCompression
