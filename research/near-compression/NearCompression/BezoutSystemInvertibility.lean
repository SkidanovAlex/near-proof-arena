import NearCompression.BoundedBezout

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Euclid's divisibility lemma derived from an actual unit certificate. -/
theorem polynomial_bezout_coprime_divisibility (p q A B r : Poly K)
    (certificate : PolynomialCoeffEq (A*p+B*q) (Poly.C 1))
    (divides : PolynomialDivides q (p*r)) : PolynomialDivides q r := by
  obtain ⟨t,identity⟩:=divides
  have cert:=(formal_polynomial_eq_iff _ _).mpr certificate
  have product:=(formal_polynomial_eq_iff _ _).mpr identity
  change formalPolynomial A*formalPolynomial p+formalPolynomial B*formalPolynomial q=1 at cert
  change formalPolynomial p*formalPolynomial r=formalPolynomial t*formalPolynomial q at product
  refine ⟨A*t+B*r,?_⟩
  apply (formal_polynomial_eq_iff _ _).mp
  change formalPolynomial r=(formalPolynomial A*formalPolynomial t+formalPolynomial B*formalPolynomial r)*formalPolynomial q
  grind

/-- No nontrivial bounded syzygy survives a unit Bezout certificate. This is
the zero-kernel property of the finite coefficient system. -/
theorem polynomial_bounded_bezout_kernel (p q A B U V : Poly K) (n : Nat)
    (ql : q.coeff n≠0) (ud : U.DegLt n)
    (certificate : PolynomialCoeffEq (A*p+B*q) (Poly.C 1))
    (kernel : (U*p+V*q).IsZero) : U.IsZero ∧ V.IsZero := by
  have equation:=(formal_polynomial_zero_iff _).mpr kernel
  change formalPolynomial U*formalPolynomial p+formalPolynomial V*formalPolynomial q=0 at equation
  have divides : PolynomialDivides q (p*U) := by
    refine ⟨-V,?_⟩
    apply (formal_polynomial_eq_iff _ _).mp
    change formalPolynomial p*formalPolynomial U= -formalPolynomial V*formalPolynomial q
    grind
  have qu:=polynomial_bezout_coprime_divisibility p q A B U certificate divides
  have uz : U.IsZero := by
    apply Classical.byContradiction
    intro nonzero
    have impossible:=polynomial_divisor_degree U q n nonzero ud qu
    exact ql (impossible n (Nat.le_refl n))
  have ueq:=(formal_polynomial_zero_iff U).mpr uz
  have vq : formalPolynomial V*formalPolynomial q=0 := by grind
  have qnz : formalPolynomial q≠0 := fun zero=>ql ((formal_polynomial_zero_iff q).mp zero n)
  have vz : formalPolynomial V=0 := by
    rcases formal_polynomial_mul_zero _ _ vq with zero|zero
    · exact zero
    · exact False.elim (qnz zero)
  exact ⟨uz,(formal_polynomial_zero_iff V).mp vz⟩

/-- Bounded solutions of the same coefficient system are formally unique. -/
theorem polynomial_bounded_bezout_unique (p q A B U V U' V' : Poly K) (n : Nat)
    (ql : q.coeff n≠0) (ud : U.DegLt n) (ud' : U'.DegLt n)
    (certificate : PolynomialCoeffEq (A*p+B*q) (Poly.C 1))
    (same : PolynomialCoeffEq (U*p+V*q) (U'*p+V'*q)) :
    PolynomialCoeffEq U U' ∧ PolynomialCoeffEq V V' := by
  have equation:=(formal_polynomial_eq_iff _ _).mpr same
  change formalPolynomial U*formalPolynomial p+formalPolynomial V*formalPolynomial q=
    formalPolynomial U'*formalPolynomial p+formalPolynomial V'*formalPolynomial q at equation
  have kernel : ((U-U')*p+(V-V')*q).IsZero := by
    apply (formal_polynomial_zero_iff _).mp
    change (formalPolynomial U-formalPolynomial U')*formalPolynomial p+
      (formalPolynomial V-formalPolynomial V')*formalPolynomial q=0
    grind
  have zero:=polynomial_bounded_bezout_kernel p q A B (U-U') (V-V') n ql
    (Poly.degLt_sub ud ud') certificate kernel
  constructor
  · intro i;have entry:=zero.1 i;rw [Poly.coeff_sub] at entry;grind
  · intro i;have entry:=zero.2 i;rw [Poly.coeff_sub] at entry;grind

private theorem bounded_product (a b : Poly K) (m n : Nat)
    (ad : a.DegLt m) (bd : b.DegLt (n+1)) : (a*b).DegLt (m+n) := by
  cases m with
  | zero =>
    have zero : a.IsZero := fun i=>ad i (Nat.zero_le i)
    have product:=(polynomial_product_zero_iff a b).mpr (Or.inl zero)
    exact fun i _=>product i
  | succ m =>
    have bound:=Poly.degLt_mul ad bd
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bound

/-- Every target below degree m+n has a bounded preimage. Together with the
zero-kernel theorem this proves invertibility of the Bezout coefficient map. -/
theorem polynomial_bounded_bezout_surjective (p q A B target : Poly K) (m n : Nat)
    (pd : p.DegLt (m+1)) (qd : q.DegLt (n+1)) (ql : q.coeff n≠0)
    (certificate : PolynomialCoeffEq (A*p+B*q) (Poly.C 1))
    (td : target.DegLt (m+n)) :
    ∃ U V : Poly K, U.DegLt n ∧ V.DegLt m ∧ PolynomialCoeffEq (U*p+V*q) target := by
  obtain ⟨t,r,_,rd,division⟩:=polynomial_division_bounded q n (A*target).coeffs.length qd ql (A*target)
    (Poly.DegLt.mono (Poly.degLt_length _) (by omega))
  let s:=B*target+t*p
  have cert:=(formal_polynomial_eq_iff _ _).mpr certificate
  change formalPolynomial A*formalPolynomial p+formalPolynomial B*formalPolynomial q=1 at cert
  have eq:=(formal_polynomial_eq_iff _ _).mpr division
  change formalPolynomial A*formalPolynomial target=formalPolynomial t*formalPolynomial q+formalPolynomial r at eq
  have solved : PolynomialCoeffEq (r*p+s*q) target := by
    apply (formal_polynomial_eq_iff _ _).mp
    change formalPolynomial r*formalPolynomial p+
      (formalPolynomial B*formalPolynomial target+formalPolynomial t*formalPolynomial p)*formalPolynomial q=formalPolynomial target
    grind
  have rpDegree : (r*p).DegLt (m+n) := by
    simpa only [Nat.add_comm] using bounded_product r p n m rd pd
  have sqDegree : (s*q).DegLt (m+n) := by
    intro i hi
    have entry:=solved i
    rw [Poly.coeff_add,rpDegree i hi,td i hi] at entry
    grind
  have sd : s.DegLt m := by
    by_cases sz : s.IsZero
    · exact fun i _=>sz i
    · obtain ⟨j,_,_,jd,jl,_⟩:=polynomial_division_exists Poly.zero s sz
      have bound : j<m := by
        apply Classical.byContradiction
        intro bad
        have entry:=sqDegree (j+n) (by omega)
        rw [polynomial_leading_product s q j n jd qd] at entry
        rcases Field.of_mul_eq_zero entry with zero|zero
        · exact jl zero
        · exact ql zero
      exact Poly.DegLt.mono jd bound
  exact ⟨r,s,rd,sd,solved⟩
end NearCompression
