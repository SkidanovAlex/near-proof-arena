import NearCompression.RationalFactorClearing

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Common polynomial content with its universal divisibility property. -/
def PolynomialListContent (rows : List (Poly K)) (content : Poly K) : Prop :=
  (∀ p∈rows,PolynomialDivides content p) ∧
  ∀ d : Poly K,(∀ p∈rows,PolynomialDivides d p)→PolynomialDivides d content

private theorem divides_trans (a b c : Poly K) (ab : PolynomialDivides a b)
    (bc : PolynomialDivides b c) : PolynomialDivides a c := by
  obtain ⟨s,bs⟩:=ab;obtain ⟨t,ct⟩:=bc
  refine ⟨t*s,?_⟩
  intro i
  rw [ct i,polynomial_mul_congr t t b (s*a) (fun _=>rfl) bs i,←polynomial_mul_assoc]

private theorem divides_self (p : Poly K) : PolynomialDivides p p := by
  refine ⟨Poly.C 1,?_⟩
  intro i
  change p.coeff i=(Poly.smul 1 p+Poly.mk [0]).coeff i
  rw [Poly.coeff_add,Poly.coeff_smul]
  have zero : (Poly.mk [0] : Poly K).coeff i=0 := by cases i <;> rfl
  rw [zero];grind

/-- Euclidean gcd construction extends to any finite nonzero coefficient
family, without assuming a content oracle or unique-factorization instance. -/
theorem polynomial_list_content_exists (rows : List (Poly K))
    (nonzero : ∃ p∈rows,¬p.IsZero) :
    ∃ content : Poly K,¬content.IsZero ∧ PolynomialListContent rows content := by
  classical
  induction rows with
  | nil => simp at nonzero
  | cons p rows ih =>
    by_cases tailNonzero : ∃ q∈rows,¬q.IsZero
    · obtain ⟨g,gnz,common,greatest⟩:=ih tailNonzero
      obtain ⟨d,A,B,dnz,_,cert,dg,dp⟩:=polynomial_bezout_gcd_exists g.coeffs.length g p gnz (Poly.degLt_length g)
      refine ⟨d,dnz,?_,?_⟩
      · intro q member
        rcases List.mem_cons.mp member with head|tail
        · subst q;exact dp
        · exact divides_trans d g q dg (common q tail)
      · intro c divides
        exact polynomial_common_divisor_divides_bezout c g p d A B
          (greatest c (fun q member=>divides q (List.mem_cons.mpr (Or.inr member))))
          (divides p (by simp)) cert
    · have tailZero : ∀ q∈rows,q.IsZero := by
        intro q member
        exact Classical.byContradiction (fun nz=>tailNonzero ⟨q,member,nz⟩)
      have pnz : ¬p.IsZero := by
        obtain ⟨q,member,nz⟩:=nonzero
        rcases List.mem_cons.mp member with head|tail
        · simpa only [head] using nz
        · exact False.elim (nz (tailZero q tail))
      refine ⟨p,pnz,?_,?_⟩
      · intro q member
        rcases List.mem_cons.mp member with head|tail
        · subst q;exact divides_self p
        · exact ⟨Poly.zero,fun i=>tailZero q tail i⟩
      · intro d divides;exact divides p (by simp)

/-- Exact coefficient-list division by content, preserving positions. -/
inductive PolynomialContentDecomposition (content : Poly K) : List (Poly K)→List (Poly K)→Prop
  | nil : PolynomialContentDecomposition content [] []
  | cons {p q ps qs} : PolynomialCoeffEq p (q*content) → PolynomialContentDecomposition content ps qs →
      PolynomialContentDecomposition content (p::ps) (q::qs)

theorem polynomial_content_quotients_exist (rows : List (Poly K)) (content : Poly K)
    (common : ∀ p∈rows,PolynomialDivides content p) :
    ∃ normalized : List (Poly K),PolynomialContentDecomposition content rows normalized := by
  induction rows with
  | nil => exact ⟨[],.nil⟩
  | cons p rows ih =>
    obtain ⟨q,identity⟩:=common p (by simp)
    obtain ⟨qs,tail⟩:=ih (fun r member=>common r (List.mem_cons.mpr (Or.inr member)))
    exact ⟨q::qs,.cons identity tail⟩

private theorem common_product (content d : Poly K) (rows normalized : List (Poly K))
    (decomposition : PolynomialContentDecomposition content rows normalized)
    (common : ∀ q∈normalized,PolynomialDivides d q) : ∀ p∈rows,PolynomialDivides (d*content) p := by
  induction decomposition with
  | nil => simp
  | @cons p q ps qs identity tail ih =>
    intro r member
    rcases List.mem_cons.mp member with head|rest
    · subst r
      obtain ⟨s,eq⟩:=common q (by simp)
      refine ⟨s,?_⟩
      intro i
      rw [identity i,polynomial_mul_congr q (s*d) content content eq (fun _=>rfl) i,polynomial_mul_assoc]
    · exact ih (fun q member=>common q (List.mem_cons.mpr (Or.inr member))) r rest

/-- Primitive means no nonconstant parameter polynomial divides every row. -/
def PolynomialRowsPrimitive (rows : List (Poly K)) : Prop :=
  ∀ d : Poly K,(∀ p∈rows,PolynomialDivides d p)→d.DegLt 1

/-- Dividing by a greatest common content really removes all nonconstant
common factors; this is proved by cancellation in the formal polynomial ring. -/
theorem polynomial_content_quotient_primitive (rows normalized : List (Poly K)) (content : Poly K)
    (nonzero : ¬content.IsZero) (greatest : PolynomialListContent rows content)
    (decomposition : PolynomialContentDecomposition content rows normalized) : PolynomialRowsPrimitive normalized := by
  intro d common
  have divides:=greatest.2 (d*content) (common_product content d rows normalized decomposition common)
  obtain ⟨s,identity⟩:=divides
  have formal:=(formal_polynomial_eq_iff _ _).mpr identity
  change formalPolynomial content=formalPolynomial s*(formalPolynomial d*formalPolynomial content) at formal
  have cn : formalPolynomial content≠0 := fun zero=>nonzero ((formal_polynomial_zero_iff _).mp zero)
  have product : (formalPolynomial s*formalPolynomial d)*formalPolynomial content=1*formalPolynomial content := by grind
  have unit:=formal_polynomial_cancel _ _ _ cn product
  have dunit : PolynomialDivides d (Poly.C (1:K)) := by
    refine ⟨s,?_⟩
    apply (formal_polynomial_eq_iff _ _).mp
    exact unit.symm
  exact polynomial_divisor_degree (Poly.C 1) d 1
    (fun zero=>Field.zero_ne_one (zero 0).symm) (Poly.degLt_length _) dunit

/-- Every nonzero polynomial coefficient family admits primitive normalization
with an explicit common factor and exact coefficientwise reconstruction. -/
theorem polynomial_primitive_normalization_exists (rows : List (Poly K))
    (nonzero : ∃ p∈rows,¬p.IsZero) :
    ∃ content : Poly K,∃ normalized : List (Poly K),¬content.IsZero ∧
      PolynomialListContent rows content ∧ PolynomialContentDecomposition content rows normalized ∧
      PolynomialRowsPrimitive normalized := by
  obtain ⟨content,cn,common⟩:=polynomial_list_content_exists rows nonzero
  obtain ⟨normalized,decomposition⟩:=polynomial_content_quotients_exist rows content common.1
  exact ⟨content,normalized,cn,common,decomposition,
    polynomial_content_quotient_primitive rows normalized content cn common decomposition⟩
/-- Content reconstruction is exactly scalar reconstruction after embedding
parameter polynomials into K(Z); coefficientwise equality permits padding. -/
theorem polynomial_parameter_content_identity (rows normalized : List (Poly K)) (content : Poly K)
    (decomposition : PolynomialContentDecomposition content rows normalized) :
    PolynomialCoeffEq (polynomialParameterFamily rows)
      (Poly.smul (polynomialRationalOfPolynomial content) (polynomialParameterFamily normalized)) := by
  intro i
  induction decomposition generalizing i with
  | nil => rw [Poly.coeff_smul];change (0:PolynomialRational K)=_*0;grind
  | @cons p q ps qs identity tail ih => cases i with
    | zero =>
      rw [Poly.coeff_smul]
      change polynomialRationalOfPolynomial p=polynomialRationalOfPolynomial content*polynomialRationalOfPolynomial q
      have eq:=(polynomial_rational_of_polynomial_eq_iff _ _).mpr identity
      rw [polynomial_rational_of_polynomial_mul] at eq
      grind
    | succ i => exact ih i

/-- Formal irreducibility is independent of trailing-zero representations. -/
theorem polynomial_irreducible_coeff_congr (p q : Poly K) (same : PolynomialCoeffEq p q)
    (irreducible : PolynomialIrreducible p) : PolynomialIrreducible q := by
  refine ⟨?_,?_,?_⟩
  · intro zero;apply irreducible.1;intro i;rw [same i];exact zero i
  · intro degree;apply irreducible.2.1;intro i hi;rw [same i];exact degree i hi
  · intro a b identity
    exact irreducible.2.2 a b (fun i=>(same i).trans (identity i))

/-- Removing nonzero content preserves the selected modulus's irreducibility
over K(Z), so primitive normalization does not change the branch factor. -/
theorem polynomial_content_normalized_irreducible (rows normalized : List (Poly K)) (content : Poly K)
    (nonzero : ¬content.IsZero) (decomposition : PolynomialContentDecomposition content rows normalized)
    (irreducible : PolynomialIrreducible (polynomialParameterFamily rows)) :
    PolynomialIrreducible (polynomialParameterFamily normalized) := by
  have cn : polynomialRationalOfPolynomial content≠0 := by
    intro zero
    have formal:=polynomial_rational_polynomial_injective _ _ zero
    exact nonzero ((formal_polynomial_zero_iff _).mp formal)
  have inverse:=Field.mul_inv_cancel cn
  have inverseNonzero : (polynomialRationalOfPolynomial content)⁻¹≠0 := by
    intro zero;rw [zero] at inverse
    have impossible : (0:PolynomialRational K)=1 := by grind
    exact Field.zero_ne_one impossible
  have reconstruction:=polynomial_parameter_content_identity rows normalized content decomposition
  have same : PolynomialCoeffEq
      (Poly.smul (polynomialRationalOfPolynomial content)⁻¹ (polynomialParameterFamily rows))
      (polynomialParameterFamily normalized) := by
    intro i
    rw [Poly.coeff_smul,reconstruction i,Poly.coeff_smul]
    grind
  exact polynomial_irreducible_coeff_congr _ _ same
    (polynomial_nonzero_scalar_irreducible _ _ inverseNonzero irreducible)
end NearCompression
