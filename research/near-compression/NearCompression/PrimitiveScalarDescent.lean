import NearCompression.PrimitivePolynomialProduct

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Finite polynomial linear combinations of a coefficient family, with
coefficient equality rather than list equality for the represented result. -/
inductive PolynomialRowSpan (rows : List (Poly K)) : Poly K → Prop
  | zero : PolynomialRowSpan rows Poly.zero
  | entry {p} : p∈rows → PolynomialRowSpan rows p
  | add {p q} : PolynomialRowSpan rows p → PolynomialRowSpan rows q → PolynomialRowSpan rows (p+q)
  | mul (a : Poly K) {p} : PolynomialRowSpan rows p → PolynomialRowSpan rows (a*p)
  | congr {p q} : PolynomialRowSpan rows p → PolynomialCoeffEq p q → PolynomialRowSpan rows q

private theorem span_weaken (ps qs : List (Poly K)) (inclusion : ∀p∈ps,p∈qs)
    (p : Poly K) (span : PolynomialRowSpan ps p) : PolynomialRowSpan qs p := by
  induction span with
  | zero => exact .zero
  | entry member => exact .entry (inclusion _ member)
  | add _ _ ih jh => exact .add ih jh
  | mul a _ ih => exact .mul a ih
  | congr _ same ih => exact .congr ih same

private theorem divides_trans (a b c : Poly K) (ab : PolynomialDivides a b)
    (bc : PolynomialDivides b c) : PolynomialDivides a c := by
  obtain ⟨s,bs⟩:=ab;obtain ⟨t,ct⟩:=bc
  refine ⟨t*s,?_⟩
  intro i
  rw [ct i,polynomial_mul_congr t t b (s*a) (fun _=>rfl) bs i,←polynomial_mul_assoc]

private theorem self_divides (p : Poly K) : PolynomialDivides p p := by
  refine ⟨Poly.C 1,?_⟩
  apply (formal_polynomial_eq_iff _ _).mp
  change formalPolynomial p=1*formalPolynomial p
  grind

/-- Euclidean gcd construction also gives an actual polynomial linear
combination of the finite family, not merely a greatest-divisor predicate. -/
theorem polynomial_row_span_common_divisor (rows : List (Poly K))
    (nonzero : ∃p∈rows,¬p.IsZero) :
    ∃g : Poly K,¬g.IsZero ∧ (∀p∈rows,PolynomialDivides g p) ∧ PolynomialRowSpan rows g := by
  classical
  induction rows with
  | nil => simp at nonzero
  | cons p ps ih =>
    by_cases tailNonzero : ∃q∈ps,¬q.IsZero
    · obtain ⟨g,gn,common,span⟩:=ih tailNonzero
      obtain ⟨d,A,B,dn,_,identity,dg,dp⟩:=polynomial_bezout_gcd_exists g.coeffs.length g p gn (Poly.degLt_length g)
      refine ⟨d,dn,?_,?_⟩
      · intro q member
        rcases List.mem_cons.mp member with head|tail
        · subst q;exact dp
        · exact divides_trans d g q dg (common q tail)
      · have gs : PolynomialRowSpan (p::ps) g := span_weaken ps (p::ps)
          (fun q member=>List.mem_cons.mpr (Or.inr member)) g span
        exact .congr (.add (.mul A gs) (.mul B (.entry (by simp)))) (fun i=>(identity i).symm)
    · have tailZero : ∀q∈ps,q.IsZero := by
        intro q member
        exact Classical.byContradiction (fun nz=>tailNonzero ⟨q,member,nz⟩)
      have pn : ¬p.IsZero := by
        obtain ⟨q,member,nz⟩:=nonzero
        rcases List.mem_cons.mp member with head|tail
        · simpa only [head] using nz
        · exact False.elim (nz (tailZero q tail))
      refine ⟨p,pn,?_,.entry (by simp)⟩
      intro q member
      rcases List.mem_cons.mp member with head|tail
      · subst q;exact self_divides p
      · exact ⟨Poly.zero,fun i=>tailZero q tail i⟩

/-- Primitiveness supplies a unit polynomial linear combination. This is
stronger than merely excluding common roots at base-field sample points. -/
theorem polynomial_primitive_row_span_one (rows : List (Poly K))
    (primitive : PolynomialRowsPrimitive rows) : PolynomialRowSpan rows (Poly.C 1) := by
  have nonzero : ∃p∈rows,¬p.IsZero := by
    apply Classical.byContradiction
    intro none
    have common : ∀p∈rows,PolynomialDivides (Poly.X : Poly K) p := by
      intro p member
      have zero : p.IsZero := Classical.byContradiction (fun nz=>none ⟨p,member,nz⟩)
      exact ⟨Poly.zero,fun i=>zero i⟩
    exact Field.zero_ne_one (primitive Poly.X common 1 (by omega)).symm
  obtain ⟨g,gn,common,span⟩:=polynomial_row_span_common_divisor rows nonzero
  have degree:=primitive g common
  have constant : PolynomialCoeffEq g (Poly.C (g.coeff 0)) := by
    intro i;cases i with
    | zero => rfl
    | succ i => exact degree (i+1) (by omega)
  have cn : g.coeff 0≠0 := by
    intro zero;apply gn;intro i
    rw [constant i]
    cases i with
    | zero => exact zero
    | succ i => rfl
  refine .congr (.mul (Poly.C (g.coeff 0)⁻¹) span) ?_
  have same:=(formal_polynomial_eq_iff _ _).mpr constant
  apply (formal_polynomial_eq_iff _ _).mp
  change formalPolynomial (Poly.C (g.coeff 0)⁻¹)*formalPolynomial g=1
  rw [same]
  apply (formal_polynomial_eq_iff _ _).mpr
  intro i
  change (Poly.smul (g.coeff 0)⁻¹ (Poly.C (g.coeff 0))+Poly.mk [0]).coeff i=(Poly.C 1).coeff i
  rw [Poly.coeff_add,Poly.coeff_smul]
  have inverse:=Field.mul_inv_cancel cn
  cases i with
  | zero => change (g.coeff 0)⁻¹*g.coeff 0+0=1;grind
  | succ i => change (g.coeff 0)⁻¹*0+0=0;grind

private theorem rational_zero : polynomialRationalOfPolynomial (Poly.zero : Poly K)=0 :=
  (polynomial_rational_of_polynomial_eq_iff _ _).mpr (by intro i;cases i <;> rfl)

/-- If multiplication by a rational scalar sends every generator to a
polynomial, it sends every polynomial linear combination to a polynomial. -/
theorem polynomial_row_span_scalar_integral (rows : List (Poly K)) (r : PolynomialRational K)
    (integral : ∀p∈rows,∃q : Poly K,r*polynomialRationalOfPolynomial p=polynomialRationalOfPolynomial q)
    (p : Poly K) (span : PolynomialRowSpan rows p) :
    ∃q : Poly K,r*polynomialRationalOfPolynomial p=polynomialRationalOfPolynomial q := by
  induction span with
  | zero => exact ⟨Poly.zero,by rw [rational_zero];grind⟩
  | entry member => exact integral _ member
  | @add p q _ _ ih jh =>
    obtain ⟨a,ae⟩:=ih;obtain ⟨b,be⟩:=jh
    refine ⟨a+b,?_⟩
    rw [polynomial_rational_of_polynomial_add,polynomial_rational_of_polynomial_add]
    grind
  | @mul a p _ ih =>
    obtain ⟨q,qe⟩:=ih
    refine ⟨a*q,?_⟩
    rw [polynomial_rational_of_polynomial_mul,polynomial_rational_of_polynomial_mul]
    grind
  | @congr p q _ same ih =>
    have equal:=(polynomial_rational_of_polynomial_eq_iff p q).mpr same
    rwa [←equal]

/-- Gauss scalar descent: no non-polynomial rational scalar can take a
primitive polynomial coefficient family entirely back into K[Z]. -/
theorem polynomial_primitive_scalar_descent (rows : List (Poly K))
    (primitive : PolynomialRowsPrimitive rows) (r : PolynomialRational K)
    (integral : ∀p∈rows,∃q : Poly K,r*polynomialRationalOfPolynomial p=polynomialRationalOfPolynomial q) :
    ∃q : Poly K,r=polynomialRationalOfPolynomial q := by
  obtain ⟨q,equal⟩:=polynomial_row_span_scalar_integral rows r integral (Poly.C 1)
    (polynomial_primitive_row_span_one rows primitive)
  refine ⟨q,?_⟩
  change r*1=polynomialRationalOfPolynomial q at equal
  grind

/-- Concrete polynomial-family interface for scalar descent; padding and
coefficient lists of different lengths are allowed. -/
theorem polynomial_primitive_family_scalar_descent (rows source : List (Poly K))
    (primitive : PolynomialRowsPrimitive rows) (r : PolynomialRational K)
    (identity : PolynomialCoeffEq (Poly.smul r (polynomialParameterFamily rows))
      (polynomialParameterFamily source)) : ∃q : Poly K,r=polynomialRationalOfPolynomial q := by
  apply polynomial_primitive_scalar_descent rows primitive r
  intro p member
  obtain ⟨i,hi,same⟩:=List.getElem_of_mem member
  refine ⟨source.getD i Poly.zero,?_⟩
  have eq:=identity i
  rw [Poly.coeff_smul,←polynomial_parameter_family_coefficient,←polynomial_parameter_family_coefficient] at eq
  have entry : rows.getD i Poly.zero=p := by simp [List.getD,hi,same]
  rwa [entry] at eq

private theorem embedding_nonzero (p : Poly K) (nonzero : ¬p.IsZero) :
    polynomialRationalOfPolynomial p≠0 := by
  intro zero
  have same:=polynomial_rational_polynomial_injective _ _ zero
  exact nonzero ((formal_polynomial_zero_iff _).mp same)

/-- Every nonzero K(Z)[Y] polynomial is a nonzero rational scalar times a
primitive polynomial parameter family, constructed by clearing and content. -/
theorem polynomial_primitive_rational_representation (p : Poly (PolynomialRational K))
    (nonzero : ¬p.IsZero) : ∃rows : List (Poly K),∃r : PolynomialRational K,
      r≠0 ∧ PolynomialRowsPrimitive rows ∧
      PolynomialCoeffEq p (Poly.smul r (polynomialParameterFamily rows)) := by
  obtain ⟨cleared,den,dn,identity⟩:=rational_polynomial_clearing_exists p
  have denNonzero:=embedding_nonzero den dn
  have existsRow : ∃q∈cleared,¬q.IsZero := by
    apply Classical.byContradiction
    intro none
    have allZero : ∀q∈cleared,q.IsZero := by
      intro q member
      exact Classical.byContradiction (fun nz=>none ⟨q,member,nz⟩)
    have familyZero : (polynomialParameterFamily cleared).IsZero := by
      intro i
      rw [←polynomial_parameter_family_coefficient]
      have zero : (cleared.getD i Poly.zero).IsZero := by
        by_cases hi : i<cleared.length
        · have member : cleared.getD i Poly.zero∈cleared := by
            simp only [List.getD, List.getElem?_eq_getElem hi, Option.getD_some]
            exact List.getElem_mem hi
          exact allZero _ member
        · have missing : cleared[i]?=Option.none := List.getElem?_eq_none (by omega)
          simp only [List.getD,missing,Option.getD_none]
          intro j;rfl
      have same : polynomialRationalOfPolynomial (cleared.getD i Poly.zero)=polynomialRationalOfPolynomial Poly.zero :=
        (polynomial_rational_of_polynomial_eq_iff _ _).mpr zero
      exact same.trans rational_zero
    apply nonzero
    intro i
    have entry:=familyZero i
    rw [identity,Poly.coeff_smul] at entry
    rcases Field.of_mul_eq_zero entry with zero|zero
    · exact False.elim (denNonzero zero)
    · exact zero
  obtain ⟨content,rows,cn,_,decomposition,primitive⟩:=polynomial_primitive_normalization_exists cleared existsRow
  have contentNonzero:=embedding_nonzero content cn
  have reconstruction:=polynomial_parameter_content_identity cleared rows content decomposition
  let r:=polynomialRationalOfPolynomial content*(polynomialRationalOfPolynomial den)⁻¹
  have inverse:=Field.mul_inv_cancel denNonzero
  have scalarIdentity : polynomialRationalOfPolynomial den*r=polynomialRationalOfPolynomial content := by
    dsimp [r];grind
  have rn : r≠0 := by intro zero;rw [zero] at scalarIdentity;apply contentNonzero;grind
  refine ⟨rows,r,rn,primitive,?_⟩
  intro i
  have entry:=reconstruction i
  rw [identity,Poly.coeff_smul,Poly.coeff_smul] at entry
  rw [Poly.coeff_smul]
  have cancel:=Field.mul_inv_cancel denNonzero
  dsimp [r]
  grind

private theorem family_scale (rows : List (Poly K)) (c : Poly K) :
    polynomialParameterFamily (rows.map (fun p=>c*p))=
      Poly.smul (polynomialRationalOfPolynomial c) (polynomialParameterFamily rows) := by
  unfold polynomialParameterFamily Poly.smul Poly.scaleL
  simp only [List.map_map,Function.comp_def,polynomial_rational_of_polynomial_mul]

private theorem constant_product (c : K) (p : Poly K) (i : Nat) :
    (Poly.C c*p).coeff i=c*p.coeff i := by
  change (Poly.smul c p+Poly.mk [0]).coeff i=_
  rw [Poly.coeff_add,Poly.coeff_smul]
  have zero : (Poly.mk [0] : Poly K).coeff i=0 := by cases i <;> rfl
  rw [zero];grind

private theorem scale_left (c : K) (p q : Poly K) (i : Nat) :
    (Poly.smul c p*q).coeff i=c*(p*q).coeff i := by
  have same : PolynomialCoeffEq (Poly.C c*p) (Poly.smul c p) := by
    intro j;rw [constant_product,Poly.coeff_smul]
  rw [←polynomial_mul_congr _ _ q q same (fun _=>rfl) i,polynomial_mul_assoc,constant_product]

private theorem scale_right (c : K) (p q : Poly K) (i : Nat) :
    (p*Poly.smul c q).coeff i=c*(p*q).coeff i := by
  rw [polynomial_mul_comm,scale_left,polynomial_mul_comm q p]

/-- Gauss factorization descent: a nonzero rational factorization of a
polynomial family has a primitive polynomial left factor and a polynomial
complement. The selected rational factor changes only by a nonzero scalar.
Parameter-degree inheritance is a separate subsequent obligation. -/
theorem polynomial_rational_factorization_descent (source : List (Poly K))
    (p q : Poly (PolynomialRational K)) (pn : ¬p.IsZero) (qn : ¬q.IsZero)
    (factorization : PolynomialCoeffEq (polynomialParameterFamily source) (p*q)) :
    ∃left right : List (Poly K),∃r : PolynomialRational K,r≠0 ∧
      PolynomialRowsPrimitive left ∧
      PolynomialCoeffEq p (Poly.smul r (polynomialParameterFamily left)) ∧
      PolynomialCoeffEq (polynomialParameterFamily source)
        (polynomialParameterFamily left*polynomialParameterFamily right) := by
  obtain ⟨left,a,an,lp,pa⟩:=polynomial_primitive_rational_representation p pn
  obtain ⟨right,b,_,rp,qb⟩:=polynomial_primitive_rational_representation q qn
  have scalarProduct : PolynomialCoeffEq (polynomialParameterFamily source)
      (Poly.smul (a*b) (polynomialParameterFamily (parameterRowsMul left right))) := by
    intro i
    rw [polynomial_parameter_rows_product,Poly.coeff_smul,factorization i]
    rw [polynomial_mul_congr _ _ _ _ pa qb i]
    rw [scale_left,scale_right]
    grind
  obtain ⟨c,ce⟩:=polynomial_primitive_family_scalar_descent (parameterRowsMul left right) source
    (polynomial_primitive_rows_product left right lp rp) (a*b) (fun i=>(scalarProduct i).symm)
  refine ⟨left,right.map (fun x=>c*x),a,an,lp,pa,?_⟩
  intro i
  rw [family_scale,scale_right,scalarProduct i,
    Poly.coeff_smul,polynomial_parameter_rows_product,ce]

/-- Descent preserves a selected irreducible modulus, producing a primitive
polynomial modulus and polynomial complement with an exact source identity. -/
theorem polynomial_selected_irreducible_factor_descent (source : List (Poly K))
    (p q : Poly (PolynomialRational K)) (irreducible : PolynomialIrreducible p)
    (sourceNonzero : ¬(polynomialParameterFamily source).IsZero)
    (factorization : PolynomialCoeffEq (polynomialParameterFamily source) (p*q)) :
    ∃left right : List (Poly K),∃r : PolynomialRational K,r≠0 ∧
      PolynomialRowsPrimitive left ∧ PolynomialIrreducible (polynomialParameterFamily left) ∧
      PolynomialCoeffEq p (Poly.smul r (polynomialParameterFamily left)) ∧
      (∀i,PolynomialCoeffEq (source.getD i Poly.zero) ((parameterRowsMul left right).getD i Poly.zero)) := by
  have qn : ¬q.IsZero := by
    intro zero
    have product:=(polynomial_product_zero_iff p q).mpr (Or.inr zero)
    apply sourceNonzero
    intro i;rw [factorization i];exact product i
  obtain ⟨left,right,r,rn,primitive,pr,identity⟩:=polynomial_rational_factorization_descent
    source p q irreducible.1 qn factorization
  have inverse:=Field.mul_inv_cancel rn
  have inverseNonzero : r⁻¹≠0 := by
    intro zero;rw [zero] at inverse
    apply (Field.zero_ne_one (α:=PolynomialRational K));grind
  have unscaled : PolynomialCoeffEq (Poly.smul r⁻¹ p) (polynomialParameterFamily left) := by
    intro i
    rw [Poly.coeff_smul,pr i,Poly.coeff_smul]
    grind
  have selected:=polynomial_irreducible_coeff_congr _ _ unscaled
    (polynomial_nonzero_scalar_irreducible p r⁻¹ inverseNonzero irreducible)
  refine ⟨left,right,r,rn,primitive,selected,pr,?_⟩
  intro i
  apply (polynomial_rational_of_polynomial_eq_iff _ _).mp
  rw [polynomial_parameter_family_coefficient,polynomial_parameter_family_coefficient,
    polynomial_parameter_rows_product]
  exact identity i
end NearCompression
