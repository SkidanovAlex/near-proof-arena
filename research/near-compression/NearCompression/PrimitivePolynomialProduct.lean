import NearCompression.PolynomialContentNormalization

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Dense addition and multiplication in K[Z][Y], retaining polynomial rows. -/
def parameterRowsAdd : List (Poly K) → List (Poly K) → List (Poly K)
  | [], qs => qs
  | ps, [] => ps
  | p::ps, q::qs => (p+q)::parameterRowsAdd ps qs

def parameterRowsMul : List (Poly K) → List (Poly K) → List (Poly K)
  | [], _ => []
  | p::ps, qs => parameterRowsAdd (qs.map (fun q=>p*q)) (Poly.zero::parameterRowsMul ps qs)

private theorem map_add {L : Type} [CommRing L] (f : Poly K → L)
    (add : ∀ p q,f (p+q)=f p+f q) (ps qs : List (Poly K)) :
    (parameterRowsAdd ps qs).map f=Poly.addL (ps.map f) (qs.map f) := by
  induction ps generalizing qs with
  | nil => rfl
  | cons p ps ih => cases qs with
    | nil => rfl
    | cons q qs => simp only [parameterRowsAdd,List.map_cons,Poly.addL,add,ih]

private theorem map_mul {L : Type} [CommRing L] (f : Poly K → L)
    (zero : f Poly.zero=0) (add : ∀ p q,f (p+q)=f p+f q)
    (mul : ∀ p q,f (p*q)=f p*f q) (ps qs : List (Poly K)) :
    (parameterRowsMul ps qs).map f=Poly.mulL (ps.map f) (qs.map f) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [parameterRowsMul,map_add f add,List.map_map,List.map_cons,zero,ih,Poly.mulL,Poly.scaleL]
    congr 2
    funext q
    exact mul p q

/-- Dense row multiplication is exactly multiplication in K(Z)[Y]. -/
theorem polynomial_parameter_rows_product (ps qs : List (Poly K)) :
    polynomialParameterFamily (parameterRowsMul ps qs)=
      polynomialParameterFamily ps*polynomialParameterFamily qs := by
  apply congrArg Poly.mk
  exact map_mul polynomialRationalOfPolynomial
    ((polynomial_rational_of_polynomial_eq_iff _ _).mpr (by intro i;cases i <;> rfl))
    polynomial_rational_of_polynomial_add polynomial_rational_of_polynomial_mul ps qs

private theorem residue_zero (h : Poly K) : polynomialResidueClass h Poly.zero=(0:PolynomialResidue h) := by
  apply (polynomial_residue_class_eq_iff h _ _).mpr
  apply polynomial_residue_of_coeff_eq
  intro i;cases i <;> rfl

/-- Reduction modulo a parameter polynomial commutes with dense products.
For an irreducible modulus the target is the already constructed residue field. -/
theorem polynomial_parameter_rows_residue_product (h : Poly K) (ps qs : List (Poly K)) :
    Poly.mk ((parameterRowsMul ps qs).map (polynomialResidueClass h))=
      (Poly.mk (ps.map (polynomialResidueClass h)))*(Poly.mk (qs.map (polynomialResidueClass h))) := by
  apply congrArg Poly.mk
  exact map_mul (polynomialResidueClass h) (residue_zero h) (fun _ _=>rfl) (fun _ _=>rfl) ps qs

private theorem mapped_zero_iff (h : Poly K) (ps : List (Poly K)) :
    (Poly.mk (ps.map (polynomialResidueClass h))).IsZero ↔ ∀p∈ps,PolynomialDivides h p := by
  induction ps with
  | nil => simp only [List.not_mem_nil,false_implies,implies_true]
           exact ⟨fun _=>True.intro,fun _ _=>rfl⟩
  | cons p ps ih =>
    constructor
    · intro zero q member
      rcases List.mem_cons.mp member with head|tail
      · subst q
        apply (polynomial_residue_zero_iff h p).mp
        exact (zero 0).trans (residue_zero h).symm
      · exact ih.mp (fun i=>zero (i+1)) q tail
    · intro common i
      cases i with
      | zero => exact ((polynomial_residue_zero_iff h p).mpr (common p (by simp))).trans (residue_zero h)
      | succ i => exact ih.mpr (fun q member=>common q (List.mem_cons.mpr (Or.inr member))) i

/-- A primitive coefficient family stays nonzero modulo every irreducible
parameter polynomial. This includes characteristic two and padded zero rows. -/
theorem polynomial_primitive_residue_nonzero (ps : List (Poly K))
    (primitive : PolynomialRowsPrimitive ps) (h : Poly K) (irreducible : PolynomialIrreducible h) :
    ¬(Poly.mk (ps.map (polynomialResidueClass h))).IsZero := by
  intro zero
  exact irreducible.2.1 (primitive h ((mapped_zero_iff h ps).mp zero))

private theorem divides_trans (a b c : Poly K) (ab : PolynomialDivides a b)
    (bc : PolynomialDivides b c) : PolynomialDivides a c := by
  obtain ⟨s,bs⟩:=ab;obtain ⟨t,ct⟩:=bc
  refine ⟨t*s,?_⟩
  intro i
  rw [ct i,polynomial_mul_congr t t b (s*a) (fun _=>rfl) bs i,←polynomial_mul_assoc]

private theorem nonconstant_divisor (d : Poly K) (nonconstant : ¬d.DegLt 1) :
    ∃h,PolynomialIrreducible h ∧ PolynomialDivides h d := by
  by_cases zero : d.IsZero
  · obtain ⟨h,irreducible,_⟩:=polynomial_irreducible_divisor_exists (Poly.X : Poly K)
      (fun zero=>Field.zero_ne_one (zero 1).symm)
      (fun degree=>Field.zero_ne_one (degree 1 (by omega)).symm)
    exact ⟨h,irreducible,Poly.zero,fun i=>zero i⟩
  · exact polynomial_irreducible_divisor_exists d zero nonconstant

/-- Gauss's primitive-product lemma for explicit K[Z][Y] coefficient lists.
The proof reduces modulo an irreducible common divisor and uses the constructed
residue field, rather than assuming unique factorization of bivariate data. -/
theorem polynomial_primitive_rows_product (ps qs : List (Poly K))
    (pp : PolynomialRowsPrimitive ps) (qp : PolynomialRowsPrimitive qs) :
    PolynomialRowsPrimitive (parameterRowsMul ps qs) := by
  intro d common
  apply Classical.byContradiction
  intro nonconstant
  obtain ⟨h,irreducible,hd⟩:=nonconstant_divisor d nonconstant
  letI := polynomialResidueField h irreducible
  have zero : (Poly.mk ((parameterRowsMul ps qs).map (polynomialResidueClass h))).IsZero :=
    (mapped_zero_iff h _).mpr (fun p member=>divides_trans h d p hd (common p member))
  rw [polynomial_parameter_rows_residue_product] at zero
  exact polynomial_product_nonzero _ _
    (polynomial_primitive_residue_nonzero ps pp h irreducible)
    (polynomial_primitive_residue_nonzero qs qp h irreducible) zero
end NearCompression
