import NearCompression.TrivariateInterpolation

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

private def sumK {A : Type} (xs : List A) (f : A→K) : K :=
  match xs with
  | [] => 0
  | x::rest => f x+sumK rest f

private theorem sum_congr {A : Type} (xs : List A) (f g : A→K)
    (same : ∀ x∈xs,f x=g x) : sumK xs f=sumK xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have head:=same x (by simp)
    have tail:=ih (fun y hy=>same y (by simp [hy]))
    simp only [sumK,head,tail]

private theorem sum_add {A : Type} (xs : List A) (f g : A→K) :
    sumK xs (fun x=>f x+g x)=sumK xs f+sumK xs g := by
  induction xs with
  | nil => simp only [sumK];grind
  | cons x xs ih => simp only [sumK,ih];grind

private theorem sum_zero {A : Type} (xs : List A) : sumK xs (fun _=>(0:K))=0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sumK,ih];grind

private theorem sum_scale {A : Type} (xs : List A) (c : K) (f : A→K) :
    sumK xs (fun x=>c*f x)=c*sumK xs f := by
  induction xs with
  | nil => simp only [sumK];grind
  | cons x xs ih => simp only [sumK,ih];grind

private theorem sum_swap {A B : Type} (xs : List A) (ys : List B) (f : A→B→K) :
    sumK xs (fun x=>sumK ys (f x))=sumK ys (fun y=>sumK xs (fun x=>f x y)) := by
  induction xs with
  | nil => simp only [sumK,sum_zero]
  | cons x xs ih => simp only [sumK,sum_add,ih]

private theorem sum_append {A : Type} (xs ys : List A) (f : A→K) :
    sumK (xs++ys) f=sumK xs f+sumK ys f := by
  induction xs with
  | nil => simp only [List.nil_append,sumK];grind
  | cons x xs ih => simp only [List.cons_append,sumK,ih];grind

private theorem sum_map {A B : Type} (xs : List A) (f : A→B) (g : B→K) :
    sumK (xs.map f) g=sumK xs (fun x=>g (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,sumK,ih]

private theorem sum_flatMap {A B : Type} (xs : List A) (f : A→List B) (g : B→K) :
    sumK (xs.flatMap f) g=sumK xs (fun x=>sumK (f x) g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,sum_append,sumK,ih]

private theorem dot_sum {A : Type} (xs : List A) (row values : A→K) :
    kernelDot xs row values=sumK xs (fun x=>row x*values x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [kernelDot,sumK,ih]

def gsSpecializedValues (DZ : Nat) (values : (Nat×Nat×Nat)→K) (z : K) (index : Nat×Nat) : K :=
  kernelDot (List.range (DZ-index.2)) (fun h=>(jetMonomial h).eval z)
    (fun h=>values (index.1,index.2,h))

def gsSpecialization (k DX height DZ : Nat) (values : (Nat×Nat×Nat)→K) (z : K) : List (Poly K) :=
  gsEncode k DX height (gsSpecializedValues DZ values z)

private theorem jet_polynomial_eval (indices : List (Nat×Nat×Nat)) (values : (Nat×Nat×Nat)→K)
    (r s : Nat) (x u v z : K) :
    (trivariateJetPolynomial indices values r s x u v).eval z=
      sumK indices (fun index=>(jetMonomial index.2.2).eval z*
        gsMixedRow x (u+z*v) r s (index.1,index.2.1)*values index) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    simp only [trivariateJetPolynomial,Poly.eval_add,Poly.eval_smul,trivariate_jet_term_eval,sumK,ih]
    grind

/-- Specialization preserves the weighted X/Y budget. It need not preserve
nonzeroness: some Z values may annihilate all specialized coefficients. -/
theorem gs_specialization_degree (k DX height DZ : Nat) (values : (Nat×Nat×Nat)→K) (z : K) :
    BivariateWeightedDegree (gsSpecialization k DX height DZ values z) k DX :=
  gs_encode_weighted_degree k DX height (gsSpecializedValues DZ values z)

/-- The actual translated coefficient of the dense bivariate specialization
is evaluation of the sparse mixed-jet polynomial in Z. -/
theorem gs_specialization_mixed_jet (k DX height DZ : Nat) (values : (Nat×Nat×Nat)→K)
    (r s : Nat) (x u v z : K) :
    ((bivariateTranslate (gsSpecialization k DX height DZ values z) x (u+z*v)).getD s Poly.zero).coeff r=
      (trivariateJetPolynomial (gsTrivariateMonomials k DX height DZ) values r s x u v).eval z := by
  unfold gsSpecialization
  rw [gs_mixed_matrix_correct,jet_polynomial_eval,dot_sum]
  simp only [gsMonomials,gsTrivariateMonomials,sum_flatMap,sum_map,Nat.zero_mul,Nat.sub_zero]
  apply sum_congr
  intro j hj
  change sumK (List.range (DX-k*j)) (fun i=>gsMixedRow x (u+z*v) r s (i,j)*
      gsSpecializedValues DZ values z (i,j))=
    sumK (List.range (DZ-j)) (fun h=>sumK (List.range (DX-k*j))
      (fun i=>(jetMonomial h).eval z*gsMixedRow x (u+z*v) r s (i,j)*values (i,j,h)))
  have inner (i : Nat) : gsMixedRow x (u+z*v) r s (i,j)*gsSpecializedValues DZ values z (i,j)=
      sumK (List.range (DZ-j)) (fun h=>gsMixedRow x (u+z*v) r s (i,j)*
        ((jetMonomial h).eval z*values (i,j,h))) := by
    unfold gsSpecializedValues
    rw [dot_sum,sum_scale]
  have expanded := sum_congr (List.range (DX-k*j)) _ _ (fun i _=>inner i)
  rw [expanded,sum_swap]
  apply sum_congr
  intro h hh
  apply sum_congr
  intro i hi
  grind

/-- Zero formal source-line jet polynomials imply all mixed constraints at
EVERY specialization, not just at a finite set of challenge samples. -/
theorem gs_specialization_constraints (k DX height DZ : Nat) (values : (Nat×Nat×Nat)→K)
    (sources : List (K×K×K)) (m : Nat)
    (identities : ∀ source∈sources,∀ r s,r+s<m→
      (trivariateJetPolynomial (gsTrivariateMonomials k DX height DZ) values r s
        source.1 source.2.1 source.2.2).IsZero)
    (z : K) : ∀ source∈sources,
      BivariateOrder (bivariateTranslate (gsSpecialization k DX height DZ values z)
        source.1 (source.2.1+z*source.2.2)) m := by
  intro source member r s order
  rw [gs_specialization_mixed_jet]
  exact Poly.eval_of_isZero (identities source member r s order) z
/-- A nonzero sparse trivariate polynomial can specialize to zero at
most DZ-1 distinct field points. This bounds total annihilation only, not
all exceptional challenges in the MCA factorization argument. -/
theorem gs_zero_specialization_count (k DX height DZ : Nat) (values : (Nat×Nat×Nat)→K)
    (nonzero : ∃ index∈gsTrivariateMonomials k DX height DZ,values index≠0)
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun z=>∀ i j,((gsSpecialization k DX height DZ values z).getD j Poly.zero).coeff i=0)≤DZ-1 := by
  obtain ⟨⟨i,j,h⟩,member,value⟩:=nonzero
  have fits:=(gs_trivariate_member k DX height DZ i j h).mp member
  let coefficient:=Poly.mk ((List.range (DZ-j)).map (fun t=>values (i,j,t)))
  have nz : ¬coefficient.IsZero := by
    intro zero
    have entry:=zero h
    have bound : h<DZ-j := by omega
    have equal : coefficient.coeff h=values (i,j,h) := by
      simp [coefficient,Poly.coeff,List.getD,bound]
    rw [equal] at entry
    exact value entry
  have degree : coefficient.DegLt (DZ-j) := by
    simpa only [coefficient,List.length_map,List.length_range] using Poly.degLt_length coefficient
  have roots:=PolyRoots.cardRootsLe_of polyEval polyDeg quotFacts isZeroEval K
    coefficient (DZ-j) sample nz degree distinct
  have subset : count sample (fun z=>∀ a b,((gsSpecialization k DX height DZ values z).getD b Poly.zero).coeff a=0)≤
      count sample (fun z=>coefficient.eval z=0) := by
    apply count_mono
    intro z zero
    have selected:=zero i j
    change ((gsEncode k DX height (gsSpecializedValues DZ values z)).getD j Poly.zero).coeff i=0 at selected
    rw [gs_encode_coefficient,ite_eq_left ⟨fits.1,fits.2.1⟩] at selected
    have evaluation:=synthetic_jet_vector_matrix (DZ-j) (fun t=>values (i,j,t)) z 0
    change coefficient.eval z=gsSpecializedValues DZ values z (i,j) at evaluation
    exact evaluation.trans selected
  omega
end NearCompression
