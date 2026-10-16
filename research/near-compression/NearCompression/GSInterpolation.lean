import NearCompression.MixedJetTranslation

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Actual coefficient-linear mixed-jet matrix, defined without any assumed
binomial/Hasse formula or matrix-correctness premise. -/
def gsMixedRow (a b : K) (r s : Nat) (index : Nat×Nat) : K :=
  syntheticJet (jetMonomial index.1) a r*syntheticJet (jetMonomial index.2) b s

private theorem dot_append {I : Type} (xs ys : List I) (row values : I→K) :
    kernelDot (xs++ys) row values=kernelDot xs row values+kernelDot ys row values := by
  induction xs with
  | nil => simp only [List.nil_append,kernelDot];grind
  | cons x xs ih => simp only [List.cons_append,kernelDot,ih];grind

private theorem flatten_dot (outer : List Nat) (width : Nat→Nat) (wx wy : Nat→K)
    (values : Nat×Nat→K) :
    kernelDot (outer.flatMap (fun j=>(List.range (width j)).map (fun i=>(i,j))))
      (fun index=>wx index.1*wy index.2) values=
    kernelDot outer wy (fun j=>kernelDot (List.range (width j)) wx (fun i=>values (i,j))) := by
  induction outer with
  | nil => rfl
  | cons j rest ih =>
    rw [List.flatMap_cons,dot_append,ih]
    have head : ∀ inner : List Nat,
        kernelDot (inner.map (fun i=>(i,j))) (fun index=>wx index.1*wy index.2) values=
        wy j*kernelDot inner wx (fun i=>values (i,j)) := by
      intro inner
      induction inner with
      | nil => simp only [List.map_nil,kernelDot];grind
      | cons i rest ih => simp only [List.map_cons,kernelDot,ih];grind
    rw [head];rfl

/-- The concrete matrix equals the actual translated mixed coefficient of
canonically encoded polynomial rows, in every field characteristic. -/
theorem gs_mixed_matrix_correct (k D height : Nat) (values : Nat×Nat→K)
    (a b : K) (r s : Nat) :
    ((bivariateTranslate (gsEncode k D height values) a b).getD s Poly.zero).coeff r=
      kernelDot (gsMonomials k D height) (gsMixedRow a b r s) values := by
  rw [bivariate_translate_mixed_jet]
  unfold syntheticMixedJet gsEncode
  simp only [List.map_map,Function.comp_def]
  rw [synthetic_jet_vector_matrix]
  have inner : (fun j=>syntheticJet (Poly.mk ((List.range (D-k*j)).map (fun i=>values (i,j)))) a r)=
      (fun j=>kernelDot (List.range (D-k*j)) (fun i=>syntheticJet (jetMonomial i) a r) (fun i=>values (i,j))) := by
    funext j
    exact synthetic_jet_vector_matrix (D-k*j) (fun i=>values (i,j)) a r
  rw [inner]
  exact (flatten_dot (List.range height) (fun j=>D-k*j)
    (fun i=>syntheticJet (jetMonomial i) a r) (fun j=>syntheticJet (jetMonomial j) b s) values).symm

def gsInterpolationMatrix (points : List (K×K)) (m : Nat) : List ((Nat×Nat)→K) :=
  (gsConstraints points m).map (fun c=>gsMixedRow c.1.1 c.1.2 c.2.1 c.2.2)

/-- General nonzero bivariate interpolation existence. The dimension inequality
is explicit and exact. Weighted degree, nonzeroness and ALL total-order mixed
jets are conclusions. No candidate-list or MCA theorem is assumed. -/
theorem gs_interpolant_exists (points : List (K×K)) (m k D height : Nat)
    (dimension : (gsConstraints points m).length<((List.range height).map (fun j=>D-k*j)).sum) :
    ∃ rows : List (Poly K),BivariateWeightedDegree rows k D ∧
      (∃ i j,(rows.getD j Poly.zero).coeff i≠0) ∧
      ∀ point∈points,BivariateOrder (bivariateTranslate rows point.1 point.2) m := by
  obtain ⟨values,nonzero,solves⟩:=homogeneous_nonzero_kernel (gsInterpolationMatrix points m)
    (gsMonomials k D height) (gs_monomials_distinct k D height)
    (by simpa only [gsInterpolationMatrix,List.length_map,gs_monomial_count] using dimension)
  refine ⟨gsEncode k D height values,gs_encode_weighted_degree k D height values,
    gs_encode_nonzero k D height values nonzero,?_⟩
  intro point member r s order
  rw [gs_mixed_matrix_correct]
  apply solves
  apply List.mem_map.mpr
  refine ⟨(point,(r,s)),?_,rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨point,member,?_⟩
  exact List.mem_map.mpr ⟨(r,s),(gs_jet_order_member m r s).mpr order,rfl⟩

/-- Denominator-free sufficient dimension check using the proved exact
constraint count; suitable for integer parameter ledgers. -/
theorem gs_interpolant_exists_counted (points : List (K×K)) (m k D height : Nat)
    (dimension : points.length*m*(m+1)<2*((List.range height).map (fun j=>D-k*j)).sum) :
    ∃ rows : List (Poly K),BivariateWeightedDegree rows k D ∧
      (∃ i j,(rows.getD j Poly.zero).coeff i≠0) ∧
      ∀ point∈points,BivariateOrder (bivariateTranslate rows point.1 point.2) m := by
  apply gs_interpolant_exists points m k D height
  have count:=gs_constraint_count points m
  omega
end NearCompression
