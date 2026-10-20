import NearCompression.JetCenterPolynomial

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- X^i Y^j Z^h with i+k*j<DX, j<height and j+h<DZ. -/
def gsTrivariateMonomials (k DX height DZ : Nat) : List (Nat×Nat×Nat) :=
  (List.range height).flatMap (fun j=>(gsMonomials 0 (DX-k*j) (DZ-j)).map
    (fun pair=>(pair.1,j,pair.2)))

omit [Field K] in
theorem gs_trivariate_member (k DX height DZ i j h : Nat) :
    (i,j,h)∈gsTrivariateMonomials k DX height DZ ↔
      j<height ∧ i+k*j<DX ∧ j+h<DZ := by
  simp only [gsTrivariateMonomials,List.mem_flatMap,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨j',hj,pair,hpair,equal⟩
    have ei:=congrArg Prod.fst equal
    have ej:=congrArg (fun p : Nat×Nat×Nat=>p.2.1) equal
    have eh:=congrArg (fun p : Nat×Nat×Nat=>p.2.2) equal
    simp only at ei ej eh
    subst j'
    have fits:=(gs_monomial_member 0 (DX-k*j) (DZ-j) pair.1 pair.2).mp hpair
    simp only [Nat.zero_mul,Nat.add_zero] at fits
    omega
  · intro fits
    refine ⟨j,fits.1,(i,h),?_,rfl⟩
    apply (gs_monomial_member 0 (DX-k*j) (DZ-j) i h).mpr
    simp only [Nat.zero_mul,Nat.add_zero]
    constructor <;> omega

omit [Field K] in
theorem gs_trivariate_distinct (k DX height DZ : Nat) :
    (gsTrivariateMonomials k DX height DZ).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  apply List.pairwise_flatMap.mpr
  constructor
  · intro j hj
    apply List.pairwise_map.mpr
    have nd:=List.nodup_iff_pairwise_ne.mp (gs_monomials_distinct 0 (DX-k*j) (DZ-j))
    apply List.Pairwise.imp ?_ nd
    intro a b different equal
    apply different
    have first:=congrArg Prod.fst equal
    have last:=congrArg (fun p : Nat×Nat×Nat=>p.2.2) equal
    exact Prod.ext first last
  · apply List.Pairwise.imp_of_mem ?_ (List.nodup_iff_pairwise_ne.mp List.nodup_range)
    intro j l hj hl different a ha b hb equal
    obtain ⟨u,hu,rfl⟩:=List.mem_map.mp ha
    obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hb
    exact different (congrArg (fun p : Nat×Nat×Nat=>p.2.1) equal)

private theorem rectangle_count (width height : Nat) :
    (gsMonomials 0 width height).length=width*height := by
  rw [gs_monomial_count]
  simp only [Nat.zero_mul,Nat.sub_zero]
  induction height with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.map_append,List.sum_append]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    grind

omit [Field K] in
theorem gs_trivariate_count (k DX height DZ : Nat) :
    (gsTrivariateMonomials k DX height DZ).length=
      ((List.range height).map (fun j=>(DX-k*j)*(DZ-j))).sum := by
  simp [gsTrivariateMonomials,List.length_flatMap,rectangle_count]

/-- Each mixed order (r,s), r+s<m, contributes DZ-s Z coefficients. -/
def gsTrivariateConstraints (sources : List (K×K×K)) (m DZ : Nat) :
    List ((K×K×K)×(Nat×Nat×Nat)) :=
  sources.flatMap (fun source=>(gsTrivariateMonomials 1 m m DZ).map (fun order=>(source,order)))

omit [Field K] in
theorem gs_trivariate_constraint_count (sources : List (K×K×K)) (m DZ : Nat) :
    (gsTrivariateConstraints sources m DZ).length=
      sources.length*((List.range m).map (fun s=>(m-s)*(DZ-s))).sum := by
  induction sources with
  | nil => simp [gsTrivariateConstraints]
  | cons source rest ih =>
    simp only [gsTrivariateConstraints,List.flatMap_cons,List.length_append,List.length_map,List.length_cons] at ih ⊢
    rw [gs_trivariate_count,ih]
    simp only [Nat.one_mul]
    grind

def gsTrivariateMatrix (sources : List (K×K×K)) (m DZ : Nat) : List ((Nat×Nat×Nat)→K) :=
  (gsTrivariateConstraints sources m DZ).map (fun c index=>
    (trivariateJetTerm index.1 index.2.1 index.2.2 c.2.1 c.2.2.1
      c.1.1 c.1.2.1 c.1.2.2).coeff c.2.2.2)

/-- Nonzero controlled-degree trivariate coefficient vector. Every mixed jet
along every source line is the zero FORMAL polynomial in Z. The coefficient
vector is interpreted on the explicit distinct monomial list only. -/
theorem gs_trivariate_interpolant_exists (sources : List (K×K×K)) (m k DX height DZ : Nat)
    (dimension : sources.length*((List.range m).map (fun s=>(m-s)*(DZ-s))).sum<
      ((List.range height).map (fun j=>(DX-k*j)*(DZ-j))).sum) :
    ∃ values : (Nat×Nat×Nat)→K,
      (∃ index∈gsTrivariateMonomials k DX height DZ,values index≠0) ∧
      ∀ source∈sources,∀ r s,r+s<m→
        (trivariateJetPolynomial (gsTrivariateMonomials k DX height DZ) values r s
          source.1 source.2.1 source.2.2).IsZero := by
  obtain ⟨values,nonzero,solves⟩:=homogeneous_nonzero_kernel (gsTrivariateMatrix sources m DZ)
    (gsTrivariateMonomials k DX height DZ) (gs_trivariate_distinct k DX height DZ)
    (by simpa only [gsTrivariateMatrix,List.length_map,gs_trivariate_constraint_count,gs_trivariate_count] using dimension)
  refine ⟨values,nonzero,?_⟩
  intro source member r s order
  apply trivariate_jet_constraints_zero _ values r s DZ source.1 source.2.1 source.2.2
  · intro index hi
    exact ((gs_trivariate_member k DX height DZ index.1 index.2.1 index.2.2).mp hi).2.2
  · intro t ht
    apply solves
    apply List.mem_map.mpr
    refine ⟨(source,(r,s,t)),?_,rfl⟩
    apply List.mem_flatMap.mpr
    refine ⟨source,member,?_⟩
    apply List.mem_map.mpr
    refine ⟨(r,s,t),?_,rfl⟩
    apply (gs_trivariate_member 1 m m DZ r s t).mpr
    simp only [Nat.one_mul]
    constructor
    · omega
    · constructor <;> omega
end NearCompression
