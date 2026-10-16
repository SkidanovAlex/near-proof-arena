import NearCompression.HomogeneousKernel

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Explicit admissible monomials X^i Y^j with j<height and i+k*j<D.
A separate height cap permits k=0 without an infinite monomial family. -/
def gsMonomials (k D height : Nat) : List (Nat×Nat) :=
  (List.range height).flatMap (fun j=>(List.range (D-k*j)).map (fun i=>(i,j)))

omit [Field K] in
theorem gs_monomial_member (k D height i j : Nat) :
    (i,j)∈gsMonomials k D height ↔ j<height ∧ i+k*j<D := by
  simp only [gsMonomials,List.mem_flatMap,List.mem_map,List.mem_range,Prod.mk.injEq]
  constructor
  · rintro ⟨j',hj,i',hi,ei,ej⟩
    subst j';subst i';omega
  · intro h
    exact ⟨j,h.1,i,by omega,rfl,rfl⟩

omit [Field K] in
theorem gs_monomials_distinct (k D height : Nat) : (gsMonomials k D height).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  apply List.pairwise_flatMap.mpr
  constructor
  · intro j hj
    apply List.pairwise_map.mpr
    have nd : (List.range (D-k*j)).Pairwise (fun a b=>a≠b) :=
      List.nodup_iff_pairwise_ne.mp List.nodup_range
    exact nd.imp (fun {a b} ne (eq : (a,j)=(b,j))=>ne (congrArg Prod.fst eq))
  · apply List.Pairwise.imp_of_mem ?_ (List.nodup_iff_pairwise_ne.mp List.nodup_range)
    intro j l hj hl different x hx y hy equal
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hx
    obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hy
    exact different (congrArg Prod.snd equal)

omit [Field K] in
theorem gs_monomial_count (k D height : Nat) :
    (gsMonomials k D height).length=((List.range height).map (fun j=>D-k*j)).sum := by
  simp [gsMonomials,List.length_flatMap]

/-- Canonical dense rows from an indexed coefficient vector. -/
def gsEncode (k D height : Nat) (values : Nat×Nat→K) : List (Poly K) :=
  (List.range height).map (fun j=>Poly.mk ((List.range (D-k*j)).map (fun i=>values (i,j))))

theorem gs_encode_coefficient (k D height i j : Nat) (values : Nat×Nat→K) :
    ((gsEncode k D height values).getD j Poly.zero).coeff i=
      if j<height ∧ i+k*j<D then values (i,j) else 0 := by
  by_cases hj : j<height
  · by_cases hi : i<D-k*j
    · have weighted : i+k*j<D := by omega
      simp [gsEncode,Poly.coeff,List.getD,hj,hi,weighted]
    · have weighted : ¬i+k*j<D := by omega
      simp [gsEncode,Poly.coeff,List.getD,hj,hi,weighted]
  · simp [gsEncode,Poly.coeff,Poly.zero,List.getD,hj]

theorem gs_encode_weighted_degree (k D height : Nat) (values : Nat×Nat→K) :
    BivariateWeightedDegree (gsEncode k D height values) k D := by
  intro i j high
  rw [gs_encode_coefficient]
  have low : ¬i+k*j<D := by omega
  simp [low]

theorem gs_encode_nonzero (k D height : Nat) (values : Nat×Nat→K)
    (nonzero : ∃ index∈gsMonomials k D height,values index≠0) :
    ∃ i j,((gsEncode k D height values).getD j Poly.zero).coeff i≠0 := by
  obtain ⟨⟨i,j⟩,member,value⟩:=nonzero
  have fits:= (gs_monomial_member k D height i j).mp member
  refine ⟨i,j,?_⟩
  rw [gs_encode_coefficient,ite_eq_left fits]
  exact value

/-- Concrete polynomial rows, not merely a nonzero abstract vector, solve
any underdetermined collection of coefficient-linear equations. Identifying
those equations with translated mixed jets is a separate theorem. -/
theorem gs_linear_interpolant (k D height : Nat) (matrix : List ((Nat×Nat)→K))
    (short : matrix.length<((List.range height).map (fun j=>D-k*j)).sum) :
    ∃ rows : List (Poly K),BivariateWeightedDegree rows k D ∧
      (∃ i j,(rows.getD j Poly.zero).coeff i≠0) ∧
      ∀ row∈matrix,kernelDot (gsMonomials k D height) row
        (fun index=>(rows.getD index.2 Poly.zero).coeff index.1)=0 := by
  obtain ⟨values,nonzero,solves⟩:=homogeneous_nonzero_kernel matrix (gsMonomials k D height)
    (gs_monomials_distinct k D height) (by rw [gs_monomial_count];exact short)
  refine ⟨gsEncode k D height values,gs_encode_weighted_degree k D height values,
    gs_encode_nonzero k D height values nonzero,?_⟩
  intro row member
  have same : ∀ index∈gsMonomials k D height,
      ((gsEncode k D height values).getD index.2 Poly.zero).coeff index.1=values index := by
    intro index hi
    rw [gs_encode_coefficient]
    exact ite_eq_left ((gs_monomial_member k D height index.1 index.2).mp hi)
  have congruent : ∀ indices : List (Nat×Nat),
      (∀ index∈indices,((gsEncode k D height values).getD index.2 Poly.zero).coeff index.1=values index)→
      kernelDot indices row (fun index=>((gsEncode k D height values).getD index.2 Poly.zero).coeff index.1)=
        kernelDot indices row values := by
    intro indices
    induction indices with
    | nil => intro h;rfl
    | cons index rest ih =>
      intro h
      have head:=h index (by simp)
      have tail:=ih (fun i hi=>h i (by simp [hi]))
      simp only [kernelDot,head,tail]
  rw [congruent _ same]
  exact solves row member

/-- Mixed derivative orders in total-degree shells, each pair exactly once. -/
def gsJetOrders (m : Nat) : List (Nat×Nat) :=
  (List.range m).flatMap (fun t=>(List.range (t+1)).map (fun r=>(r,t-r)))

omit [Field K] in
theorem gs_jet_order_member (m r s : Nat) : (r,s)∈gsJetOrders m ↔ r+s<m := by
  simp only [gsJetOrders,List.mem_flatMap,List.mem_map,List.mem_range,Prod.mk.injEq]
  constructor
  · rintro ⟨t,ht,r',hr,er,es⟩
    subst r';omega
  · intro h
    exact ⟨r+s,h,r,by omega,rfl,by omega⟩

omit [Field K] in
theorem gs_jet_order_count (m : Nat) : 2*(gsJetOrders m).length=m*(m+1) := by
  have size : ∀ n,(gsJetOrders n).length=((List.range n).map (fun t=>t+1)).sum := by
    intro n;simp [gsJetOrders,List.length_flatMap]
  rw [size]
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ,List.map_append,List.sum_append]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    grind
omit [Field K] in
theorem gs_jet_orders_distinct (m : Nat) : (gsJetOrders m).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  apply List.pairwise_flatMap.mpr
  constructor
  · intro t ht
    apply List.pairwise_map.mpr
    have nd : (List.range (t+1)).Pairwise (fun a b=>a≠b) :=
      List.nodup_iff_pairwise_ne.mp List.nodup_range
    exact nd.imp (fun {a b} ne (eq : (a,t-a)=(b,t-b))=>ne (congrArg Prod.fst eq))
  · apply List.Pairwise.imp_of_mem ?_ (List.nodup_iff_pairwise_ne.mp List.nodup_range)
    intro t u ht hu different x hx y hy equal
    obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hx
    obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hy
    have er:=congrArg Prod.fst equal
    have es:=congrArg Prod.snd equal
    have br:=List.mem_range.mp hr
    have bs:=List.mem_range.mp hs
    simp only at er es
    exact different (by omega)

def gsConstraints (points : List (K×K)) (m : Nat) : List ((K×K)×(Nat×Nat)) :=
  points.flatMap (fun point=>(gsJetOrders m).map (fun order=>(point,order)))

omit [Field K] in
theorem gs_constraint_count (points : List (K×K)) (m : Nat) :
    2*(gsConstraints points m).length=points.length*m*(m+1) := by
  have orders:=gs_jet_order_count m
  induction points with
  | nil => simp [gsConstraints]
  | cons point rest ih =>
    simp only [gsConstraints,List.flatMap_cons,List.length_append,List.length_map,List.length_cons] at ih ⊢
    grind
end NearCompression
