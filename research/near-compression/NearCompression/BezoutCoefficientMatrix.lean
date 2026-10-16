import NearCompression.DeterminantRowSpan

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem dot_map (xs : List Nat) (f : Nat→Nat) (a b : Nat→K) :
    kernelDot (xs.map f) a b=kernelDot xs (fun i=>a (f i)) (fun i=>b (f i)) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp only [List.map_cons,kernelDot,ih]

private theorem dot_append (xs ys : List Nat) (a b : Nat→K) :
    kernelDot (xs++ys) a b=kernelDot xs a b+kernelDot ys a b := by
  induction xs with
  | nil => change _=0+_;grind
  | cons i xs ih => simp only [List.cons_append,kernelDot,ih];grind

private theorem dot_terms (xs : List Nat) (a b c d : Nat→K)
    (same : ∀ i∈xs,a i*b i=c i*d i) : kernelDot xs a b=kernelDot xs c d := by
  induction xs with
  | nil => rfl
  | cons i xs ih => rw [kernelDot,kernelDot,same i (by simp),ih (fun j hj=>same j (by simp [hj]))]

private theorem dot_zero (xs : List Nat) (a b : Nat→K) (zero : ∀ i∈xs,a i*b i=0) :
    kernelDot xs a b=0 := by
  induction xs with
  | nil => rfl
  | cons i xs ih => rw [kernelDot,zero i (by simp),ih (fun j hj=>zero j (by simp [hj]))];grind

private theorem cons_product (c : K) (cs : List K) (p : Poly K) (i : Nat) :
    ((Poly.mk (c::cs))*p).coeff i=c*p.coeff i+
      (match i with | 0=>0 | j+1=>((Poly.mk cs)*p).coeff j) := by
  change (Poly.smul c p+Poly.mk (0::Poly.mulL cs p.coeffs)).coeff i=_
  rw [Poly.coeff_add,Poly.coeff_smul]
  cases i <;> rfl

/-- The exact finite convolution underlying the coefficient matrix. -/
theorem polynomial_bounded_product_coefficient (A p : Poly K) (n i : Nat) (degree : A.DegLt n) :
    (A*p).coeff i=kernelDot (List.range n) A.coeff (fun j=>if j≤i then p.coeff (i-j) else 0) := by
  induction n generalizing A i with
  | zero =>
    have az : A.IsZero := fun j=>degree j (Nat.zero_le j)
    exact (polynomial_product_zero_iff A p).mpr (Or.inl az) i
  | succ n ih =>
    rw [List.range_succ_eq_map,kernelDot,dot_map]
    cases A with | mk cs => cases cs with
      | nil =>
        have zero : kernelDot (List.range n) (fun j=>(Poly.mk ([]:List K)).coeff (j+1))
            (fun j=>if j+1≤i then p.coeff (i-(j+1)) else 0)=0 := by
          apply dot_zero;intro j hj;change (0:K)*_=0;grind
        rw [zero]
        change (0:K)=0*(if 0≤i then p.coeff (i-0) else 0)+0
        grind
      | cons c cs =>
        rw [cons_product]
        have tail : (Poly.mk cs).DegLt n := fun j hj=>degree (j+1) (by omega)
        cases i with
        | zero =>
          have zero : kernelDot (List.range n) (fun j=>(Poly.mk (c::cs)).coeff (j+1))
              (fun j=>if j+1≤0 then p.coeff (0-(j+1)) else 0)=0 := by
            apply dot_zero;intro j hj;rw [ite_eq_right (by omega)];grind
          rw [zero]
          change c*p.coeff 0+0=c*p.coeff 0+0
          rfl
        | succ i =>
          simp only [Nat.succ_eq_add_one,Nat.zero_le,ite_true,Nat.sub_zero,Nat.add_le_add_iff_right,Nat.add_sub_add_right]
          change c*p.coeff (i+1)+((Poly.mk cs)*p).coeff i=
            c*p.coeff (i+1)+kernelDot (List.range n) (Poly.mk cs).coeff (fun j=>if j≤i then p.coeff (i-j) else 0)
          rw [ih (Poly.mk cs) i tail]

/-- Output coefficient i, unknown coefficient j, matching the polynomial-entry matrix. -/
def bezoutScalarCoefficientMatrix (p q : Poly K) (m n i j : Nat) : K :=
  if j<n then (if j≤i then p.coeff (i-j) else 0)
  else (if j<m+n ∧ j-n≤i then q.coeff (i-(j-n)) else 0)

def bezoutCoefficientVector (A B : Poly K) (n j : Nat) : K :=
  if j<n then A.coeff j else B.coeff (j-n)

/-- Explicit matrix multiplication is exactly polynomial multiplication and addition. -/
theorem bezout_coefficient_matrix_action (p q A B : Poly K) (m n i : Nat)
    (ad : A.DegLt n) (bd : B.DegLt m) :
    kernelDot (List.range (n+m)) (bezoutCoefficientVector A B n)
      (fun j=>bezoutScalarCoefficientMatrix p q m n i j)=(A*p+B*q).coeff i := by
  rw [Poly.coeff_add,polynomial_bounded_product_coefficient A p n i ad,
    polynomial_bounded_product_coefficient B q m i bd,List.range_add,dot_append,dot_map]
  have left : kernelDot (List.range n) (bezoutCoefficientVector A B n)
      (fun j=>bezoutScalarCoefficientMatrix p q m n i j)=
      kernelDot (List.range n) A.coeff (fun j=>if j≤i then p.coeff (i-j) else 0) := by
    apply dot_terms
    intro j member
    have inside:=List.mem_range.mp member
    simp [bezoutCoefficientVector,bezoutScalarCoefficientMatrix,inside]
  have right : kernelDot (List.range m) (fun j=>bezoutCoefficientVector A B n (n+j))
      (fun j=>bezoutScalarCoefficientMatrix p q m n i (n+j))=
      kernelDot (List.range m) B.coeff (fun j=>if j≤i then q.coeff (i-j) else 0) := by
    apply dot_terms
    intro j member
    have inside:=List.mem_range.mp member
    have first : ¬n+j<n := by omega
    have second : n+j<m+n := by omega
    simp [bezoutCoefficientVector,bezoutScalarCoefficientMatrix,first,second]
  rw [left,right]

/-- Transposed coefficient orientation: a solution vector combines these
rows into the target polynomial's coefficient vector. -/
def bezoutRowMatrix (p q : Poly K) (m n : Nat) : Nat→Nat→K :=
  fun j i=>bezoutScalarCoefficientMatrix p q m n i j

/-- Solve every monomial target to construct an actual row inverse. The
identity holds at every output index, not only inside the square block. -/
theorem bezout_coefficient_row_inverse (p q A B : Poly K) (m n : Nat)
    (pd : p.DegLt (m+1)) (qd : q.DegLt (n+1)) (ql : q.coeff n≠0)
    (certificate : PolynomialCoeffEq (A*p+B*q) (Poly.C 1)) :
    ∃ weights : Nat→Nat→K, ∀ r∈List.range (n+m),∀ i,
      kernelDot (List.range (n+m)) (weights r) (fun j=>bezoutRowMatrix p q m n j i)=
        if r=i then 1 else 0 := by
  classical
  have solutions : ∀ r : Nat, ∃ w : Nat→K, r<n+m → ∀ i,
      kernelDot (List.range (n+m)) w (fun j=>bezoutRowMatrix p q m n j i)=if r=i then 1 else 0 := by
    intro r
    by_cases inside : r<n+m
    · have targetDegree : (jetMonomial r : Poly K).DegLt (m+n) := by
        intro i hi
        rw [jet_monomial_coefficient,ite_eq_right (by omega)]
      obtain ⟨U,V,ud,vd,solved⟩:=polynomial_bounded_bezout_surjective p q A B (jetMonomial r) m n pd qd ql certificate targetDegree
      refine ⟨bezoutCoefficientVector U V n,?_⟩
      intro _ i
      change kernelDot (List.range (n+m)) (bezoutCoefficientVector U V n)
        (fun j=>bezoutScalarCoefficientMatrix p q m n i j)=_
      rw [bezout_coefficient_matrix_action p q U V m n i ud vd,solved i,jet_monomial_coefficient]
      simp only [eq_comm]
    · exact ⟨fun _=>0,fun bad=>False.elim (inside bad)⟩
  refine ⟨fun r=>Classical.choose (solutions r),?_⟩
  intro r member i
  exact Classical.choose_spec (solutions r) (List.mem_range.mp member) i

/-- Coprimality now proves, rather than assumes, nonzeroness of the explicit
transposed Bezout coefficient determinant. -/
theorem bezout_coefficient_determinant_nonzero (p q A B : Poly K) (m n : Nat)
    (pd : p.DegLt (m+1)) (qd : q.DegLt (n+1)) (ql : q.coeff n≠0)
    (certificate : PolynomialCoeffEq (A*p+B*q) (Poly.C 1)) :
    scalarMinorDeterminant (bezoutRowMatrix p q m n) (List.range (n+m)) (List.range (n+m))≠0 := by
  obtain ⟨weights,inverse⟩:=bezout_coefficient_row_inverse p q A B m n pd qd ql certificate
  exact scalar_minor_nonzero_of_row_inverse _ weights _ List.nodup_range inverse

/-- Bounded polynomial solutions have the common determinant denominator,
with no nonsingularity premise beyond the proved unit certificate. -/
theorem bezout_coefficient_cramer (p q A B U V target : Poly K) (m n r : Nat)
    (pd : p.DegLt (m+1)) (qd : q.DegLt (n+1)) (ql : q.coeff n≠0)
    (certificate : PolynomialCoeffEq (A*p+B*q) (Poly.C 1))
    (ud : U.DegLt n) (vd : V.DegLt m) (solved : PolynomialCoeffEq (U*p+V*q) target)
    (inside : r<n+m) :
    bezoutCoefficientVector U V n r=
      scalarMinorDeterminant (replaceDeterminantRow (bezoutRowMatrix p q m n) r target.coeff)
        (List.range (n+m)) (List.range (n+m))*
      (scalarMinorDeterminant (bezoutRowMatrix p q m n) (List.range (n+m)) (List.range (n+m)))⁻¹ := by
  apply scalar_minor_cramer_denominator _ _ _ List.nodup_range r (List.mem_range.mpr inside)
    (bezoutCoefficientVector U V n) target.coeff
  · intro i
    exact (bezout_coefficient_matrix_action p q U V m n i ud vd).trans (solved i)
  · exact bezout_coefficient_determinant_nonzero p q A B m n pd qd ql certificate
end NearCompression
