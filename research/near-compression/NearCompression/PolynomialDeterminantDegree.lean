import NearCompression.BezoutSystemInvertibility

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Laplace expansion in the given row/column order. Square minors use equal
lengths; []/[] has determinant one. No divisions or pivot choices occur. -/
def scalarMinorDeterminant (matrix : Nat → Nat → K) : List Nat → List Nat → K
  | [], _ => 1
  | row::rows, columns =>
    ((List.range columns.length).map (fun j=>
      (if j%2=0 then (1:K) else -1)*matrix row (columns.getD j 0)*
        scalarMinorDeterminant matrix rows (columns.eraseIdx j))).foldr (·+·) 0

/-- The same division-free expansion over explicit polynomial coefficients. -/
def polynomialMinorDeterminant (matrix : Nat → Nat → Poly K) : List Nat → List Nat → Poly K
  | [], _ => Poly.C 1
  | row::rows, columns =>
    Poly.sum ((List.range columns.length).map (fun j=>
      Poly.smul (if j%2=0 then (1:K) else -1)
        (matrix row (columns.getD j 0)*polynomialMinorDeterminant matrix rows (columns.eraseIdx j))))

private theorem sum_degree (ps : List (Poly K)) (D : Nat) (degree : ∀ p∈ps,p.DegLt D) :
    (Poly.sum ps).DegLt D := by
  induction ps with
  | nil => intro i hi;rfl
  | cons p ps ih =>
    exact Poly.degLt_add (degree p (by simp)) (ih (fun q h=>degree q (by simp [h])))

private theorem sum_eval (ps : List (Poly K)) (z : K) :
    (Poly.sum ps).eval z=(ps.map (fun p=>p.eval z)).foldr (·+·) 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change (p+Poly.sum ps).eval z=_
    rw [Poly.eval_add,ih]
    rfl

/-- An N-row minor with entry degrees ≤D has determinant degree ≤N*D.
This is a polynomial bound, unaffected by elimination pivot denominators. -/
theorem polynomial_minor_determinant_degree (matrix : Nat → Nat → Poly K)
    (rows columns : List Nat) (D : Nat) (entries : ∀ i j,(matrix i j).DegLt (D+1)) :
    (polynomialMinorDeterminant matrix rows columns).DegLt (rows.length*D+1) := by
  induction rows generalizing columns with
  | nil => simpa [polynomialMinorDeterminant,Poly.C] using (Poly.degLt_length (Poly.C (1:K)))
  | cons row rows ih =>
    apply sum_degree
    intro p member
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp member
    have product:=Poly.degLt_mul (entries row (columns.getD j 0)) (ih (columns.eraseIdx j))
    have scaled:=Poly.degLt_smul (if j%2=0 then (1:K) else -1) product
    simpa only [List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using scaled

/-- Specializing the polynomial determinant equals the determinant of the
specialized entry matrix, including singular matrices and characteristic two. -/
theorem polynomial_minor_determinant_eval (matrix : Nat → Nat → Poly K)
    (rows columns : List Nat) (z : K) :
    (polynomialMinorDeterminant matrix rows columns).eval z=
      scalarMinorDeterminant (fun i j=>(matrix i j).eval z) rows columns := by
  induction rows generalizing columns with
  | nil => exact Poly.eval_C 1 z
  | cons row rows ih =>
    simp only [polynomialMinorDeterminant,scalarMinorDeterminant,sum_eval,List.map_map,Function.comp_def]
    congr 2
    funext j
    rw [Poly.eval_smul,Poly.eval_mul,ih]
    grind

/-- Once nonzeroness is established, at most N*D distinct specialization
points make the entry matrix determinant vanish. -/
theorem polynomial_minor_determinant_exception_count (matrix : Nat → Nat → Poly K)
    (rows columns : List Nat) (D : Nat) (entries : ∀ i j,(matrix i j).DegLt (D+1))
    (nonzero : ¬(polynomialMinorDeterminant matrix rows columns).IsZero)
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun z=>scalarMinorDeterminant (fun i j=>(matrix i j).eval z) rows columns=0)
      ≤rows.length*D := by
  have bound:=PolyRoots.cardRootsLe_of polyEval polyDeg quotFacts isZeroEval K
    (polynomialMinorDeterminant matrix rows columns) (rows.length*D+1) sample nonzero
    (polynomial_minor_determinant_degree matrix rows columns D entries) distinct
  have same : (fun z=>scalarMinorDeterminant (fun i j=>(matrix i j).eval z) rows columns=0)=
      (fun z=>(polynomialMinorDeterminant matrix rows columns).eval z=0) := by
    funext z
    rw [polynomial_minor_determinant_eval]
  rw [same]
  omega

/-- Coefficient matrix for U*p+V*q with n coefficients of U and m of V.
Rows and columns are indexed from zero; coefficients outside the support
must be supplied as zero by the source coefficient functions. -/
def bezoutPolynomialMatrix (p q : Nat → Poly K) (m n i j : Nat) : Poly K :=
  if j<n then (if j≤i then p (i-j) else Poly.zero)
  else (if j<m+n ∧ j-n≤i then q (i-(j-n)) else Poly.zero)

theorem bezout_polynomial_matrix_degree (p q : Nat → Poly K) (m n D : Nat)
    (pd : ∀ i,(p i).DegLt (D+1)) (qd : ∀ i,(q i).DegLt (D+1)) :
    ∀ i j,(bezoutPolynomialMatrix p q m n i j).DegLt (D+1) := by
  intro i j
  unfold bezoutPolynomialMatrix
  split
  · split
    · exact pd _
    · intro k hk;rfl
  · split
    · exact qd _
    · intro k hk;rfl

def derivativeBezoutPolynomialMatrix (p : Nat → Poly K) (d : Nat) : Nat → Nat → Poly K :=
  bezoutPolynomialMatrix p (fun i=>Poly.smul (OfNat.ofNat (i+1)) (p (i+1))) d (d-1)

/-- Formal derivative multiplication by natural coefficients does not increase
parameter degree, even when characteristic causes coefficients to vanish. -/
theorem derivative_bezout_matrix_degree (p : Nat → Poly K) (d D : Nat)
    (degree : ∀ i,(p i).DegLt (D+1)) :
    ∀ i j,(derivativeBezoutPolynomialMatrix p d i j).DegLt (D+1) :=
  bezout_polynomial_matrix_degree p _ d (d-1) D degree
    (fun i=>Poly.degLt_smul (OfNat.ofNat (i+1)) (degree (i+1)))

def derivativeBezoutPolynomialDeterminant (p : Nat → Poly K) (d : Nat) : Poly K :=
  polynomialMinorDeterminant (derivativeBezoutPolynomialMatrix p d)
    (List.range (d+(d-1))) (List.range (d+(d-1)))

/-- Source-parameter degree bound for the derivative Bezout determinant.
Nonzeroness and its inverse-certificate interpretation are separate proofs. -/
theorem derivative_bezout_determinant_degree (p : Nat → Poly K) (d D : Nat)
    (positive : 0<d) (degree : ∀ i,(p i).DegLt (D+1)) :
    (derivativeBezoutPolynomialDeterminant p d).DegLt ((2*d-1)*D+1) := by
  have bound:=polynomial_minor_determinant_degree (derivativeBezoutPolynomialMatrix p d)
    (List.range (d+(d-1))) (List.range (d+(d-1))) D (derivative_bezout_matrix_degree p d D degree)
  have same : d+(d-1)=2*d-1 := by omega
  simpa only [derivativeBezoutPolynomialDeterminant,List.length_range,same] using bound
end NearCompression
