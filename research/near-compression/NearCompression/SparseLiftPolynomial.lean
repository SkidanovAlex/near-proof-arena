import NearCompression.SparseLiftMLE
import NearCompression.HeterogeneousSourcePair

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def coefficientPolynomial (n : Nat) (coefficients : Nat → K) : Poly K :=
  Poly.mk ((List.range (2^n)).map coefficients)

def sparseLiftPolynomial (k n : Nat) (coefficients : List K) : Poly K :=
  coefficientPolynomial (k+n) (sparseLowLift k (fun i => coefficients.getD i 0))

private theorem tensor_congr (n : Nat) (a b point : Nat → K)
    (same : ∀ i,i<2^n → a i=b i) : laneTensor n a point=laneTensor n b point := by
  induction n generalizing a b point with
  | zero => exact same 0 (by decide)
  | succ n ih =>
    rw [laneTensor,laneTensor]
    rw [ih (fun i => a (2*i)) (fun i => b (2*i)) _ (by intro i hi; apply same; rw [Nat.pow_succ]; omega),
      ih (fun i => a (2*i+1)) (fun i => b (2*i+1)) _ (by intro i hi; apply same; rw [Nat.pow_succ]; omega)]

private theorem tensor_zero (n : Nat) (point : Nat → K) : laneTensor n (fun _ => 0) point=0 := by
  induction n generalizing point with
  | zero => rfl
  | succ n ih => simp only [laneTensor,ih]; grind

private theorem tensor_add (n : Nat) (a b point : Nat → K) :
    laneTensor n (fun i => a i+b i) point=laneTensor n a point+laneTensor n b point := by
  induction n generalizing a b point with
  | zero => rfl
  | succ n ih => simp only [laneTensor,ih]; grind

private theorem tensor_scale (n : Nat) (a : K) (f point : Nat → K) :
    laneTensor n (fun i => a*f i) point=a*laneTensor n f point := by
  induction n generalizing f point with
  | zero => rfl
  | succ n ih => simp only [laneTensor,ih]; grind

/-- Evaluation of the exact fixed-length coefficient array reads the same
monomial tensor, without Boolean interpolation factors. -/
theorem coefficient_polynomial_eval (n : Nat) (coefficients : Nat → K) (x : K) :
    (coefficientPolynomial n coefficients).eval x=laneTensor n coefficients (fun i => x^(2^i)) := by
  have tensor := generic_monomial_tensor_power_curve n ((List.range (2^n)).map coefficients)
    (by simp) x
  rw [lane_tensor_monomial] at tensor
  unfold coefficientPolynomial
  rw [←tensor]
  apply tensor_congr
  intro i hi
  simp [List.getD,hi]

/-- Sparse low-coordinate lifting deletes those coordinates from monomial
tensor evaluation. Unlike sparse_lift_mle there is no (1-u) factor. -/
theorem sparse_lift_monomial_tensor (k n : Nat) (coefficients point : Nat → K) :
    laneTensor (k+n) (sparseLowLift k coefficients) point=
      laneTensor n coefficients (fun i => point (k+i)) := by
  induction k generalizing point with
  | zero => simp only [Nat.zero_add,sparseLowLift]
  | succ k ih =>
    rw [show k+1+n=(k+n)+1 by omega]
    have even (i : Nat) : (2*i)/2=i := by omega
    simp only [laneTensor,sparseLowLift,Nat.mul_mod_right,even,
      Nat.add_mod,Nat.zero_add,Nat.mod_eq_of_lt (show 1<2 by decide),
      Nat.reduceEqDiff,ite_true,ite_false]
    rw [tensor_zero,ih]
    have index : (fun i => point (k+i+1))=(fun i => point (k+1+i)) := by
      funext i
      congr 1
      omega
    rw [index]
    grind

/-- The exact stride-2^k coefficient array evaluates to f(X^(2^k)). This
includes a short zero-padded source array and all field points, including zero. -/
theorem sparse_lift_polynomial_eval (k n : Nat) (coefficients : List K)
    (shape : coefficients.length≤2^n) (x : K) :
    (sparseLiftPolynomial k n coefficients).eval x=(Poly.mk coefficients).eval (x^(2^k)) := by
  rw [sparseLiftPolynomial,coefficient_polynomial_eval,sparse_lift_monomial_tensor]
  have curve : (fun i => x^(2^(k+i)))=(fun i => (x^(2^k))^(2^i)) := by
    funext i
    rw [←pow_mul_eq,Nat.pow_add]
  rw [curve,←lane_tensor_monomial]
  have point : (fun i => (x^(2^k))^(2^i))=genericMonomialCurve (x^(2^k)) := by
    funext i
    exact (generic_monomial_curve_power _ _).symm
  rw [point]
  exact generic_monomial_tensor_curve n coefficients shape _

/-- Exact algebraic storage of branch_words: weighted lanes occupy stride
2^k positions in a common-degree scalar coefficient array. -/
def branchWordsPolynomial (k n : Nat) (beta : List K) (lanes : List (List K)) : Poly K :=
  coefficientPolynomial (k+n) (fun i => weightedLaneValues beta
    (lanes.map (fun coefficients => sparseLowLift k (fun j => coefficients.getD j 0) i)))

private theorem tensor_weighted (n : Nat) (beta : List K) (lanes : List (Nat → K)) (point : Nat → K) :
    laneTensor n (fun i => weightedLaneValues beta (lanes.map (fun f => f i))) point=
      weightedLaneValues beta (lanes.map (fun f => laneTensor n f point)) := by
  induction beta generalizing lanes with
  | nil => exact tensor_zero n point
  | cons a rest ih =>
    cases lanes with
    | nil => exact tensor_zero n point
    | cons f fs =>
      simp only [List.map_cons,weightedLaneValues]
      rw [tensor_add,tensor_scale,ih]

/-- The complete weighted branch coefficient accumulator evaluates to the
same lifted source oracle used in the heterogeneous pair theorem. -/
theorem branch_words_polynomial_eval (k n : Nat) (beta : List K) (lanes : List (List K))
    (shape : ∀ coefficients∈lanes,coefficients.length≤2^n) (x : K) :
    (branchWordsPolynomial k n beta lanes).eval x=
      weightedVirtualOracle beta (liftedSourceFunctions k (lanes.map (fun cs => (Poly.mk cs).eval))) x := by
  rw [branchWordsPolynomial,coefficient_polynomial_eval]
  have nested : (fun i => weightedLaneValues beta
      (lanes.map (fun coefficients => sparseLowLift k (fun j => coefficients.getD j 0) i)))=
      (fun i => weightedLaneValues beta
        ((lanes.map (fun coefficients => sparseLowLift k (fun j => coefficients.getD j 0))).map (fun f => f i))) := by
    simp only [List.map_map,Function.comp_def]
  rw [nested,tensor_weighted]
  simp only [weightedVirtualOracle,liftedSourceFunctions,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro coefficients member
  rw [←coefficient_polynomial_eval]
  exact sparse_lift_polynomial_eval k n coefficients (shape coefficients member) x

theorem branch_words_degree (k n : Nat) (beta : List K) (lanes : List (List K)) :
    (branchWordsPolynomial k n beta lanes).DegLt (2^(k+n)) := by
  simpa [branchWordsPolynomial,coefficientPolynomial] using
    Poly.degLt_length (branchWordsPolynomial k n beta lanes)

/-- Exact occupied coefficient position in the common-degree array. -/
theorem branch_words_stride_coefficient (k n i j : Nat) (hi : i<2^n) (hj : j<2^k)
    (beta : List K) (lanes : List (List K)) :
    (branchWordsPolynomial k n beta lanes).coeff (2^k*i+j)=
      weightedLaneValues beta (lanes.map (fun cs => if j=0 then cs.getD i 0 else 0)) := by
  have bound : 2^k*i+j<2^(k+n) := by
    rw [Nat.pow_add]
    have h := Nat.mul_le_mul_left (2^k) (Nat.succ_le_iff.mpr hi)
    simp only [Nat.mul_succ] at h
    omega
  simp only [branchWordsPolynomial,coefficientPolynomial,Poly.coeff]
  have read : (((List.range (2^(k+n))).map (fun index => weightedLaneValues beta
      (lanes.map (fun cs => sparseLowLift k (fun t => cs.getD t 0) index)))).getD (2^k*i+j) 0)=
      weightedLaneValues beta (lanes.map (fun cs => sparseLowLift k (fun t => cs.getD t 0) (2^k*i+j))) := by
    simp [List.getD,bound]
  rw [read]
  congr 1
  apply List.map_congr_left
  intro cs hc
  exact sparse_lift_block k (fun t => cs.getD t 0) i j hj

/-- Composition with the actual source-pair projection: authenticated source
RS leaves yield evaluations of the exact branch_words coefficient accumulator.
Authentication remains an explicit fixed-oracle binding premise. -/
theorem branch_words_authenticated_pair (omega : K) (k n D s : Nat)
    (degree : D=2^k*2^n) (halfOrder : omega^(2*D)= -1)
    (beta : List K) (lanes : List (List K)) (shape : ∀ cs∈lanes,cs.length≤2^n)
    (leaf : List (K×K))
    (authenticated : leaf=sourceWideLeaf (lanes.map (fun cs => (Poly.mk cs).eval))
      ((omega^(2^k))^(s%(2*2^n)))) :
    projectedBetaPair k (2^n) s beta leaf=
      ((branchWordsPolynomial k n beta lanes).eval (omega^(s%(2*D))),
       (branchWordsPolynomial k n beta lanes).eval (-(omega^(s%(2*D))))) := by
  rw [branch_words_polynomial_eval k n beta lanes shape,branch_words_polynomial_eval k n beta lanes shape]
  exact heterogeneous_beta_pair_exact omega k (2^n) D s (Nat.two_pow_pos n) degree
    (heterogeneous_half_order omega k (2^n) D degree halfOrder) beta _ leaf authenticated

end NearCompression
