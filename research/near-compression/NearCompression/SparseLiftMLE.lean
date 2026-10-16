import NearCompression.GenericRowMLE

/-! Heterogeneous lanes on a common coefficient cube. Sparse coefficient
lifting inserts zero low-bit positions; weights repeat across those positions.
This is the low-round scale schedule in the weighted joint prover, not a
commitment or transcript soundness theorem. -/
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

def sparseLowLift : Nat → (Nat → K) → Nat → K
  | 0,values => values
  | k+1,values => fun i => if i%2=0 then sparseLowLift k values (i/2) else 0

def repeatLowWeights : Nat → (Nat → K) → Nat → K
  | 0,values => values
  | k+1,values => fun i => repeatLowWeights k values (i/2)

def lowZeroFactor : Nat → (Nat → K) → K
  | 0,_ => 1
  | k+1,point => (1-point 0)*lowZeroFactor k (fun i => point (i+1))

theorem sparse_lift_mle (k n : Nat) (values point : Nat → K) :
    genericRowMLE (k+n) (sparseLowLift k values) point=
      lowZeroFactor k point*genericRowMLE n values (fun i => point (k+i)) := by
  induction k generalizing point with
  | zero => simp only [Nat.zero_add,sparseLowLift,lowZeroFactor]; grind
  | succ k ih =>
    rw [show k+1+n=(k+n)+1 by omega]
    have even (i : Nat) : (2*i)/2=i := by omega
    simp only [genericRowMLE,sparseLowLift,Nat.mul_mod_right,even,
      Nat.add_mod,Nat.zero_add,Nat.mod_eq_of_lt (show 1<2 by decide),
      Nat.reduceEqDiff,ite_true,ite_false]
    rw [generic_row_mle_zero,ih]
    simp only [lowZeroFactor]
    have index : (fun i => point (k+i+1))=(fun i => point (k+1+i)) := by
      funext i;congr 1;omega
    rw [index]
    grind

theorem repeated_low_weight_mle (k n : Nat) (values point : Nat → K) :
    genericRowMLE (k+n) (repeatLowWeights k values) point=
      genericRowMLE n values (fun i => point (k+i)) := by
  induction k generalizing point with
  | zero => simp only [Nat.zero_add,repeatLowWeights]
  | succ k ih =>
    rw [show k+1+n=(k+n)+1 by omega]
    have even (i : Nat) : (2*i)/2=i := by omega
    have odd (i : Nat) : (2*i+1)/2=i := by omega
    simp only [genericRowMLE,repeatLowWeights,even,odd,ih]
    have index : (fun i => point (k+i+1))=(fun i => point (k+1+i)) := by
      funext i;congr 1;omega
    rw [index]
    grind

/-- Exact sparse storage: coefficient i occupies position 2^k*i and every
other position in its stride block is zero. -/
theorem sparse_lift_block (k : Nat) (values : Nat → K) (i j : Nat) (bound : j<2^k) :
    sparseLowLift k values (2^k*i+j)=if j=0 then values i else 0 := by
  induction k generalizing j with
  | zero =>
    have h : j=0 := by simpa using bound
    simp [h,sparseLowLift]
  | succ k ih =>
    have power : 2^(k+1)=2*2^k := by simp [Nat.pow_succ,Nat.mul_comm]
    rw [power] at bound ⊢
    have div : (2*2^k*i+j)/2=2^k*i+j/2 := by rw [Nat.mul_assoc]; omega
    have rem : (2*2^k*i+j)%2=j%2 := by rw [Nat.mul_assoc]; omega
    simp only [sparseLowLift,div,rem]
    split
    · rename_i even
      rw [ih (j/2) (by omega)]
      have zero : j/2=0 ↔ j=0 := by omega
      simp only [zero]
    · rename_i odd
      have nonzero : j≠0 := by omega
      simp only [nonzero,ite_false]

/-- Repeated weights assign the original weight to every position in the
same stride block, including the positions with zero lifted coefficients. -/
theorem repeated_weight_block (k : Nat) (values : Nat → K) (i j : Nat) (bound : j<2^k) :
    repeatLowWeights k values (2^k*i+j)=values i := by
  induction k generalizing j with
  | zero =>
    have h : j=0 := by simpa using bound
    simp [h,repeatLowWeights]
  | succ k ih =>
    have power : 2^(k+1)=2*2^k := by simp [Nat.pow_succ,Nat.mul_comm]
    rw [power] at bound ⊢
    have div : (2*2^k*i+j)/2=2^k*i+j/2 := by rw [Nat.mul_assoc]; omega
    simp only [repeatLowWeights,div]
    exact ih (j/2) (by omega)

end NearCompression
