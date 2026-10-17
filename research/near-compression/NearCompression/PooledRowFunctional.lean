import NearCompression.DualMobiusWeights
import NearCompression.CallLinearBatch
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

private theorem pooled_sum_append (a b : List K) : (a++b).sum=a.sum+b.sum := by
  induction a with
  | nil => simp; grind
  | cons x xs ih => simp only [List.cons_append,List.sum_cons,ih]; grind

private theorem pooled_sum_add (indices : List Nat) (f g : Nat → K) :
    (indices.map (fun i => f i+g i)).sum=(indices.map f).sum+(indices.map g).sum := by
  induction indices with
  | nil => simp; grind
  | cons i is ih => simp only [List.map_cons,List.sum_cons,ih]; grind

private theorem pooled_sum_scale (indices : List Nat) (a : K) (f : Nat → K) :
    (indices.map (fun i => a*f i)).sum=a*(indices.map f).sum := by
  induction indices with
  | nil => simp; grind
  | cons i is ih => simp only [List.map_cons,List.sum_cons,ih]; grind

private theorem pooled_prefix_sum (n extra : Nat) (f : Nat → K) :
    ((List.range (n+extra)).map (fun i => if i<n then f i else 0)).sum =
      ((List.range n).map f).sum := by
  induction extra with
  | zero =>
    simp only [Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro i hi
    simp [List.mem_range.mp hi]
  | succ extra ih =>
    rw [Nat.add_succ,List.range_succ,List.map_append,pooled_sum_append,ih]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    rw [ite_eq_right (by omega)]
    grind

/-- A logical table uses only the first 2^n physical rows. Other bank rows may
be arbitrary: neither zero padding nor repetition is an assumption. -/
def pooledRowMask (n : Nat) (weights : Nat → K) (i : Nat) : K :=
  if i<2^n then weights i else 0

theorem pooled_row_mask_dot (n m : Nat) (bounded : 2^n ≤ 2^m)
    (weights values : Nat → K) :
    cubeSum m (fun i => upperZeta m (pooledRowMask n weights) i * mobiusCoefficients m values i) =
      cubeSum n (fun i => weights i * values i) := by
  rw [dual_mobius_dot]
  have same : (fun i => pooledRowMask n weights i * values i) =
      (fun i => if i<2^n then weights i * values i else 0) := by
    funext i
    unfold pooledRowMask
    split <;> grind
  rw [same]
  unfold cubeSum
  have total : 2^m = 2^n+(2^m-2^n) := by omega
  rw [total]
  exact pooled_prefix_sum (2^n) (2^m-2^n) _

theorem pooled_current_row_functional (n m : Nat) (bounded : 2^n ≤ 2^m)
    (point values : Nat → K) :
    cubeSum m (fun i => upperZeta m (pooledRowMask n (rowEqualityWeight n point)) i *
      mobiusCoefficients m values i) = genericRowMLE n values point := by
  rw [pooled_row_mask_dot n m bounded]
  exact row_equality_dot n point values

/-- Next-row rotation wraps inside the logical table; extending the row point
and rotating the entire physical bank would be a different functional. -/
theorem pooled_next_row_functional (n m : Nat) (bounded : 2^n ≤ 2^m)
    (point values : Nat → K) :
    cubeSum m (fun i => upperZeta m (pooledRowMask n (cyclicRowWeight n point)) i *
      mobiusCoefficients m values i) = genericRowNextMLE n values point := by
  rw [pooled_row_mask_dot n m bounded]
  have same := next_dual_mobius n point values
  rw [dual_mobius_dot] at same
  exact same

theorem pooled_current_next_row_functional (n m : Nat) (bounded : 2^n ≤ 2^m)
    (point values : Nat → K) (a b : K) :
    cubeSum m (fun i =>
      (a * upperZeta m (pooledRowMask n (rowEqualityWeight n point)) i +
       b * upperZeta m (pooledRowMask n (cyclicRowWeight n point)) i) * mobiusCoefficients m values i) =
      a * genericRowMLE n values point + b * genericRowNextMLE n values point := by
  have distribute : (fun i =>
      (a * upperZeta m (pooledRowMask n (rowEqualityWeight n point)) i +
       b * upperZeta m (pooledRowMask n (cyclicRowWeight n point)) i) * mobiusCoefficients m values i) =
      (fun i => a * (upperZeta m (pooledRowMask n (rowEqualityWeight n point)) i * mobiusCoefficients m values i) +
        b * (upperZeta m (pooledRowMask n (cyclicRowWeight n point)) i * mobiusCoefficients m values i)) := by
    funext i
    grind
  rw [distribute]
  unfold cubeSum
  rw [pooled_sum_add,pooled_sum_scale,pooled_sum_scale]
  change a * cubeSum m _ + b * cubeSum m _ = _
  rw [pooled_current_row_functional n m bounded,pooled_next_row_functional n m bounded]
/-- Full-bank coefficient identity for arbitrary bounded scattered cell weights.
Repeated cells from several logical functionals add, rather than overwrite.
This connects column/row placement to the existing scatter proof. -/
theorem pooled_scatter_coefficient_functional (dimension : Nat)
    (entries : List (Nat × K)) (values : Nat → K)
    (bounds : ∀ e ∈ entries, e.1 < 2^dimension) :
    cubeSum dimension (fun i => upperZeta dimension (gkrScatter entries) i *
      mobiusCoefficients dimension values i) =
      (entries.map (fun e => e.2 * values e.1)).sum := by
  rw [dual_mobius_dot]
  exact call_scatter_dot (2^dimension) entries values bounds
end NearCompression
