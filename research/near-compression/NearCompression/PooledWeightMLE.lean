import NearCompression.PooledRowFunctional
import NearCompression.GenericPackingIdentity
import NearCompression.SparseLiftMLE
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

private theorem pooled_upper_zero (n i : Nat) : upperZeta n (fun _ => (0:K)) i=0 := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    have zero : (fun _ : Nat => (0:K)+0)=(fun _ => (0:K)) := by funext j; grind
    simp only [upperZeta,zero,ih]
    split <;> rfl

/-- Upper-zeta of a logical row prefix remains supported on that prefix.
This is what permits compact beta evaluation without the full bank tensor. -/
theorem pooled_upper_zeta_mask (m n : Nat) (height : n≤m) (weights : Nat → K)
    (i : Nat) (bound : i<2^m) :
    upperZeta m (pooledRowMask n weights) i = pooledRowMask n (upperZeta n weights) i := by
  induction m generalizing n weights i with
  | zero =>
    have hn : n=0 := by omega
    have hi : i=0 := by simpa using bound
    subst n; subst i
    simp [upperZeta,pooledRowMask]
  | succ m ih =>
    have half : i/2<2^m := by rw [Nat.pow_succ] at bound; omega
    cases n with
    | zero =>
      have even : (fun j => pooledRowMask 0 weights (2*j)+pooledRowMask 0 weights (2*j+1)) = pooledRowMask 0 weights := by
        funext j
        unfold pooledRowMask
        simp only [Nat.pow_zero]
        by_cases hj : j=0
        · subst j; simp; grind
        · have a : ¬2*j<1 := by omega
          have b : ¬2*j+1<1 := by omega
          have c : ¬j<1 := by omega
          simp [a,b,c]; grind
      have odd : (fun j => pooledRowMask 0 weights (2*j+1))=(fun _ => (0:K)) := by
        funext j
        unfold pooledRowMask
        rw [ite_eq_right (by simp only [Nat.pow_zero]; omega)]
      change (if i%2=0 then upperZeta m _ (i/2) else upperZeta m _ (i/2)) = _
      rw [even,odd,pooled_upper_zero,ih 0 (by omega) weights (i/2) half]
      by_cases parity : i%2=0
      · have small : (i/2<1) ↔ i<1 := by omega
        simp [parity,pooledRowMask,upperZeta,small]
      · have big : ¬i<1 := by omega
        simp [parity,pooledRowMask,big]
    | succ n =>
      have hn : n≤m := by omega
      have even : (fun j => pooledRowMask (n+1) weights (2*j)+pooledRowMask (n+1) weights (2*j+1)) =
          pooledRowMask n (fun j => weights (2*j)+weights (2*j+1)) := by
        funext j
        have a : (2*j<2^(n+1)) ↔ j<2^n := by rw [Nat.pow_succ]; omega
        have b : (2*j+1<2^(n+1)) ↔ j<2^n := by rw [Nat.pow_succ]; omega
        simp only [pooledRowMask,a,b]
        split <;> grind
      have odd : (fun j => pooledRowMask (n+1) weights (2*j+1)) =
          pooledRowMask n (fun j => weights (2*j+1)) := by
        funext j
        have b : (2*j+1<2^(n+1)) ↔ j<2^n := by rw [Nat.pow_succ]; omega
        simp only [pooledRowMask,b]
      change (if i%2=0 then upperZeta m _ (i/2) else upperZeta m _ (i/2)) = _
      rw [even,odd,ih n hn _ (i/2) half,ih n hn _ (i/2) half]
      have small : (i/2<2^n) ↔ i<2^(n+1) := by rw [Nat.pow_succ]; omega
      by_cases parity : i%2=0 <;> simp [pooledRowMask,upperZeta,parity,small]
private theorem pooled_zero_index_mle (k : Nat) (value : K) (point : Nat → K) :
    genericRowMLE k (fun i => if i=0 then value else 0) point = lowZeroFactor k point * value := by
  induction k generalizing point with
  | zero => simp [genericRowMLE,lowZeroFactor]; grind
  | succ k ih =>
    have even : (fun i : Nat => if 2*i=0 then value else 0) = (fun i => if i=0 then value else 0) := by
      funext i
      have same : (2*i=0) ↔ i=0 := by omega
      simp only [same]
    have odd : (fun i : Nat => if 2*i+1=0 then value else 0) = (fun _ => (0:K)) := by
      funext i
      rw [ite_eq_right (by omega)]
    change (1-point 0)*genericRowMLE k _ (fun i => point (i+1)) +
      point 0*genericRowMLE k _ (fun i => point (i+1)) = _
    rw [even,odd,generic_row_mle_zero,ih]
    simp only [lowZeroFactor]
    grind

/-- Logical row bits precede the unused high physical-row bits. Their exact
factor is a product of (1-u), and does not rotate the logical next-row weights. -/
theorem pooled_row_mask_mle (n extra : Nat) (weights point : Nat → K) :
    genericRowMLE (n+extra) (pooledRowMask n weights) point =
      lowZeroFactor extra (fun i => point (n+i)) * genericRowMLE n weights point := by
  rw [generic_row_mle_split_axes]
  have slices : (fun col => genericRowMLE n
      (fun row => pooledRowMask n weights (row+2^n*col)) point) =
      (fun col => if col=0 then genericRowMLE n weights point else 0) := by
    funext col
    by_cases zero : col=0
    · subst col
      simp only [Nat.mul_zero,Nat.add_zero,ite_true]
      apply generic_row_mle_congr
      intro row bound
      simp [pooledRowMask,bound]
    · rw [ite_eq_right zero]
      have large : 2^n ≤ 2^n*col := by
        simpa using Nat.mul_le_mul_left (2^n) (show 1≤col by omega)
      have same : genericRowMLE n (fun row => pooledRowMask n weights (row+2^n*col)) point =
          genericRowMLE n (fun _ => (0:K)) point := by
        apply generic_row_mle_congr
        intro row bound
        unfold pooledRowMask
        rw [ite_eq_right (by omega)]
      rw [same,generic_row_mle_zero]
  rw [slices,pooled_zero_index_mle]

/-- Compact beta row factor for the actual masked dual transform. This applies
to both ordinary equality weights and logical cyclic-next equality weights. -/
theorem pooled_upper_weight_mle (n extra : Nat) (weights point : Nat → K) :
    genericRowMLE (n+extra) (upperZeta (n+extra) (pooledRowMask n weights)) point =
      lowZeroFactor extra (fun i => point (n+i)) * genericRowMLE n (upperZeta n weights) point := by
  have same : genericRowMLE (n+extra) (upperZeta (n+extra) (pooledRowMask n weights)) point =
      genericRowMLE (n+extra) (pooledRowMask n (upperZeta n weights)) point := by
    apply generic_row_mle_congr
    intro i bound
    exact pooled_upper_zeta_mask (n+extra) n (by omega) weights i bound
  rw [same,pooled_row_mask_mle]
end NearCompression
