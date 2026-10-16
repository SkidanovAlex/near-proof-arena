import NearCompression.InterleavedResidual
import NearCompression.GenericRowMLE

/-! Equality weights in little-endian coefficient order. The first challenge
is the low bit: recursively interleave (1-r) and r times the tail weights.
Both sides below read exactly the first 2^point.length coefficient positions;
no degree bound or nonzero challenge factor is required. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def equalityWeights : List K → List K
  | [] => [1]
  | r::rs => rsInterleave ((equalityWeights rs).map (fun w => (1-r)*w))
      ((equalityWeights rs).map (fun w => r*w))

def equalityWeightRead : List K → (Nat → K) → K
  | [],_ => 0
  | w::ws,values => w*values 0+equalityWeightRead ws (fun i => values (i+1))

private theorem equality_read_congr (weights : List K) (a b : Nat → K) (equal : ∀ i,a i=b i) :
    equalityWeightRead weights a=equalityWeightRead weights b := by
  have h : a=b := funext equal
  rw [h]

private theorem equality_read_interleave (weights : List K) (w0 w1 : K) (values : Nat → K) :
    equalityWeightRead (rsInterleave (weights.map (fun w => w0*w)) (weights.map (fun w => w1*w))) values=
      w0*equalityWeightRead weights (fun i => values (2*i))+
      w1*equalityWeightRead weights (fun i => values (2*i+1)) := by
  induction weights generalizing values with
  | nil => simp only [List.map_nil,rsInterleave,equalityWeightRead]; grind
  | cons w ws ih =>
    simp only [List.map_cons,rsInterleave,equalityWeightRead]
    rw [ih]
    have even : (fun i => values (2*i+1+1))=(fun i => values (2*(i+1))) := by
      funext i
      congr 1
    have odd : (fun i => values (2*i+1+1+1))=(fun i => values (2*(i+1)+1)) := by
      funext i
      congr 1
    rw [even,odd]
    grind

theorem equality_weight_read_mle (point : List K) (values : Nat → K) :
    equalityWeightRead (equalityWeights point) values=
      genericRowMLE point.length values (fun i => point.getD i 0) := by
  induction point generalizing values with
  | nil => simp only [equalityWeights,equalityWeightRead,List.length_nil,genericRowMLE]; grind
  | cons r rs ih =>
    rw [equalityWeights,equality_read_interleave,ih,ih]
    simp only [List.length_cons,genericRowMLE,List.getD_cons_zero,List.getD_cons_succ]

private theorem scalar_residual_read (weights : List K) (p : Poly K) (offset : Nat) :
    scalarRSResidualFrom p offset weights=equalityWeightRead weights (fun i => p.coeff (offset+i)) := by
  induction weights generalizing offset with
  | nil => rfl
  | cons w ws ih =>
    simp only [scalarRSResidualFrom,equalityWeightRead,Nat.add_zero,ih]
    congr 1
    apply equality_read_congr
    intro i
    congr 1
    omega

/-- Exact scalar residual/MLE representation used at the weighted-joint to
folding boundary. This also includes r=0, r=1 and vanishing products. -/
theorem scalar_residual_eq_weights_mle (point : List K) (p : Poly K) :
    scalarRSResidual (equalityWeights point) p=
      genericRowMLE point.length p.coeff (fun i => point.getD i 0) := by
  unfold scalarRSResidual
  rw [scalar_residual_read]
  simpa only [Nat.zero_add] using equality_weight_read_mle point p.coeff

private theorem interleave_equal_length (a b : List K) (same : a.length=b.length) :
    (rsInterleave a b).length=2*a.length := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [rsInterleave]
  | cons x xs ih =>
    cases b with
    | nil => simp at same
    | cons y ys =>
      have h := ih ys (by simpa using same)
      simp only [rsInterleave,List.length_cons,h]
      omega

theorem equality_weights_length (point : List K) : (equalityWeights point).length=2^point.length := by
  induction point with
  | nil => rfl
  | cons r rs ih =>
    rw [equalityWeights,interleave_equal_length _ _ (by simp)]
    simp only [List.length_map,ih,List.length_cons,Nat.pow_succ]
    omega

end NearCompression
