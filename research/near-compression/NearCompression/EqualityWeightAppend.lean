import NearCompression.EqualityWeightResidual

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem interleave_map (f : K → K) (a b : List K) (same : a.length=b.length) :
    (rsInterleave a b).map f=rsInterleave (a.map f) (b.map f) := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [rsInterleave]
  | cons x xs ih =>
    cases b with
    | nil => simp at same
    | cons y ys => simp [rsInterleave,ih ys (by simpa using same)]

private theorem interleave_append (a b c d : List K) (same : a.length=b.length) :
    rsInterleave (a++c) (b++d)=rsInterleave a b++rsInterleave c d := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [rsInterleave]
  | cons x xs ih =>
    cases b with
    | nil => simp at same
    | cons y ys =>
      simp only [List.cons_append,rsInterleave]
      rw [ih ys (by simpa using same)]

/-- Exact iterative append order used by Python eq_weights: the newest
coordinate is the high bit. No factors are divided, so zero and one are valid. -/
theorem equality_weights_append (point : List K) (r : K) :
    equalityWeights (point++[r])=
      (equalityWeights point).map (fun v => v*(1-r))++
      (equalityWeights point).map (fun v => v*r) := by
  induction point with
  | nil => simp [equalityWeights,rsInterleave]; grind
  | cons a rest ih =>
    simp only [List.cons_append,equalityWeights,ih,List.map_append]
    rw [interleave_append _ _ _ _ (by simp)]
    rw [interleave_map _ _ _ (by simp),interleave_map _ _ _ (by simp)]
    simp only [List.map_map]
    congr 2 <;> apply List.map_congr_left <;> intro x hx <;> grind

end NearCompression
