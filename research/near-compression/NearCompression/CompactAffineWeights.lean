import NearCompression.RepeatedAffineFold

/-! Compact monomial weight folding. The scalar accumulator is a product,
never a quotient, so zero factors are supported without exceptions. -/
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

/-- Little-endian weights: the low bit selects 1 or the first coordinate. -/
def compactTensorWeights : List K → List K
  | [] => [1]
  | z::zs => (compactTensorWeights zs).flatMap (fun w => [w,z*w])

def compactWeightScale : List K → List K → K
  | _,[] => 1
  | [],_::_ => 1
  | z::zs,r::rs => (1+r*(z-1))*compactWeightScale zs rs

def affineFoldValuesFinal (values : List K) : List K → List K
  | [] => values
  | r::rs => affineFoldValuesFinal (affineFoldValues r values) rs

/-- Literal scalar update used by a streaming verifier. -/
def compactWeightAccumulator (scalar : K) : List K → List K → K
  | _,[] => scalar
  | [],_::_ => scalar
  | z::zs,r::rs => compactWeightAccumulator (scalar*(1+r*(z-1))) zs rs

theorem compact_weight_accumulator (point challenges : List K) (scalar : K) :
    compactWeightAccumulator scalar point challenges=scalar*compactWeightScale point challenges := by
  induction challenges generalizing point scalar with
  | nil => simp only [compactWeightAccumulator,compactWeightScale]; grind
  | cons r rs ih =>
    cases point with
    | nil => simp only [compactWeightAccumulator,compactWeightScale]; grind
    | cons z zs => simp only [compactWeightAccumulator,compactWeightScale,ih]; grind

/-- High-coordinate extension, matching Python's `ws += [w*z for w in ws]`. -/
theorem compact_tensor_weights_append (point : List K) (z : K) :
    compactTensorWeights (point++[z]) =
      compactTensorWeights point++(compactTensorWeights point).map (fun w => w*z) := by
  induction point with
  | nil => simp only [List.nil_append,compactTensorWeights,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.cons.injEq]; grind
  | cons x xs ih =>
    simp only [List.cons_append,compactTensorWeights,ih,List.flatMap_append]
    congr 1
    simp only [List.flatMap_map,List.map_flatMap]
    congr 1
    funext w
    simp only [List.map_cons,List.map_nil,List.cons.injEq]
    grind

theorem compact_tensor_weights_length (point : List K) :
    (compactTensorWeights point).length=2^point.length := by
  induction point with
  | nil => rfl
  | cons z zs ih =>
    have pairs : ∀ values : List K,
        (values.flatMap (fun w => [w,z*w])).length=2*values.length := by
      intro values
      induction values with
      | nil => rfl
      | cons w ws h => simp [h]; omega
    simp only [compactTensorWeights,pairs,ih,List.length_cons,Nat.pow_succ]
    omega

theorem affine_fold_values_scale (r s : K) : ∀ values : List K,
    affineFoldValues r (values.map (fun v => s*v)) =
      (affineFoldValues r values).map (fun v => s*v)
  | [] => rfl
  | [_] => rfl
  | a::b::rest => by
    simp only [List.map_cons,affineFoldValues,affine_fold_values_scale r s rest]
    congr 1
    grind

theorem compact_tensor_one_fold (r z : K) (zs : List K) :
    affineFoldValues r (compactTensorWeights (z::zs)) =
      (compactTensorWeights zs).map (fun w => (1+r*(z-1))*w) := by
  have pairs : ∀ values : List K,
      affineFoldValues r (values.flatMap (fun w => [w,z*w])) =
        values.map (fun w => (1+r*(z-1))*w) := by
    intro values
    induction values with
    | nil => rfl
    | cons w ws ih =>
      simp only [List.flatMap_cons,List.cons_append,List.nil_append,affineFoldValues,List.map_cons,ih]
      congr 1
      grind
  exact pairs _

theorem affine_fold_values_final_scale (challenges values : List K) (s : K) :
    affineFoldValuesFinal (values.map (fun v => s*v)) challenges =
      (affineFoldValuesFinal values challenges).map (fun v => s*v) := by
  induction challenges generalizing values with
  | nil => rfl
  | cons r rs ih =>
    simp only [affineFoldValuesFinal,affine_fold_values_scale,ih]

/-- Exact vector identity for the executable adjacent-pair folding rule. -/
theorem compact_affine_weights (point challenges : List K)
    (shape : challenges.length≤point.length) :
    affineFoldValuesFinal (compactTensorWeights point) challenges =
      (compactTensorWeights (point.drop challenges.length)).map
        (fun w => compactWeightScale point challenges*w) := by
  induction challenges generalizing point with
  | nil =>
    simp only [affineFoldValuesFinal,List.length_nil,List.drop_zero,compactWeightScale]
    have eq : (fun w : K => 1*w)=(fun w => w) := by funext w; grind
    rw [eq]
    exact (List.map_id _).symm
  | cons r rs ih =>
    cases point with
    | nil => simp at shape
    | cons z zs =>
      have smaller : rs.length≤zs.length := by simp only [List.length_cons] at shape; omega
      simp only [affineFoldValuesFinal,compact_tensor_one_fold,
        affine_fold_values_final_scale,ih zs smaller,List.map_map,
        List.length_cons,List.drop_succ_cons,compactWeightScale,Function.comp_def]
      congr 1
      funext w
      grind

theorem affine_fold_final_weights (challenges : List K) (values : List (K×K)) :
    (affineFoldFinal values challenges).map Prod.snd =
      affineFoldValuesFinal (values.map Prod.snd) challenges := by
  induction challenges generalizing values with
  | nil => rfl
  | cons r rs ih =>
    simp only [affineFoldFinal,affineFoldValuesFinal,ih,(affine_fold_coordinates r values).2]

/-- Direct interface to the existing paired coefficient/weight state. -/
theorem compact_affine_final_state_weights (point challenges : List K)
    (values : List (K×K)) (weights : values.map Prod.snd=compactTensorWeights point)
    (shape : challenges.length≤point.length) :
    (affineFoldFinal values challenges).map Prod.snd =
      (compactTensorWeights (point.drop challenges.length)).map
        (fun w => compactWeightScale point challenges*w) := by
  rw [affine_fold_final_weights,weights]
  exact compact_affine_weights point challenges shape

theorem compact_affine_weights_length (point challenges : List K)
    (shape : challenges.length≤point.length) :
    (affineFoldValuesFinal (compactTensorWeights point) challenges).length =
      2^(point.length-challenges.length) := by
  rw [compact_affine_weights point challenges shape,List.length_map,
    compact_tensor_weights_length,List.length_drop]

end NearCompression
