import NearCompression.AirBooleanRowEnvironment

namespace NearCompression
open Lean.Grind ZkFormal.Air
variable {K : Type} [Field K]

private theorem constant_mle (n : Nat) (value : K) (point : Nat→K) :
    genericRowMLE n (fun _=>value) point=value := by
  induction n generalizing point with
  | zero => rfl
  | succ n ih => simp only [genericRowMLE,ih]; grind

/-- Executable first-row product is the selector MLE at all field points. -/
theorem air_first_selector_product (point : List K) :
    packedGridEval point.length (fun r=>if r=0 then (1:K) else 0) point=
      (point.map (fun x=>1-x)).prod := by
  induction point with
  | nil => rfl
  | cons x xs ih =>
    rw [List.length_cons,packed_grid_eval_cons]
    have even : (fun i=>if 2*i=0 then (1:K) else 0)=(fun i=>if i=0 then 1 else 0) := by
      funext i
      have h : (2*i=0)↔i=0:=by omega
      simp only [h]
    have odd : (fun i=>if 2*i+1=0 then (1:K) else 0)=(fun _=>0) := by
      funext i;simp
    rw [even,odd,ih]
    have zero : packedGridEval xs.length (fun _=>(0:K)) xs=0:=generic_row_mle_zero _ _
    rw [zero]
    simp only [List.map_cons,List.prod_cons]
    grind

/-- Executable last-row product includes the final Boolean row exactly. -/
theorem air_last_selector_product (point : List K) :
    packedGridEval point.length (fun r=>if r+1=2^point.length then (1:K) else 0) point=point.prod := by
  induction point with
  | nil => rfl
  | cons x xs ih =>
    rw [List.length_cons,packed_grid_eval_cons]
    have even : (fun i=>if 2*i+1=2^(xs.length+1) then (1:K) else 0)=(fun _=>0) := by
      funext i
      have ne : 2*i+1≠2^(xs.length+1) := by rw [Nat.pow_succ];omega
      simp [ne]
    have odd : (fun i=>if 2*i+1+1=2^(xs.length+1) then (1:K) else 0)=
        (fun i=>if i+1=2^xs.length then 1 else 0) := by
      funext i
      have h : (2*i+1+1=2^(xs.length+1))↔i+1=2^xs.length := by rw [Nat.pow_succ];omega
      simp only [h]
    rw [even,odd,ih]
    have zero : packedGridEval xs.length (fun _=>(0:K)) xs=0:=generic_row_mle_zero _ _
    rw [zero,List.prod_cons]
    grind

/-- The transition selector is one minus last, including zero-dimensional
and off-Boolean points. -/
theorem air_transition_selector_product (point : List K) :
    packedGridEval point.length (fun r=>if r+1=2^point.length then (0:K) else 1) point=1-point.prod := by
  have values : (fun r=>if r+1=2^point.length then (0:K) else 1)=
      (fun r=>(1:K)+(-1)*(if r+1=2^point.length then 1 else 0)) := by
    funext r;split <;> grind
  rw [values]
  unfold packedGridEval
  rw [generic_row_mle_add,constant_mle,generic_row_mle_scale]
  have last:=air_last_selector_product point
  unfold packedGridEval at last
  rw [last]
  grind

/-- Same columns/public inputs, with the actual verifier's selector formulas. -/
noncomputable def airProductSelectorEnv (tr : Trace K) (t : Nat) (pub : List K) (point : List K) : Env K :=
  {airRowMLEEnv tr t pub point with
    isFirst:=(point.map (fun x=>1-x)).prod
    isLast:=point.prod
    isTransition:=1-point.prod}

/-- The product-selector environment agrees everywhere, not just on rows. -/
theorem air_product_selector_env (tr : Trace K) (t : Nat) (pub : List K)
    (point : List K) (length : point.length=tr.log t) :
    airProductSelectorEnv tr t pub point=airRowMLEEnv tr t pub point := by
  unfold airProductSelectorEnv airRowMLEEnv
  simp only [Trace.height,←length,air_first_selector_product,air_last_selector_product,air_transition_selector_product]

/-- Actual product selectors can be used directly in the source-expression
Boolean-row adapter. -/
theorem air_product_selector_expression_boolean (tr : Trace K) (t : Nat) (pub : List K)
    (point : List K) (length : point.length=tr.log t) (boolean : ∀ x∈point,x=0 ∨ x=1) (e : Expr) :
    e.evalWith (airProductSelectorEnv tr t pub point)=e.eval tr t (airBooleanIndex point) pub := by
  rw [air_product_selector_env tr t pub point length]
  exact air_row_mle_expression_boolean tr t pub point length boolean e

end NearCompression
