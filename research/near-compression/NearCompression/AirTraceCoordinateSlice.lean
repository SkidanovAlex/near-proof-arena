import NearCompression.BusPolynomialLowering

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Affineness in an arbitrary coordinate, with an already-fixed history and
suffix. Neither need be Boolean; values are the actual row table. -/
theorem air_mle_coordinate_affine (values : Nat→K) (history suffix : List K) (x : K) :
    packedGridEval (history.length+1+suffix.length) values (history++x::suffix)=
      (1-x)*packedGridEval (history.length+1+suffix.length) values (history++0::suffix)+
      x*packedGridEval (history.length+1+suffix.length) values (history++1::suffix) := by
  induction history generalizing values with
  | nil =>
    simp only [List.length_nil,Nat.zero_add,List.nil_append,Nat.add_comm 1 suffix.length,packed_grid_eval_cons]
    grind
  | cons y ys ih =>
    have size : (y::ys).length+1+suffix.length=(ys.length+1+suffix.length)+1 := by simp;omega
    simp only [size,List.cons_append,packed_grid_eval_cons,ih]
    grind

noncomputable def airCoordinatePolynomial (values : Nat→K) (history suffix : List K) : Poly K :=
  let a:=packedGridEval (history.length+1+suffix.length) values (history++0::suffix)
  let b:=packedGridEval (history.length+1+suffix.length) values (history++1::suffix)
  Poly.mk [a,b-a]

theorem air_coordinate_polynomial_eval (values : Nat→K) (history suffix : List K) (x : K) :
    (airCoordinatePolynomial values history suffix).eval x=
      packedGridEval (history.length+1+suffix.length) values (history++x::suffix) := by
  rw [air_mle_coordinate_affine values history suffix x]
  simp only [airCoordinatePolynomial,Poly.eval,Poly.evalL]
  grind

theorem air_coordinate_polynomial_degree (values : Nat→K) (history suffix : List K) :
    (airCoordinatePolynomial values history suffix).DegLt 2 := Poly.degLt_length _

/-- Actual current/cyclic-next columns and selector row tables; public inputs
are constant. No separately supplied affine environment is required. -/
noncomputable def airTraceCoordinateInputs (tr : Trace K) (t : Nat) (pubValues : List K)
    (history suffix : List K) : AirPolynomialInputs K where
  col:=fun c nx=>airCoordinatePolynomial
    (fun r=>tr.cell t (if nx then (r+1)%tr.height t else r) c) history suffix
  pub:=fun i=>Poly.C (pubValues.getD i 0)
  isFirst:=airCoordinatePolynomial (fun r=>if r=0 then 1 else 0) history suffix
  isLast:=airCoordinatePolynomial (fun r=>if r+1=tr.height t then 1 else 0) history suffix
  isTransition:=airCoordinatePolynomial (fun r=>if r+1=tr.height t then 0 else 1) history suffix

theorem air_trace_coordinate_affine (tr : Trace K) (t : Nat) (pubValues : List K) (history suffix : List K) :
    AirPolynomialAffine (airTraceCoordinateInputs tr t pubValues history suffix) := by
  exact ⟨fun _ _=>air_coordinate_polynomial_degree _ _ _,fun _=>Poly.degLt_length _,
    air_coordinate_polynomial_degree _ _ _,air_coordinate_polynomial_degree _ _ _,
    air_coordinate_polynomial_degree _ _ _⟩

theorem air_trace_coordinate_environment (tr : Trace K) (t : Nat) (pubValues : List K)
    (history suffix : List K) (length : history.length+1+suffix.length=tr.log t) (x : K) :
    airPolynomialPointEnv (airTraceCoordinateInputs tr t pubValues history suffix) x=
      airProductSelectorEnv tr t pubValues (history++x::suffix) := by
  rw [air_product_selector_env tr t pubValues _ (by simp only [List.length_append,List.length_cons];omega)]
  unfold airPolynomialPointEnv airTraceCoordinateInputs airRowMLEEnv
  simp only [air_coordinate_polynomial_eval,Poly.eval_C,length]

theorem bus_trace_coordinate_environment (tr : Trace K) (t : Nat) (pubValues : List K)
    (history suffix : List K) (length : history.length+1+suffix.length=tr.log t) (x : K) :
    busPolynomialPointEnv (airTraceCoordinateInputs tr t pubValues history suffix) x=
      busMLEProgramEnv tr t (history++x::suffix) := by
  unfold busPolynomialPointEnv busMLEProgramEnv
  rw [air_product_selector_env tr t [] _ (by simp only [List.length_append,List.length_cons];omega)]
  unfold airTraceCoordinateInputs airRowMLEEnv
  simp only [air_coordinate_polynomial_eval,length]

/-- Combined polynomial evaluation is the actual source/auxiliary point
residual batch on the common trace, including concrete product selectors. -/
theorem combined_trace_coordinate_eval (tr : Trace K) (t : Nat) (pubValues : List K)
    (history suffix : List K) (length : history.length+1+suffix.length=tr.log t)
    (source : List Expr) (auxiliary : List (BusProgramFormula K)) (mixing x : K) :
    (combinedAirPolynomial (airTraceCoordinateInputs tr t pubValues history suffix) source auxiliary mixing).eval x=
      lanePowerBatch mixing (airCombinedPointResiduals tr t pubValues source auxiliary (history++x::suffix)) := by
  rw [combined_air_polynomial_eval,air_trace_coordinate_environment tr t pubValues history suffix length x,
    bus_trace_coordinate_environment tr t pubValues history suffix length x]
  rfl

theorem air_kernel_coordinate_affine (tau history suffix : List K) (x : K) :
    whirKernel tau (history++x::suffix)=
      (1-x)*whirKernel tau (history++0::suffix)+x*whirKernel tau (history++1::suffix) := by
  induction history generalizing tau with
  | nil => cases tau <;> simp only [List.nil_append,whirKernel,whirEq] <;> grind
  | cons y ys ih => cases tau with
    | nil => simp only [List.cons_append,whirKernel];grind
    | cons a rest => simp only [List.cons_append,whirKernel,ih];grind

noncomputable def airKernelCoordinatePolynomial (tau history suffix : List K) : Poly K :=
  let a:=whirKernel tau (history++0::suffix)
  let b:=whirKernel tau (history++1::suffix)
  Poly.mk [a,b-a]

theorem air_kernel_coordinate_eval (tau history suffix : List K) (x : K) :
    (airKernelCoordinatePolynomial tau history suffix).eval x=whirKernel tau (history++x::suffix) := by
  rw [air_kernel_coordinate_affine tau history suffix x]
  simp only [airKernelCoordinatePolynomial,Poly.eval,Poly.evalL]
  grind

theorem air_kernel_coordinate_degree (tau history suffix : List K) :
    (airKernelCoordinatePolynomial tau history suffix).DegLt 2 := Poly.degLt_length _

end NearCompression
