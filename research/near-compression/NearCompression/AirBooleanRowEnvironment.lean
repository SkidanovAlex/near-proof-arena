import NearCompression.AirEqualityWeightedTarget

namespace NearCompression
open Lean.Grind ZkFormal.Air
variable {K : Type} [Field K]
attribute [local instance] Classical.propDecidable

noncomputable def airBooleanIndex : List K→Nat
  | [] => 0
  | x::xs => (if x=1 then 1 else 0)+2*airBooleanIndex xs

private theorem boolean_mle (point : List K) (values : Nat→K)
    (boolean : ∀ x∈point,x=0 ∨ x=1) :
    packedGridEval point.length values point=values (airBooleanIndex point) := by
  classical
  induction point generalizing values with
  | nil => rfl
  | cons x xs ih =>
    have tail:=fun y hy=>boolean y (List.mem_cons_of_mem x hy)
    simp only [List.length_cons,packed_grid_eval_cons,airBooleanIndex]
    rw [ih _ tail,ih _ tail]
    rcases boolean x (by simp) with rfl|rfl
    · have nz : (0:K)≠1:=Field.zero_ne_one
      simp only [nz,ite_false,Nat.zero_add]
      grind
    · simp only [ite_true]
      have index : 1+2*airBooleanIndex xs=2*airBooleanIndex xs+1:=by omega
      rw [index]
      grind

/-- Multilinear input environment: public inputs stay fixed, next rows are
cyclically permuted before interpolation, and selectors interpolate row flags. -/
noncomputable def airRowMLEEnv (tr : Trace K) (t : Nat) (pub : List K) (point : List K) : Env K where
  ofNat:=fun n=>@Nat.cast K Semiring.natCast n
  add:=(·+·)
  mul:=(·*·)
  neg:=(-·)
  pub:=fun i=>pub.getD i 0
  col:=fun c next=>packedGridEval (tr.log t)
    (fun r=>tr.cell t (if next then (r+1)%tr.height t else r) c) point
  isFirst:=packedGridEval (tr.log t) (fun r=>if r=0 then 1 else 0) point
  isLast:=packedGridEval (tr.log t) (fun r=>if r+1=tr.height t then 1 else 0) point
  isTransition:=packedGridEval (tr.log t) (fun r=>if r+1=tr.height t then 0 else 1) point

/-- Every source AIR expression agrees with actual Expr.eval at Boolean
rows, including cyclic-next columns and all three boundary selectors. -/
theorem air_row_mle_expression_boolean (tr : Trace K) (t : Nat) (pub : List K)
    (point : List K) (length : point.length=tr.log t) (boolean : ∀ x∈point,x=0 ∨ x=1) (e : Expr) :
    e.evalWith (airRowMLEEnv tr t pub point)=e.eval tr t (airBooleanIndex point) pub := by
  have atRow (values : Nat→K) : packedGridEval (tr.log t) values point=values (airBooleanIndex point) := by
    rw [←length]
    exact boolean_mle point values boolean
  induction e with
  | const n => rfl
  | pub i => rfl
  | col c next => exact atRow _
  | isFirst => exact atRow _
  | isLast => exact atRow _
  | isTransition => exact atRow _
  | add a b ha hb => change _+_= _+_; rw [ha,hb]; rfl
  | mul a b ha hb => change _*_= _*_; rw [ha,hb]; rfl
  | neg a ha => exact congrArg Neg.neg ha

/-- Ordered source residual batching discharges the weighted-target theorem's
Boolean-row correspondence for any source constraint list (including bits). -/
theorem air_source_batch_boolean (tr : Trace K) (t : Nat) (pub : List K) (constraints : List Expr)
    (mixing : K) (point : List K) (length : point.length=tr.log t)
    (boolean : ∀ x∈point,x=0 ∨ x=1) :
    lanePowerBatch mixing (constraints.map (fun e=>e.evalWith (airRowMLEEnv tr t pub point)))=
      packedGridEval (tr.log t) (fun r=>lanePowerBatch mixing (constraints.map (fun e=>e.eval tr t r pub))) point := by
  rw [←length,boolean_mle point _ boolean]
  apply congrArg (lanePowerBatch mixing)
  apply List.map_congr_left
  intro e _
  exact air_row_mle_expression_boolean tr t pub point length boolean e

/-- Source AIR equality-weighted sum, with Boolean correspondence derived
from the actual expressions rather than supplied as a premise. -/
theorem air_source_weighted_target (tr : Trace K) (t : Nat) (pub : List K) (constraints : List Expr)
    (mixing : K) (point : List K) (length : point.length=tr.log t) :
    whirCubeSum (tr.log t) (fun bits=>whirKernel point bits*
      lanePowerBatch mixing (constraints.map (fun e=>e.evalWith (airRowMLEEnv tr t pub bits))))=
    packedGridEval (tr.log t) (fun r=>lanePowerBatch mixing (constraints.map (fun e=>e.eval tr t r pub))) point := by
  have h:=air_equality_weighted_target point
    (fun r=>lanePowerBatch mixing (constraints.map (fun e=>e.eval tr t r pub)))
    (fun bits=>lanePowerBatch mixing (constraints.map (fun e=>e.evalWith (airRowMLEEnv tr t pub bits))))
    (by
      intro bits size boolean
      have hl : bits.length=tr.log t:=size.trans length
      simpa only [length] using air_source_batch_boolean tr t pub constraints mixing bits hl boolean)
  simpa only [length] using h

/-- Initial local error for concrete source AIR residuals. Auxiliary bus
residuals, adaptive rounds and authenticated inputs are separate obligations. -/
theorem air_source_weighted_zero_count (tr : Trace K) (t : Nat) (pub : List K) (constraints : List Expr)
    (n row lane : Nat) (height : tr.log t=n+1) (positive : 0<constraints.length)
    (rowBound : row<2^(n+1))
    (wrong : (constraints.map (fun e=>e.eval tr t row pub)).getD lane 0≠0)
    (sample : List K) (distinct : sample.Nodup) :
    ArenaCore.Security.count
      (sample.flatMap (fun mixing=>(packedGrid sample (n+1)).map (fun point=>(mixing,point))))
      (fun pair=>whirCubeSum (n+1) (fun bits=>whirKernel pair.2 bits*
        lanePowerBatch pair.1 (constraints.map (fun e=>e.evalWith (airRowMLEEnv tr t pub bits))))=0) ≤
      (constraints.length-1)*sample.length^(n+1)+sample.length*((n+1)*sample.length^n) := by
  apply air_weighted_target_zero_count n constraints.length row lane
    (fun r=>constraints.map (fun e=>e.eval tr t r pub)) positive rowBound (by simp) wrong
    (fun mixing bits=>lanePowerBatch mixing (constraints.map (fun e=>e.evalWith (airRowMLEEnv tr t pub bits))))
    ?_ sample distinct
  intro mixing bits length boolean
  simpa only [height] using air_source_batch_boolean tr t pub constraints mixing bits
    (length.trans height.symm) boolean

end NearCompression
