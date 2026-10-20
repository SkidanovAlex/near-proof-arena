import NearCompression.AirResidualBatchSoundness
import NearCompression.WHIRTerminalWeight
import ArenaCore.Security.ROMLemmas

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Equality weighting reproduces the row MLE, not the monomial tensor. -/
theorem air_equality_weighted_mle (point : List K) (values : Nat→K) :
    whirCubeSum point.length (fun bits=>whirKernel point bits*packedGridEval point.length values bits)=
      packedGridEval point.length values point := by
  induction point generalizing values with
  | nil => simp only [List.length_nil,whirCubeSum,whirKernel,packedGridEval,genericRowMLE]; grind
  | cons x xs ih =>
    simp only [List.length_cons,whirCubeSum,whirKernel,packed_grid_eval_cons]
    have a : (fun bits=>whirEq x 0*whirKernel xs bits*
        ((1-0)*packedGridEval xs.length (fun i=>values (2*i)) bits+
          0*packedGridEval xs.length (fun i=>values (2*i+1)) bits)) =
      (fun bits=>(1-x)*(whirKernel xs bits*packedGridEval xs.length (fun i=>values (2*i)) bits)) := by
      funext bits; unfold whirEq; grind
    have b : (fun bits=>whirEq x 1*whirKernel xs bits*
        ((1-1)*packedGridEval xs.length (fun i=>values (2*i)) bits+
          1*packedGridEval xs.length (fun i=>values (2*i+1)) bits)) =
      (fun bits=>x*(whirKernel xs bits*packedGridEval xs.length (fun i=>values (2*i+1)) bits)) := by
      funext bits; unfold whirEq; grind
    rw [a,b,whir_cube_scale,whir_cube_scale,ih,ih]

/-- Only Boolean values of the actual constraint polynomial matter to the
initial target. No invalid commutation of nonlinear constraints with MLEs. -/
theorem air_cube_boolean_congr (n : Nat) (f g : List K→K)
    (equal : ∀ bits,bits.length=n→(∀ x∈bits,x=0 ∨ x=1)→f bits=g bits) :
    whirCubeSum n f=whirCubeSum n g := by
  induction n generalizing f g with
  | zero => exact equal [] rfl (by simp)
  | succ n ih =>
    simp only [whirCubeSum]
    congr 1
    · apply ih
      intro bits length boolean
      exact equal (0::bits) (by simp [length]) (by intro x hx;rcases List.mem_cons.mp hx with h|h;exact Or.inl h;exact boolean x h)
    · apply ih
      intro bits length boolean
      exact equal (1::bits) (by simp [length]) (by intro x hx;rcases List.mem_cons.mp hx with h|h;exact Or.inr h;exact boolean x h)

/-- A Boolean-row adapter is enough to identify the honest initial sumcheck
claim with the residual-vector MLE used by the counting theorem. -/
theorem air_equality_weighted_target (point : List K) (values : Nat→K) (evaluate : List K→K)
    (boolean : ∀ bits,bits.length=point.length→(∀ x∈bits,x=0 ∨ x=1)→
      evaluate bits=packedGridEval point.length values bits) :
    whirCubeSum point.length (fun bits=>whirKernel point bits*evaluate bits)=
      packedGridEval point.length values point := by
  rw [air_cube_boolean_congr point.length _
    (fun bits=>whirKernel point bits*packedGridEval point.length values bits)
    (by intro bits length isBool;rw [boolean bits length isBool])]
  exact air_equality_weighted_mle point values

omit [Field K] in
private theorem grid_point_length (sample : List K) (n : Nat) (point : List K)
    (member : point∈packedGrid sample n) : point.length=n := by
  induction n generalizing point with
  | zero => simpa [packedGrid] using member
  | succ n ih =>
    obtain ⟨tail,ht,hm⟩:=List.mem_flatMap.mp member
    obtain ⟨x,_,rfl⟩:=List.mem_map.mp hm
    simp [ih tail ht]

/-- Initial zerocheck bound for the equality-weighted Boolean sum of the
actual evaluator, assuming only its explicit Boolean-row correspondence. -/
theorem air_weighted_target_zero_count (n L row lane : Nat) (residuals : Nat→List K)
    (positive : 0<L) (rowBound : row<2^(n+1)) (shape : (residuals row).length=L)
    (wrong : (residuals row).getD lane 0≠0) (evaluate : K→List K→K)
    (boolean : ∀ mixing bits,bits.length=n+1→(∀ x∈bits,x=0 ∨ x=1)→
      evaluate mixing bits=packedGridEval (n+1) (fun r=>lanePowerBatch mixing (residuals r)) bits)
    (sample : List K) (distinct : sample.Nodup) :
    count (sample.flatMap (fun mixing=>(packedGrid sample (n+1)).map (fun point=>(mixing,point))))
      (fun pair=>whirCubeSum (n+1) (fun bits=>whirKernel pair.2 bits*evaluate pair.1 bits)=0) ≤
      (L-1)*sample.length^(n+1)+sample.length*((n+1)*sample.length^n) := by
  apply Nat.le_trans (count_mono_mem _ (fun pair member accepted=>?_))
    (air_residual_batch_zero_count n L row lane residuals positive rowBound shape wrong sample distinct)
  obtain ⟨mixing,_,hm⟩:=List.mem_flatMap.mp member
  obtain ⟨point,hp,rfl⟩:=List.mem_map.mp hm
  have length:=grid_point_length sample (n+1) point hp
  have target:=air_equality_weighted_target point (fun r=>lanePowerBatch mixing (residuals r))
    (evaluate mixing) (by simpa only [length] using boolean mixing)
  rw [length] at target
  exact target ▸ accepted

end NearCompression
