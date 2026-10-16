import NearCompression.GenericLaneBatching
import NearCompression.GenericPackedGridCounting
import NearCompression.AIRProgramAccumulation

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

private theorem power_loop (registers : Nat→K) (mixing power : K) (ids : List Nat) :
    airMixValue registers mixing power ids=power*lanePowerBatch mixing (ids.map registers) := by
  induction ids generalizing power with
  | nil => simp only [airMixValue,List.map_nil,lanePowerBatch]; grind
  | cons id ids ih => simp only [airMixValue,List.map_cons,lanePowerBatch,ih]; grind

/-- The compiler's increasing-power accumulator is the same polynomial as
ordered Horner batching, including a zero mixing challenge. -/
theorem air_mix_value_power_batch (registers : Nat→K) (mixing : K) (ids : List Nat) :
    airMixValue registers mixing 1 ids=lanePowerBatch mixing (ids.map registers) := by
  rw [power_loop]
  grind

private theorem zeros_batch (mixing : K) (n : Nat) :
    lanePowerBatch mixing (List.replicate n 0)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,lanePowerBatch,ih]; grind

private theorem conditional_sum {A B : Type} (xs : List A) (ys : List B)
    (bad : A→Prop) (accept : A→B→Prop) (limit : Nat)
    (good : ∀ x∈xs,¬bad x→count ys (accept x)≤limit) :
    (xs.map (fun x=>count ys (accept x))).sum≤count xs bad*ys.length+xs.length*limit := by
  classical
  induction xs with
  | nil => simp [count]
  | cons x xs ih =>
    have tail:=ih (fun y hy=>good y (by simp [hy]))
    have head:=good x (by simp)
    have maximum : count ys (accept x)≤ys.length:=List.countP_le_length
    simp only [List.map_cons,List.sum_cons,count,List.countP_cons,List.length_cons] at *
    by_cases h:bad x <;> simp_all <;> grind

/-- Ideal initial zerocheck error: a fixed nonzero row/residual can disappear
under power batching or under row equality weighting. Residuals are fixed
before mixing and the row point; no prover-chosen postchallenge matrix. -/
theorem air_residual_batch_zero_count (n L row lane : Nat) (residuals : Nat→List K)
    (positive : 0<L) (rowBound : row<2^(n+1)) (shape : (residuals row).length=L)
    (wrong : (residuals row).getD lane 0≠0)
    (sample : List K) (distinct : sample.Nodup) :
    count (sample.flatMap (fun mixing=>(packedGrid sample (n+1)).map (fun point=>(mixing,point))))
      (fun pair=>packedGridEval (n+1) (fun r=>lanePowerBatch pair.1 (residuals r)) pair.2=0) ≤
      (L-1)*sample.length^(n+1)+sample.length*((n+1)*sample.length^n) := by
  let bad:=fun mixing=>lanePowerBatch mixing (residuals row)=0
  let accept:=fun mixing point=>packedGridEval (n+1) (fun r=>lanePowerBatch mixing (residuals r)) point=0
  have mixBound : count sample bad≤L-1 := by
    have h:=lane_claim_batch_bad_count_le (residuals row) (List.replicate L (0:K)) L lane
      positive shape (by simp) (by
        have zero : (List.replicate L (0:K)).getD lane 0=0 := by
          by_cases hl:lane<L <;> simp [List.getD,hl]
        simpa only [zero] using wrong) sample distinct
    simpa only [bad,zeros_batch] using h
  have rowBounded (mixing : K) (_ : mixing∈sample) (notBad : ¬bad mixing) :
      count (packedGrid sample (n+1)) (accept mixing)≤(n+1)*sample.length^n := by
    have h:=packed_claim_grid_bad_count n row (fun r=>lanePowerBatch mixing (residuals r))
      (fun _=>(0:K)) rowBound notBad sample distinct
    have zero (point : List K) : packedGridEval (n+1) (fun _=>(0:K)) point=0:=generic_row_mle_zero _ _
    simpa only [accept,zero] using h
  have h:=conditional_sum sample (packedGrid sample (n+1)) bad accept
    ((n+1)*sample.length^n) rowBounded
  have result:=Nat.le_trans h (Nat.add_le_add_right
    (Nat.mul_le_mul_right (packedGrid sample (n+1)).length mixBound) _)
  simpa only [count,List.countP_flatMap,List.countP_map,Function.comp_def,accept,packed_grid_length] using result

end NearCompression
