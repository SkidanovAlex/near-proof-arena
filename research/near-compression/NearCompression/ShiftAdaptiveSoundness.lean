import NearCompression.ShiftInitialClaim
import NearCompression.AirLocalSoundness

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

private def sumPolynomials : List (Poly K)→Poly K
  | [] => Poly.zero
  | p::rest => p+sumPolynomials rest

private theorem sum_polynomials_eval (polys : List (Poly K)) (x : K) :
    (sumPolynomials polys).eval x=(polys.map (fun p=>p.eval x)).sum := by
  induction polys with
  | nil => rfl
  | cons p rest ih => simp only [sumPolynomials,Poly.eval_add,List.map_cons,List.sum_cons,ih]

private theorem sum_polynomials_degree (polys : List (Poly K)) (bounds : ∀ p∈polys,p.DegLt 3) :
    (sumPolynomials polys).DegLt 3 := by
  induction polys with
  | nil => exact (Poly.degLt_length Poly.zero).mono (by change 0≤3;decide)
  | cons p rest ih =>
    exact Poly.degLt_add (bounds p (List.mem_cons_self ..))
      (ih (fun q hq=>bounds q (List.mem_cons_of_mem _ hq)))

noncomputable def shiftTraceValue (tr : Trace K) (t width : Nat) (target : List K) (alpha : K) (point : List K) : K :=
  shiftReductionWeight target point alpha width*lanePowerBatch alpha
    ((List.range width).map (fun c=>packedGridEval (tr.log t) (fun r=>tr.cell t r c) point))

noncomputable def shiftHonestRound (tr : Trace K) (t width : Nat) (target : List K) (alpha : K) (history : List K) : Poly K :=
  sumPolynomials ((airBooleanSuffixes (tr.log t-(history.length+1))).map
    (fun suffix=>shiftReductionSlicePolynomial tr t width target history suffix alpha))

theorem shift_honest_round_degree (tr : Trace K) (t width : Nat) (target history : List K) (alpha : K) :
    (shiftHonestRound tr t width target alpha history).DegLt 3 := by
  apply sum_polynomials_degree
  intro p hp
  obtain ⟨suffix,_,rfl⟩:=List.mem_map.mp hp
  exact shift_reduction_slice_degree tr t width target history suffix alpha

theorem shift_honest_round_represents (tr : Trace K) (t width : Nat) (target history : List K) (alpha x : K)
    (targetLength : target.length=tr.log t) (short : history.length<tr.log t) :
    (shiftHonestRound tr t width target alpha history).eval x=
      polynomialSumcheckTruth (tr.log t) (shiftTraceValue tr t width target alpha) (history++[x]) := by
  unfold shiftHonestRound
  rw [sum_polynomials_eval]
  simp only [List.map_map,Function.comp_def]
  have same : (airBooleanSuffixes (tr.log t-(history.length+1))).map
      (fun suffix=>(shiftReductionSlicePolynomial tr t width target history suffix alpha).eval x)=
      (airBooleanSuffixes (tr.log t-(history.length+1))).map
      (fun suffix=>shiftTraceValue tr t width target alpha (history++x::suffix)) := by
    apply List.map_congr_left
    intro suffix hs
    exact shift_reduction_slice_eval tr t width target history suffix alpha x targetLength
      (by rw [air_boolean_suffix_length _ _ hs];omega)
  rw [same,air_boolean_suffix_sum]
  simp only [polynomialSumcheckTruth,List.length_append,List.length_singleton,List.append_assoc,List.singleton_append]

theorem shift_adaptive_round_count (sample : List K) (distinct : sample.Nodup)
    (tr : Trace K) (t width : Nat) (target : List K) (targetLength : target.length=tr.log t) (alpha : K)
    (sent : List K→Poly K) (claim : List K→K)
    (wrong : claim []≠whirCubeSum (tr.log t) (shiftTraceValue tr t width target alpha)) :
    count (uniformTuples sample (tr.log t))
      (fun path=>polynomialSumcheckChecks 2 sent claim [] path ∧ claim path=shiftTraceValue tr t width target alpha path)*sample.length≤
      (2*tr.log t)*sample.length^(tr.log t) := by
  exact adaptive_polynomial_cube_sumcheck_count sample distinct 2 (tr.log t)
    (shiftTraceValue tr t width target alpha) sent (shiftHonestRound tr t width target alpha) claim
    (fun _ _=>shift_honest_round_degree _ _ _ _ _ _) (fun h hh r=>shift_honest_round_represents _ _ _ _ _ _ _ targetLength hh) wrong

def shiftTraceClaims (tr : Trace K) (t width : Nat) (target : List K) : List K :=
  shiftHonestClaims target ((List.range width).map (fun c=>fun r=>tr.cell t r c))

theorem shift_trace_initial_sum (tr : Trace K) (t width : Nat) (target : List K)
    (targetLength : target.length=tr.log t) (alpha : K) :
    whirCubeSum (tr.log t) (shiftTraceValue tr t width target alpha)=
      lanePowerBatch alpha (shiftTraceClaims tr t width target) := by
  have initial:=shift_reduction_batched_initial target ((List.range width).map (fun c=>fun r=>tr.cell t r c)) alpha
  unfold shiftTraceValue shiftTraceClaims shiftHonestClaims
  simpa only [List.length_map,List.length_range,List.map_map,Function.comp_def,targetLength] using initial

noncomputable def shiftAcceptedCount (sample : List K) (tr : Trace K) (t width : Nat) (target : List K)
    (sent : K→List K→Poly K) (claim : K→List K→K) : Nat :=
  (sample.map (fun alpha=>count (uniformTuples sample (tr.log t))
    (fun path=>polynomialSumcheckChecks 2 (sent alpha) (claim alpha) [] path ∧
      claim alpha path=shiftTraceValue tr t width target alpha path))).sum

/-- Full algebraic current/next reduction bound. The vector is fixed before
alpha; round messages may depend on alpha and the full prior challenge history.
Terminal equality still requires authenticating original-column PCS openings. -/
theorem shift_wrong_vector_count (sample : List K) (distinct : sample.Nodup)
    (tr : Trace K) (t width : Nat) (target : List K) (targetLength : target.length=tr.log t)
    (vector : List K) (shape : vector.length=2*width) (lane : Nat)
    (wrong : vector.getD lane 0≠(shiftTraceClaims tr t width target).getD lane 0)
    (sent : K→List K→Poly K) (claim : K→List K→K)
    (initial : ∀ alpha,claim alpha []=lanePowerBatch alpha vector) :
    shiftAcceptedCount sample tr t width target sent claim*sample.length≤
      (2*width-1+2*tr.log t)*sample.length^(tr.log t+1) := by
  let bad := fun alpha=>lanePowerBatch alpha vector=lanePowerBatch alpha (shiftTraceClaims tr t width target)
  let accept := fun alpha path=>polynomialSumcheckChecks 2 (sent alpha) (claim alpha) [] path ∧
    claim alpha path=shiftTraceValue tr t width target alpha path
  have bound:=conditional_scaled_accept_count sample (uniformTuples sample (tr.log t)) bad accept sample.length
    ((2*tr.log t)*sample.length^(tr.log t)) (by
      intro alpha _ good
      apply shift_adaptive_round_count sample distinct tr t width target targetLength alpha (sent alpha) (claim alpha)
      rw [initial,shift_trace_initial_sum tr t width target targetLength]
      exact good)
  have collision:=lane_claim_batch_bad_count vector (shiftTraceClaims tr t width target) (2*width) lane shape
    (by simp only [shiftTraceClaims,shiftHonestClaims,List.length_append,List.length_map,List.length_range];omega)
    wrong sample distinct
  have small : count sample bad≤2*width-1 := by dsimp only [bad];omega
  change shiftAcceptedCount sample tr t width target sent claim*sample.length≤_ at bound
  rw [uniform_tuples_length] at bound
  have result:=Nat.le_trans bound (Nat.add_le_add_right
    (Nat.mul_le_mul_right sample.length (Nat.mul_le_mul_right (sample.length^(tr.log t)) small))
    (sample.length*((2*tr.log t)*sample.length^(tr.log t))))
  have normalize (B D q r : Nat) : B*q^r*q+q*(D*q^r)=(B+D)*q^(r+1) := by
    rw [Nat.pow_succ]
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  exact normalize (2*width-1) (2*tr.log t) sample.length (tr.log t) ▸ result

end NearCompression
