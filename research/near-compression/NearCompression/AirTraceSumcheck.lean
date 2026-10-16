import NearCompression.AirTraceCoordinateSlice

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def airBooleanSuffixes : Nat→List (List K)
  | 0 => [[]]
  | n+1 => (airBooleanSuffixes n).map ((0:K)::·)++(airBooleanSuffixes n).map ((1:K)::·)

theorem air_boolean_suffix_length (n : Nat) (suffix : List K) (member : suffix∈airBooleanSuffixes n) : suffix.length=n := by
  induction n generalizing suffix with
  | zero => simp [airBooleanSuffixes] at member;subst suffix;rfl
  | succ n ih =>
    rcases List.mem_append.mp member with h | h
    all_goals
      obtain ⟨xs,hx,rfl⟩:=List.mem_map.mp h
      simp only [List.length_cons,ih xs hx]

private theorem sum_append (xs ys : List K) : (xs++ys).sum=xs.sum+ys.sum := by
  induction xs with
  | nil => simp only [List.nil_append,List.sum_nil];grind
  | cons x xs ih => simp only [List.cons_append,List.sum_cons,ih];grind

theorem air_boolean_suffix_sum (n : Nat) (f : List K→K) :
    ((airBooleanSuffixes n).map f).sum=whirCubeSum n f := by
  induction n generalizing f with
  | zero => simp only [airBooleanSuffixes,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,whirCubeSum];grind
  | succ n ih => simp only [airBooleanSuffixes,List.map_append,sum_append,List.map_map,
      Function.comp_def,ih,whirCubeSum]

noncomputable def airTraceRoundSlices (tr : Trace K) (t : Nat) (pubValues tau history : List K) :
    List (AirPolynomialInputs K × Poly K) :=
  (airBooleanSuffixes (tr.log t-(history.length+1))).map fun suffix=>
    (airTraceCoordinateInputs tr t pubValues history suffix,airKernelCoordinatePolynomial tau history suffix)

noncomputable def airTraceWeightedValue (tr : Trace K) (t : Nat) (pubValues : List K)
    (source : List Expr) (auxiliary : List (BusProgramFormula K)) (mixing : K) (tau point : List K) : K :=
  whirKernel tau point*lanePowerBatch mixing (airCombinedPointResiduals tr t pubValues source auxiliary point)

/-- Honest rounds are constructed from the actual trace and Boolean suffix
assignments. Their evaluator is the fixed weighted combined residual function. -/
theorem air_trace_round_represents (tr : Trace K) (t : Nat) (pubValues : List K)
    (source : List Expr) (auxiliary : List (BusProgramFormula K)) (mixing : K)
    (tau history : List K) (short : history.length<tr.log t) (x : K) :
    (combinedAirRoundPolynomial source auxiliary mixing (airTraceRoundSlices tr t pubValues tau history)).eval x=
      polynomialSumcheckTruth (tr.log t) (airTraceWeightedValue tr t pubValues source auxiliary mixing tau) (history++[x]) := by
  rw [combined_air_round_eval]
  unfold airTraceRoundSlices
  simp only [List.map_map,Function.comp_def]
  have evaluated : ((airBooleanSuffixes (tr.log t-(history.length+1))).map (fun suffix=>
      (airKernelCoordinatePolynomial tau history suffix).eval x *
        lanePowerBatch mixing (source.map (fun e=>e.evalWith (airPolynomialPointEnv
          (airTraceCoordinateInputs tr t pubValues history suffix) x))++
          auxiliary.map (busProgramFormulaValue (busPolynomialPointEnv
            (airTraceCoordinateInputs tr t pubValues history suffix) x)))))=
      (airBooleanSuffixes (tr.log t-(history.length+1))).map
        (fun suffix=>airTraceWeightedValue tr t pubValues source auxiliary mixing tau (history++x::suffix)) := by
    apply List.map_congr_left
    intro suffix hs
    have size : history.length+1+suffix.length=tr.log t := by rw [air_boolean_suffix_length _ _ hs];omega
    rw [air_kernel_coordinate_eval,air_trace_coordinate_environment tr t pubValues history suffix size x,
      bus_trace_coordinate_environment tr t pubValues history suffix size x]
    rfl
  rw [evaluated,air_boolean_suffix_sum]
  simp only [polynomialSumcheckTruth,List.length_append,List.length_singleton,List.append_assoc,List.singleton_append]

/-- Full adaptive local sumcheck bound for the concrete combined trace
function. Affine inputs, degree and honest suffix representation are derived;
the terminal equality still requires a cryptographic binding argument. -/
theorem air_trace_adaptive_sumcheck_count (sample : List K) (distinct : sample.Nodup)
    (tr : Trace K) (t : Nat) (pubValues : List K) (source : List Expr)
    (auxiliary : List (BusProgramFormula K)) (mixing : K) (tau : List K) (d : Nat)
    (sourceDegrees : ∀ e∈source,e.degree≤d) (auxDegrees : ∀ e∈auxiliary,busFormulaDegree e≤d)
    (sent : List K→Poly K) (claim : List K→K)
    (wrong : claim []≠whirCubeSum (tr.log t) (airTraceWeightedValue tr t pubValues source auxiliary mixing tau)) :
    count (uniformTuples sample (tr.log t))
      (fun path=>polynomialSumcheckChecks (d+1) sent claim [] path ∧
        claim path=airTraceWeightedValue tr t pubValues source auxiliary mixing tau path)*sample.length≤
      ((d+1)*tr.log t)*sample.length^(tr.log t) := by
  apply combined_air_adaptive_sumcheck_count sample distinct source auxiliary mixing d (tr.log t)
    (airTraceWeightedValue tr t pubValues source auxiliary mixing tau) sent claim
    (airTraceRoundSlices tr t pubValues tau) sourceDegrees auxDegrees
  · intro h hh pw hp
    obtain ⟨suffix,_,rfl⟩:=List.mem_map.mp hp
    exact ⟨air_trace_coordinate_affine tr t pubValues h suffix,air_kernel_coordinate_degree tau h suffix⟩
  · intro h hh r
    exact air_trace_round_represents tr t pubValues source auxiliary mixing tau h hh r
  · exact wrong

end NearCompression
