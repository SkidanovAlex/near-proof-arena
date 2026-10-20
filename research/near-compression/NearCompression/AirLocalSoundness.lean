import NearCompression.AirTraceSumcheck

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

theorem conditional_scaled_accept_count {A B : Type} (initial : List A) (paths : List B)
    (bad : A→Prop) (accept : A→B→Prop) (scale limit : Nat)
    (good : ∀ a∈initial,¬bad a → count paths (accept a)*scale≤limit) :
    (initial.map (fun a=>count paths (accept a))).sum*scale≤
      count initial bad*paths.length*scale+initial.length*limit := by
  classical
  induction initial with
  | nil => simp [count]
  | cons a rest ih =>
    have tail:=ih (fun b hb=>good b (List.mem_cons_of_mem _ hb))
    have head:=good a (List.mem_cons_self ..)
    have maximum : count paths (accept a)*scale≤paths.length*scale :=
      Nat.mul_le_mul_right scale List.countP_le_length
    simp only [List.map_cons,List.sum_cons,count,List.countP_cons,List.length_cons] at tail head maximum ⊢
    by_cases h : bad a <;> simp_all <;> grind

def airLocalInitialChallenges (sample : List K) (rounds : Nat) : List (K × List K) :=
  sample.flatMap (fun mixing=>(packedGrid sample rounds).map (fun tau=>(mixing,tau)))

private theorem initial_length (sample : List K) (rounds : Nat) :
    (airLocalInitialChallenges sample rounds).length=sample.length^(rounds+1) := by
  unfold airLocalInitialChallenges
  simp only [List.length_flatMap,List.length_map,packed_grid_length]
  have constant (xs : List K) (value : Nat) : (xs.map (fun _=>value)).sum=xs.length*value := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih,Nat.add_mul,Nat.add_comm]
  rw [constant,Nat.pow_succ,Nat.mul_comm]

/-- Exact count over mixing, equality point, and adaptive sumcheck challenge
paths. Strategies may depend on the initial mixing and equality point. -/
noncomputable def airLocalAcceptedCount (sample : List K) (tr : Trace K) (t : Nat)
    (pubValues : List K) (source : List Expr) (auxiliary : List (BusProgramFormula K)) (d : Nat)
    (sent : K→List K→List K→Poly K) (claim : K→List K→List K→K) : Nat :=
  ((airLocalInitialChallenges sample (tr.log t)).map (fun initial=>
    count (uniformTuples sample (tr.log t)) (fun path=>
      polynomialSumcheckChecks (d+1) (sent initial.1 initial.2) (claim initial.1 initial.2) [] path ∧
      claim initial.1 initial.2 path=airTraceWeightedValue tr t pubValues source auxiliary initial.1 initial.2 path))).sum

private theorem normalize_budget (B D q r : Nat) :
    B*q^r*q^r*q+q^(r+1)*(D*q^r)=(B+D)*q^(2*r+1) := by
  have power : q^(2*r+1)=q^r*q^r*q := by
    rw [show 2*r+1=(r+r)+1 by omega,Nat.pow_succ,Nat.pow_add]
  rw [power,Nat.pow_succ]
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

/-- Combined initial batching/row-MLE and adaptive-round error for a concrete
invalid trace. For q>0, the conditional acceptance probability is at most
(residualCount-1+rounds+(d+1)*rounds)/q. Terminal equality is to the honest
trace evaluator; cryptographic authentication remains separate. -/
theorem air_local_invalid_trace_count (sample : List K) (distinct : sample.Nodup)
    (tr : Trace K) (t : Nat) (pubValues : List K) (source : List Expr)
    (auxiliary : List (BusProgramFormula K)) (d n row lane : Nat)
    (height : tr.log t=n+1) (positive : 0<source.length+auxiliary.length)
    (rowBound : row<2^(n+1))
    (wrong : (airCombinedRowResiduals tr t pubValues source auxiliary row).getD lane 0≠0)
    (sourceDegrees : ∀ e∈source,e.degree≤d) (auxDegrees : ∀ e∈auxiliary,busFormulaDegree e≤d)
    (sent : K→List K→List K→Poly K) (claim : K→List K→List K→K)
    (initialZero : ∀ mixing tau,claim mixing tau []=0) :
    airLocalAcceptedCount sample tr t pubValues source auxiliary d sent claim*sample.length≤
      (source.length+auxiliary.length-1+(n+1)+(d+1)*(n+1))*sample.length^(2*(n+1)+1) := by
  let bad := fun initial : K × List K=>
    whirCubeSum (tr.log t) (airTraceWeightedValue tr t pubValues source auxiliary initial.1 initial.2)=0
  let accept := fun initial : K × List K=>fun path=>
    polynomialSumcheckChecks (d+1) (sent initial.1 initial.2) (claim initial.1 initial.2) [] path ∧
      claim initial.1 initial.2 path=airTraceWeightedValue tr t pubValues source auxiliary initial.1 initial.2 path
  have conditional := conditional_scaled_accept_count (airLocalInitialChallenges sample (tr.log t))
    (uniformTuples sample (tr.log t)) bad accept sample.length
    (((d+1)*tr.log t)*sample.length^(tr.log t)) (by
      intro initial _ good
      apply air_trace_adaptive_sumcheck_count sample distinct tr t pubValues source auxiliary
        initial.1 initial.2 d sourceDegrees auxDegrees (sent initial.1 initial.2) (claim initial.1 initial.2)
      rw [initialZero]
      exact Ne.symm good)
  have batching := air_combined_weighted_zero_count tr t pubValues source auxiliary n row lane
    height positive rowBound wrong sample distinct
  have batchBound : count (airLocalInitialChallenges sample (tr.log t)) bad≤
      (source.length+auxiliary.length-1+(n+1))*sample.length^(n+1) := by
    change count (airLocalInitialChallenges sample (tr.log t)) bad≤_
    have same : count (airLocalInitialChallenges sample (tr.log t)) bad≤
        (source.length+auxiliary.length-1)*sample.length^(n+1)+sample.length*((n+1)*sample.length^n) := by
      unfold airLocalInitialChallenges
      dsimp only [bad]
      rw [height]
      exact batching
    have rhs : (source.length+auxiliary.length-1)*sample.length^(n+1)+sample.length*((n+1)*sample.length^n)=
        (source.length+auxiliary.length-1+(n+1))*sample.length^(n+1) := by
      simp only [Nat.pow_succ]
      grind
    exact rhs ▸ same
  change airLocalAcceptedCount sample tr t pubValues source auxiliary d sent claim*sample.length≤_ at conditional
  rw [uniform_tuples_length,initial_length,height] at conditional
  have scaled := Nat.mul_le_mul_right sample.length (Nat.mul_le_mul_right (sample.length^(n+1)) batchBound)
  rw [height] at scaled
  have result := Nat.le_trans conditional (Nat.add_le_add_right scaled
    (sample.length^(n+1+1)*(((d+1)*(n+1))*sample.length^(n+1))))
  exact normalize_budget (source.length+auxiliary.length-1+(n+1)) ((d+1)*(n+1)) sample.length (n+1) ▸ result

end NearCompression
