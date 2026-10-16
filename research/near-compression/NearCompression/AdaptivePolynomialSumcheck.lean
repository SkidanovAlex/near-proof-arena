import NearCompression.AdaptiveWeightedSumcheck
import NearCompression.WHIRTerminalWeight

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def polynomialSumcheckChecks (degree : Nat) (sent : List K→Poly K) (claim : List K→K) :
    List K→List K→Prop
  | _,[] => True
  | history,r::rest =>
    (sent history).DegLt (degree+1) ∧
    (sent history).eval 0+(sent history).eval 1=claim history ∧
    claim (history++[r])=(sent history).eval r ∧
    polynomialSumcheckChecks degree sent claim (history++[r]) rest

def polynomialSumcheckBad (degree : Nat) (sent honest : List K→Poly K)
    (claim truth : List K→K) (history : List K) (r : K) : Prop :=
  (sent history).DegLt (degree+1) ∧
  (sent history).eval 0+(sent history).eval 1=claim history ∧
  claim history≠truth history ∧ (sent history).eval r=(honest history).eval r

/-- Malformed/aborted branches require no polynomial strategy assumptions.
A checked false-claim transition has at most degree many hiding challenges. -/
theorem polynomial_sumcheck_round_count (sample : List K) (distinct : sample.Nodup)
    (degree : Nat) (sent honest : List K→Poly K) (claim truth : List K→K) (history : List K)
    (honestDegree : (honest history).DegLt (degree+1))
    (endpoints : (honest history).eval 0+(honest history).eval 1=truth history) :
    count sample (polynomialSumcheckBad degree sent honest claim truth history)≤degree := by
  classical
  by_cases checked : (sent history).DegLt (degree+1) ∧
      (sent history).eval 0+(sent history).eval 1=claim history ∧ claim history≠truth history
  · have wrong : (sent history).eval 0+(sent history).eval 1≠
        (honest history).eval 0+(honest history).eval 1 := by
      rw [checked.2.1,endpoints]; exact checked.2.2
    have roots:=instruction_round_bad_roots_degree (sent history) (honest history) (degree+1)
      checked.1 honestDegree wrong sample distinct
    have sub : count sample (polynomialSumcheckBad degree sent honest claim truth history)≤
        count sample (fun r=>(sent history).eval r=(honest history).eval r) :=
      count_mono sample (fun _ h=>h.2.2.2)
    omega
  · have empty : count sample (polynomialSumcheckBad degree sent honest claim truth history)=0 := by
      unfold count
      apply List.countP_eq_zero.mpr
      intro r _ h
      have bad := @_root_.of_decide_eq_true _ (Classical.propDecidable _) h
      exact checked ⟨bad.1,bad.2.1,bad.2.2.1⟩
    omega

/-- Without a bad transition a false claim remains false. Consistency is
required only at nonterminal histories actually within the protocol depth. -/
theorem polynomial_sumcheck_false_persists (degree rounds : Nat)
    (sent honest : List K→Poly K) (claim truth : List K→K)
    (step : ∀ h, h.length<rounds → ∀ r,truth (h++[r])=(honest h).eval r)
    (history path : List K) (length : history.length+path.length≤rounds)
    (wrong : claim history≠truth history)
    (checks : polynomialSumcheckChecks degree sent claim history path)
    (good : ¬adaptivePathBad (polynomialSumcheckBad degree sent honest claim truth) history path) :
    claim (history++path)≠truth (history++path) := by
  induction path generalizing history with
  | nil => simpa using wrong
  | cons r rest ih =>
    obtain ⟨bound,endpoints,next,tail⟩:=checks
    have short : history.length<rounds := by simp only [List.length_cons] at length;omega
    have nextWrong : claim (history++[r])≠truth (history++[r]) := by
      intro equal
      apply good
      left
      refine ⟨bound,endpoints,wrong,?_⟩
      rw [←next,←step history short r]
      exact equal
    have remaining:=ih (history++[r]) (by simp only [List.length_append,List.length_singleton,List.length_cons,List.length_nil] at length ⊢;omega)
      nextWrong tail (fun h=>good (Or.inr h))
    simpa only [List.append_assoc,List.singleton_append] using remaining

private theorem depth_bounds (sample : List K) (bad : List K→K→Prop)
    (history : List K) (remaining degree : Nat)
    (localBound : ∀ h : List K,h.length<history.length+remaining → count sample (bad h)≤degree) :
    AdaptiveRoundBounds sample bad history (List.replicate remaining degree) := by
  induction remaining generalizing history with
  | zero => trivial
  | succ n ih =>
    constructor
    · exact localBound history (by omega)
    · intro r _
      apply ih
      intro h hh
      apply localBound h
      simp only [List.length_append,List.length_singleton] at hh
      omega

private theorem tuple_length (sample : List K) (n : Nat) (path : List K)
    (member : path∈uniformTuples sample n) : path.length=n := by
  induction n generalizing path with
  | zero => simp [uniformTuples] at member; subst path; rfl
  | succ n ih =>
    obtain ⟨r,_,hm⟩:=List.mem_flatMap.mp member
    obtain ⟨tail,ht,equal⟩:=List.mem_map.mp hm
    subst path
    simp only [List.length_cons,ih tail ht]

/-- Complete ideal challenge-path bound for adaptive degree-generic messages.
The terminal equality is to the honest value; PCS binding is not assumed
proved. Dividing by |sample|^(rounds+1) gives rounds*degree/|sample|. -/
theorem adaptive_polynomial_sumcheck_count (sample : List K) (distinct : sample.Nodup)
    (degree rounds : Nat) (sent honest : List K→Poly K) (claim truth : List K→K)
    (honestDegree : ∀ h, h.length<rounds → (honest h).DegLt (degree+1))
    (endpoints : ∀ h, h.length<rounds → (honest h).eval 0+(honest h).eval 1=truth h)
    (step : ∀ h, h.length<rounds → ∀ r,truth (h++[r])=(honest h).eval r)
    (wrong : claim []≠truth []) :
    count (uniformTuples sample rounds) (fun path=>polynomialSumcheckChecks degree sent claim [] path ∧
      claim path=truth path)*sample.length≤(degree*rounds)*sample.length^rounds := by
  let bad:=polynomialSumcheckBad degree sent honest claim truth
  have bounds:=depth_bounds sample bad [] rounds degree (by
    intro h hh
    have short : h.length<rounds := by simpa using hh
    exact polynomial_sumcheck_round_count sample distinct degree sent honest claim truth h
      (honestDegree h short) (endpoints h short))
  have total:=adaptive_round_failure_budget sample bad [] (List.replicate rounds degree) bounds
  have replicateSum : ∀ n : Nat,(List.replicate n degree).sum=degree*n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp only [List.replicate_succ,List.sum_cons,ih,Nat.mul_succ];omega
  simp only [List.length_replicate,replicateSum] at total
  have sub : count (uniformTuples sample rounds) (fun path=>polynomialSumcheckChecks degree sent claim [] path ∧
      claim path=truth path)≤count (uniformTuples sample rounds) (adaptivePathBad bad []) := by
    apply count_mono_mem
    intro path hp accepted
    apply Classical.byContradiction
    intro good
    have mismatch:=polynomial_sumcheck_false_persists degree rounds sent honest claim truth step [] path
      (by simp only [List.length_nil,Nat.zero_add,tuple_length sample rounds path hp];omega) wrong accepted.1 good
    exact mismatch accepted.2
  rw [adaptive_failure_leaves_exact] at sub
  have scaled:=Nat.mul_le_mul_right sample.length sub
  exact Nat.le_trans scaled total

def polynomialSumcheckTruth (rounds : Nat) (f : List K→K) (history : List K) : K :=
  whirCubeSum (rounds-history.length) (fun suffix=>f (history++suffix))

/-- Honest endpoint consistency follows from partitioning the actual Boolean
suffix cube; it is not an independently supplied protocol assumption. -/
theorem polynomial_sumcheck_truth_endpoints (rounds : Nat) (f : List K→K)
    (history : List K) (short : history.length<rounds) :
    polynomialSumcheckTruth rounds f (history++[0])+polynomialSumcheckTruth rounds f (history++[1])=
      polynomialSumcheckTruth rounds f history := by
  unfold polynomialSumcheckTruth
  simp only [List.length_append,List.length_singleton]
  have hs : rounds-history.length=(rounds-(history.length+1))+1 := by omega
  conv => rhs; rw [hs,whirCubeSum]
  simp only [List.append_assoc,List.singleton_append]

theorem polynomial_sumcheck_truth_terminal (rounds : Nat) (f : List K→K)
    (path : List K) (length : path.length=rounds) : polynomialSumcheckTruth rounds f path=f path := by
  simp [polynomialSumcheckTruth,length,whirCubeSum]

/-- The adaptive bound for one fixed multivariate evaluator. Honest rounds
must represent its actual remaining Boolean sums and satisfy the degree cap;
terminal authentication is still a separate obligation. -/
theorem adaptive_polynomial_cube_sumcheck_count (sample : List K) (distinct : sample.Nodup)
    (degree rounds : Nat) (f : List K→K) (sent honest : List K→Poly K) (claim : List K→K)
    (honestDegree : ∀ h, h.length<rounds → (honest h).DegLt (degree+1))
    (represents : ∀ h, h.length<rounds → ∀ r,
      (honest h).eval r=polynomialSumcheckTruth rounds f (h++[r]))
    (wrong : claim []≠whirCubeSum rounds f) :
    count (uniformTuples sample rounds) (fun path=>polynomialSumcheckChecks degree sent claim [] path ∧
      claim path=f path)*sample.length≤(degree*rounds)*sample.length^rounds := by
  have bound:=adaptive_polynomial_sumcheck_count sample distinct degree rounds sent honest claim
    (polynomialSumcheckTruth rounds f) honestDegree
    (fun h hh=>by rw [represents h hh 0,represents h hh 1];exact polynomial_sumcheck_truth_endpoints rounds f h hh)
    (fun h hh r=>(represents h hh r).symm)
    (by simpa only [polynomialSumcheckTruth,List.length_nil,Nat.sub_zero,List.nil_append] using wrong)
  have sub : count (uniformTuples sample rounds) (fun path=>polynomialSumcheckChecks degree sent claim [] path ∧ claim path=f path)≤
      count (uniformTuples sample rounds) (fun path=>polynomialSumcheckChecks degree sent claim [] path ∧
        claim path=polynomialSumcheckTruth rounds f path) := by
    apply count_mono_mem
    intro path hp accepted
    rw [polynomial_sumcheck_truth_terminal rounds f path (tuple_length sample rounds path hp)]
    exact accepted
  exact Nat.le_trans (Nat.mul_le_mul_right sample.length sub) bound

end NearCompression
