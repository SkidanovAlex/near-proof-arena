import NearCompression.GKRRoundState
import NearCompression.AdaptiveWeightedSumcheck

/-! Adaptive ideal counting for actual indexed GKR bit rounds. The starting
values and terms are fixed before the challenge path; messages may depend on
past challenges only. Axis reset and complete layer wiring are separate. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def gkrRoundStateFinal (values : Nat → K) (terms : List (GKRIndexedTerm K)) :
    List K → (Nat → K) × List (GKRIndexedTerm K)
  | [] => (values,terms)
  | r::rest => gkrRoundStateFinal (gkrFoldInput values r) (terms.map (gkrAdvanceTerm r)) rest

theorem gkr_round_state_final_append (values : Nat → K) (terms : List (GKRIndexedTerm K))
    (history tail : List K) :
    gkrRoundStateFinal values terms (history++tail)=
      gkrRoundStateFinal (gkrRoundStateFinal values terms history).1
        (gkrRoundStateFinal values terms history).2 tail := by
  induction history generalizing values terms with
  | nil => rfl
  | cons r rs ih => exact ih (gkrFoldInput values r) (terms.map (gkrAdvanceTerm r))

noncomputable def gkrAdaptiveRoundBad (values : Nat → K) (terms : List (GKRIndexedTerm K))
    (sent : List K → Poly K) (claim : List K → K) (history : List K) (r : K) : Prop :=
  let state := gkrRoundStateFinal values terms history
  (sent history).DegLt 3 ∧
  (sent history).eval 0+(sent history).eval 1=claim history ∧
  claim history≠gkrStateClaim state.1 state.2 ∧
  (sent history).eval r=(gkrStatePolynomial state.1 state.2).eval r

/-- The actual folded state constructs its own honest degree-two polynomial. -/
theorem gkr_adaptive_round_count (sample : List K) (distinct : sample.Nodup)
    (values : Nat → K) (terms : List (GKRIndexedTerm K))
    (sent : List K → Poly K) (claim : List K → K) (history : List K) :
    count sample (gkrAdaptiveRoundBad values terms sent claim history)≤2 := by
  classical
  let state := gkrRoundStateFinal values terms history
  by_cases checked : (sent history).DegLt 3 ∧
      (sent history).eval 0+(sent history).eval 1=claim history ∧
      claim history≠gkrStateClaim state.1 state.2
  · have roots := gkr_state_bad_count state.1 state.2 (sent history) (claim history)
      checked.1 checked.2.1 checked.2.2 sample distinct
    have subset : count sample (gkrAdaptiveRoundBad values terms sent claim history)≤
        count sample (fun r => (sent history).eval r=
          gkrStateClaim (gkrFoldInput state.1 r) (state.2.map (gkrAdvanceTerm r))) := by
      apply count_mono
      intro r h
      rw [gkr_state_advance]
      exact h.2.2.2
    omega
  · have empty : count sample (gkrAdaptiveRoundBad values terms sent claim history)=0 := by
      unfold count
      apply List.countP_eq_zero.mpr
      intro r hr
      intro h
      have bad := @_root_.of_decide_eq_true _ (Classical.propDecidable _) h
      exact checked ⟨bad.1,bad.2.1,bad.2.2.1⟩
    omega

/-- Checked false claims persist outside explicit first-repair events. -/
theorem gkr_adaptive_false_persists (values : Nat → K) (terms : List (GKRIndexedTerm K))
    (sent : List K → Poly K) (claim : List K → K) (history path : List K)
    (wrong : claim history≠gkrStateClaim (gkrRoundStateFinal values terms history).1
      (gkrRoundStateFinal values terms history).2)
    (checks : weightedSumcheckChecks sent claim history path)
    (good : ¬adaptivePathBad (gkrAdaptiveRoundBad values terms sent claim) history path) :
    claim (history++path)≠gkrStateClaim (gkrRoundStateFinal values terms (history++path)).1
      (gkrRoundStateFinal values terms (history++path)).2 := by
  induction path generalizing history with
  | nil => simpa using wrong
  | cons r rest ih =>
    obtain ⟨degree,endpoints,next,tail⟩ := checks
    have nextWrong : claim (history++[r])≠
        gkrStateClaim (gkrRoundStateFinal values terms (history++[r])).1
          (gkrRoundStateFinal values terms (history++[r])).2 := by
      intro equal
      apply good
      left
      refine ⟨degree,endpoints,wrong,?_⟩
      rw [←next,←gkr_state_advance]
      simpa only [gkr_round_state_final_append,gkrRoundStateFinal] using equal
    have remaining := ih (history++[r]) nextWrong tail (fun h => good (Or.inr h))
    simpa only [List.append_assoc,List.singleton_append] using remaining

omit [Field K] in
private theorem uniform_round_bounds (sample : List K) (bad : List K → K → Prop)
    (localBound : ∀ h,count sample (bad h)≤2) (history : List K) (remaining : Nat) :
    AdaptiveRoundBounds sample bad history (List.replicate remaining 2) := by
  induction remaining generalizing history with
  | zero => trivial
  | succ n ih => exact ⟨localBound history,fun r _ => ih (history++[r])⟩

/-- Ideal adaptive path bound for indexed bit rounds. Invalid messages need
satisfy no hypotheses: acceptance includes degree, endpoint and claim updates.
This is not yet a complete GKR layer or Fiat-Shamir theorem. -/
theorem gkr_adaptive_rounds_count (sample : List K) (distinct : sample.Nodup)
    (values : Nat → K) (terms : List (GKRIndexedTerm K))
    (sent : List K → Poly K) (claim : List K → K) (rounds : Nat)
    (wrong : claim []≠gkrStateClaim values terms) :
    count (uniformTuples sample rounds) (fun path => weightedSumcheckChecks sent claim [] path ∧
      claim path=gkrStateClaim (gkrRoundStateFinal values terms path).1
        (gkrRoundStateFinal values terms path).2)*sample.length≤
      (2*rounds)*sample.length^rounds := by
  let bad := gkrAdaptiveRoundBad values terms sent claim
  have bounds := uniform_round_bounds sample bad
    (gkr_adaptive_round_count sample distinct values terms sent claim) [] rounds
  have total := adaptive_round_failure_budget sample bad [] (List.replicate rounds 2) bounds
  have replicateSum : ∀ n : Nat,(List.replicate n 2).sum=2*n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp only [List.replicate_succ,List.sum_cons,ih];omega
  simp only [List.length_replicate,replicateSum] at total
  have subset : count (uniformTuples sample rounds) (fun path => weightedSumcheckChecks sent claim [] path ∧
      claim path=gkrStateClaim (gkrRoundStateFinal values terms path).1
        (gkrRoundStateFinal values terms path).2)≤
      count (uniformTuples sample rounds) (adaptivePathBad bad []) := by
    apply count_mono
    intro path accepted
    apply Classical.byContradiction
    intro good
    have mismatch := gkr_adaptive_false_persists values terms sent claim [] path wrong accepted.1 good
    exact mismatch accepted.2
  rw [adaptive_failure_leaves_exact] at subset
  have scaled := Nat.mul_le_mul_right sample.length subset
  exact Nat.le_trans scaled total
/-- Union bound for all indexed-round repair events, independent of whether
an initial claim is wrong. This is the reusable conditional budget for an axis. -/
theorem gkr_adaptive_bad_paths_count (sample : List K) (distinct : sample.Nodup)
    (values : Nat → K) (terms : List (GKRIndexedTerm K))
    (sent : List K → Poly K) (claim : List K → K) (rounds : Nat) :
    count (uniformTuples sample rounds)
      (adaptivePathBad (gkrAdaptiveRoundBad values terms sent claim) [])*sample.length≤
      (2*rounds)*sample.length^rounds := by
  have bounds := uniform_round_bounds sample (gkrAdaptiveRoundBad values terms sent claim)
    (gkr_adaptive_round_count sample distinct values terms sent claim) [] rounds
  have total := adaptive_round_failure_budget sample (gkrAdaptiveRoundBad values terms sent claim)
    [] (List.replicate rounds 2) bounds
  have sum : ∀ n : Nat,(List.replicate n 2).sum=2*n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp only [List.replicate_succ,List.sum_cons,ih];omega
  rw [List.length_replicate,sum rounds,←adaptive_failure_leaves_exact] at total
  exact total
end NearCompression
