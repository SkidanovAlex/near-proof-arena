import NearCompression.RepeatedAffineFold
import NearCompression.IndependentQueryBudget

/-! Adaptive quadratic sumcheck for the executable coefficient/weight pair
fold. Both honest coordinates fold; degree and endpoint checks reject malformed
messages. The initial honest vector is fixed before all challenges. This is an
ideal finite counting theorem, not a source commitment or QROM assertion. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def pairFoldPolynomial (xs : List (K×K)) : Poly K :=
  let q := affineFoldQuadratic xs
  Poly.mk [q.c0,q.c1,q.c2]

theorem pair_fold_polynomial_degree (xs : List (K×K)) : (pairFoldPolynomial xs).DegLt 3 :=
  Poly.degLt_length _

theorem pair_fold_polynomial_eval (xs : List (K×K)) (r : K) :
    (pairFoldPolynomial xs).eval r=affineFoldDot (affineFoldVector r xs) := by
  have h := affine_fold_quadratic_eval r xs
  simp only [pairFoldPolynomial,Poly.eval,Poly.evalL,WhirQuadratic.eval] at h ⊢
  grind

theorem pair_fold_polynomial_endpoints (xs : List (K×K)) (even : xs.length%2=0) :
    (pairFoldPolynomial xs).eval 0+(pairFoldPolynomial xs).eval 1=affineFoldDot xs := by
  have h := affine_fold_quadratic_endpoints xs even
  simp only [pairFoldPolynomial,Poly.eval,Poly.evalL,WhirQuadratic.endpoints,WhirQuadratic.eval] at h ⊢
  grind

theorem affine_fold_final_append (xs : List (K×K)) (history tail : List K) :
    affineFoldFinal xs (history++tail)=affineFoldFinal (affineFoldFinal xs history) tail := by
  induction history generalizing xs with
  | nil => rfl
  | cons r rs ih => exact ih (affineFoldVector r xs)

theorem affine_fold_prefix_shape (history : List K) (xs : List (K×K)) (rounds lanes : Nat)
    (length : history.length≤rounds) (shape : xs.length=lanes*2^rounds) :
    (affineFoldFinal xs history).length=lanes*2^(rounds-history.length) := by
  induction history generalizing xs rounds with
  | nil => simpa [affineFoldFinal] using shape
  | cons r rs ih =>
    cases rounds with
    | zero => simp at length
    | succ rounds =>
      have next := affine_fold_next_shape xs r rounds lanes shape
      have h := ih (affineFoldVector r xs) rounds (by simpa using length) next
      simpa only [affineFoldFinal,List.length_cons,Nat.add_sub_add_right] using h

noncomputable def weightedSumcheckBad (xs : List (K×K))
    (sent : List K → Poly K) (claim : List K → K) (history : List K) (r : K) : Prop :=
  (sent history).DegLt 3 ∧
  (sent history).eval 0+(sent history).eval 1=claim history ∧
  claim history≠affineFoldDot (affineFoldFinal xs history) ∧
  (sent history).eval r=(pairFoldPolynomial (affineFoldFinal xs history)).eval r

def weightedSumcheckChecks (sent : List K → Poly K) (claim : List K → K) : List K → List K → Prop
  | _,[] => True
  | history,r::rest =>
    (sent history).DegLt 3 ∧
    (sent history).eval 0+(sent history).eval 1=claim history ∧
    claim (history++[r])=(sent history).eval r ∧
    weightedSumcheckChecks sent claim (history++[r]) rest

/-- Each checked false-claim transition has at most two successful challenges;
the honest polynomial and its degree/endpoints are constructed from xs. -/
theorem weighted_sumcheck_round_count (sample : List K) (distinct : sample.Nodup)
    (xs : List (K×K)) (sent : List K → Poly K) (claim : List K → K)
    (history : List K) (rounds lanes : Nat) (short : history.length<rounds)
    (shape : xs.length=lanes*2^rounds) :
    count sample (weightedSumcheckBad xs sent claim history)≤2 := by
  classical
  have length := affine_fold_prefix_shape history xs rounds lanes (by omega) shape
  have even : (affineFoldFinal xs history).length%2=0 := by
    rw [length]
    have diff : rounds-history.length=(rounds-history.length-1)+1 := by omega
    rw [diff,Nat.pow_succ]
    simp [←Nat.mul_assoc]
  by_cases checked : (sent history).DegLt 3 ∧
      (sent history).eval 0+(sent history).eval 1=claim history ∧
      claim history≠affineFoldDot (affineFoldFinal xs history)
  · have wrong : (sent history).eval 0+(sent history).eval 1≠
        (pairFoldPolynomial (affineFoldFinal xs history)).eval 0+
          (pairFoldPolynomial (affineFoldFinal xs history)).eval 1 := by
      rw [checked.2.1,pair_fold_polynomial_endpoints _ even]
      exact checked.2.2
    have bound := instruction_round_bad_roots_degree (sent history)
      (pairFoldPolynomial (affineFoldFinal xs history)) 3 checked.1
      (pair_fold_polynomial_degree _) wrong sample distinct
    have subset : count sample (weightedSumcheckBad xs sent claim history)≤
        count sample (fun r => (sent history).eval r=(pairFoldPolynomial (affineFoldFinal xs history)).eval r) := by
      apply count_mono
      intro r h
      exact h.2.2.2
    omega
  · have empty : count sample (weightedSumcheckBad xs sent claim history)=0 := by
      unfold count
      apply List.countP_eq_zero.mpr
      intro r hr
      intro h
      have bad := @_root_.of_decide_eq_true _ (Classical.propDecidable _) h
      exact checked ⟨bad.1,bad.2.1,bad.2.2.1⟩
    omega

/-- Outside the explicit round bad events a false claim stays false through
all checked rounds, even for adaptive message strategies. -/
theorem weighted_sumcheck_false_persists (xs : List (K×K))
    (sent : List K → Poly K) (claim : List K → K) (history path : List K)
    (wrong : claim history≠affineFoldDot (affineFoldFinal xs history))
    (checks : weightedSumcheckChecks sent claim history path)
    (good : ¬adaptivePathBad (weightedSumcheckBad xs sent claim) history path) :
    claim (history++path)≠affineFoldDot (affineFoldFinal xs (history++path)) := by
  induction path generalizing history with
  | nil => simpa using wrong
  | cons r rest ih =>
    obtain ⟨degree,endpoints,next,tail⟩ := checks
    have nextWrong : claim (history++[r])≠affineFoldDot (affineFoldFinal xs (history++[r])) := by
      intro equal
      apply good
      left
      refine ⟨degree,endpoints,wrong,?_⟩
      rw [←next,pair_fold_polynomial_eval]
      simpa only [affine_fold_final_append,affineFoldFinal] using equal
    have remaining := ih (history++[r]) nextWrong tail (fun h => good (Or.inr h))
    simpa only [List.append_assoc,List.singleton_append] using remaining

omit [Field K] in
private theorem bounds_at_depth (sample : List K) (bad : List K → K → Prop)
    (history : List K) (remaining : Nat)
    (localBound : ∀ h : List K,h.length<history.length+remaining → count sample (bad h)≤2) :
    AdaptiveRoundBounds sample bad history (List.replicate remaining 2) := by
  induction remaining generalizing history with
  | zero => trivial
  | succ n ih =>
    constructor
    · exact localBound history (by omega)
    · intro r hr
      apply ih
      intro h hh
      apply localBound h
      simp only [List.length_append,List.length_singleton] at hh
      omega

/-- Exact ideal challenge-path bound. Acceptance requires checked messages;
invalid/aborting branches need satisfy no degree or endpoint assumptions.
The terminal equality is the event of concealing a false initial dot claim. -/
theorem adaptive_weighted_sumcheck_count (sample : List K) (distinct : sample.Nodup)
    (xs : List (K×K)) (sent : List K → Poly K) (claim : List K → K)
    (rounds lanes : Nat) (shape : xs.length=lanes*2^rounds)
    (wrong : claim []≠affineFoldDot xs) :
    count (uniformTuples sample rounds) (fun path => weightedSumcheckChecks sent claim [] path ∧
      claim path=affineFoldDot (affineFoldFinal xs path))*sample.length≤
      (2*rounds)*sample.length^rounds := by
  let bad := weightedSumcheckBad xs sent claim
  have bounds := bounds_at_depth sample bad [] rounds (by
    intro h hh
    exact weighted_sumcheck_round_count sample distinct xs sent claim h rounds lanes (by simpa using hh) shape)
  have total := adaptive_round_failure_budget sample bad [] (List.replicate rounds 2) bounds
  have replicateSum : ∀ n : Nat,(List.replicate n 2).sum=2*n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp only [List.replicate_succ,List.sum_cons,ih]; omega
  simp only [List.length_replicate,replicateSum] at total
  have subset : count (uniformTuples sample rounds) (fun path => weightedSumcheckChecks sent claim [] path ∧
        claim path=affineFoldDot (affineFoldFinal xs path))≤
      count (uniformTuples sample rounds) (adaptivePathBad bad []) := by
    apply count_mono
    intro path accepted
    apply Classical.byContradiction
    intro good
    have mismatch := weighted_sumcheck_false_persists xs sent claim [] path wrong accepted.1 good
    exact mismatch accepted.2
  rw [adaptive_failure_leaves_exact] at subset
  have scaled := Nat.mul_le_mul_right sample.length subset
  have result := Nat.le_trans scaled total
  simpa [Nat.mul_comm] using result

end NearCompression
