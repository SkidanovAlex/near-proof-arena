import NearCompression.CheckedHistoryTerminal
import NearCompression.ChronologicalChallengeCount
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Checked acceptance for the literal successive-prefix algebraic IOP. The
query vector is sampled independently AFTER the final state/disclosure. -/
def checkedHistoryAccept (strategy : List K→GeneralFoldTranscript K)
    (sizes degrees : Nat→Nat) (path : List K) (queries : List Nat) : Prop :=
  checkedHistoryTerminalChecks strategy sizes degrees path ∧
  allQueriesPass (generalFoldHistoryQuery strategy sizes path.length path) queries

private theorem indexed_bounds {A : Type} (sample : List A)
    (bad : List A→A→Prop) (error : Nat→Nat) (history : List A) (remaining : Nat)
    (bound : ∀ h : List A,h.length<history.length+remaining → count sample (bad h)≤error h.length) :
    AdaptiveRoundBounds sample bad history ((List.range remaining).map (fun i=>error (history.length+i))) := by
  induction remaining generalizing history with
  | zero => trivial
  | succ n ih =>
    rw [List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,Nat.add_zero]
    constructor
    · exact bound history (by omega)
    · intro a ha
      have next := ih (history++[a]) (by
        intro h hh
        apply bound h
        simp only [List.length_append,List.length_singleton] at hh
        omega)
      simpa [List.length_append,Function.comp_def,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using next

/-- Charge the actual shrinking domain at each round, rather than the largest
round bound repeated throughout the protocol. -/
theorem checked_history_adaptive_escape_sum_budget
    (sample : List K) (distinct : sample.Nodup)
    (strategy : List K→GeneralFoldTranscript K) (N0 T rounds : Nat)
    (sizes degrees : Nat→Nat) (initial : sizes 0=N0)
    (positive : ∀ j≤rounds,0<sizes j)
    (sizeHalves : ∀ j<rounds,sizes j=2*sizes (j+1))
    (degreeHalves : ∀ j<rounds,degrees j=2*degrees (j+1))
    (regime : 2*N0+degrees 0<3*T) (h2 : (2:K)≠0)
    (fixed : ∀ h : List K,h.length<rounds → ∀ r∈sample,
      (strategy (h++[r])).snapshot N0 sizes h.length=(strategy h).snapshot N0 sizes h.length)
    (weights : ∀ h : List K,h.length<rounds → ∀ r∈sample,
      (strategy (h++[r])).weights h.length=(strategy h).weights h.length)
    (claim : ∀ h : List K,h.length<rounds → ∀ r∈sample,
      (strategy (h++[r])).claims h.length=(strategy h).claims h.length)
    (challenge : ∀ h : List K,h.length<rounds → ∀ r∈sample,
      (strategy (h++[r])).challenges h.length=r)
 :
    adaptiveFailureLeaves sample (checkedHistoryEscape strategy N0 T sizes degrees) [] rounds*
      sample.length≤((List.range rounds).map (fun i=>max (sizes (i+1)) 2)).sum*sample.length^rounds := by
  have localBound : ∀ h : List K,h.length<rounds →
      count sample (checkedHistoryEscape strategy N0 T sizes degrees h)≤max (sizes (h.length+1)) 2 := by
    intro h hh
    exact checked_history_escape_bound sample distinct strategy h N0 T sizes degrees
      initial (fun j hj=>positive j (by omega)) (fun j hj=>sizeHalves j (by omega))
      (fun j hj=>degreeHalves j (by omega)) regime h2 (fixed h hh) (weights h hh)
      (claim h hh) (challenge h hh)
  have bounds := indexed_bounds sample (checkedHistoryEscape strategy N0 T sizes degrees)
    (fun i=>max (sizes (i+1)) 2) [] rounds (by simpa using localBound)
  have result := adaptive_round_failure_budget sample (checkedHistoryEscape strategy N0 T sizes degrees)
    [] ((List.range rounds).map (fun i=>max (sizes (i+1)) 2)) (by simpa using bounds)
  simpa using result

/-- Combined adaptive-fold and terminal-query bound for the actual checked
acceptance predicate. For nonempty alphabets this gives
Pr[accept] <= sum_i max(nextSize_i,2)/|sample| + ((T-1)/N0)^q.
Initial doom and prechallenge state bindings are explicit premises, not
conclusions about the executable prover, hash commitments or QROM. -/
theorem checked_history_interactive_acceptance_budget
    (sample : List K) (distinct : sample.Nodup)
    (strategy : List K→GeneralFoldTranscript K) (N0 T rounds q : Nat)
    (sizes degrees : Nat→Nat) (initial : sizes 0=N0)
    (positive : ∀ j≤rounds,0<sizes j)
    (sizeHalves : ∀ j<rounds,sizes j=2*sizes (j+1))
    (degreeHalves : ∀ j<rounds,degrees j=2*degrees (j+1))
    (regime : 2*N0+degrees 0<3*T) (h2 : (2:K)≠0)
    (fixed : ∀ h : List K,h.length<rounds → ∀ r∈sample,
      (strategy (h++[r])).snapshot N0 sizes h.length=(strategy h).snapshot N0 sizes h.length)
    (weights : ∀ h : List K,h.length<rounds → ∀ r∈sample,
      (strategy (h++[r])).weights h.length=(strategy h).weights h.length)
    (claim : ∀ h : List K,h.length<rounds → ∀ r∈sample,
      (strategy (h++[r])).claims h.length=(strategy h).claims h.length)
    (challenge : ∀ h : List K,h.length<rounds → ∀ r∈sample,
      (strategy (h++[r])).challenges h.length=r)
    (noInitial : ¬indexedChainCandidate N0 sizes degrees (strategy []).roots
      (strategy []).challenges (strategy []).oracles (strategy []).weights
      (strategy []).claims T 0) :
    count ((uniformTuples sample rounds).flatMap (fun path=>
      (uniformTuples (List.range N0) q).map (fun queries=>(path,queries))))
      (fun pair=>checkedHistoryAccept strategy sizes degrees pair.1 pair.2)*sample.length≤
      ((List.range rounds).map (fun i=>max (sizes (i+1)) 2)).sum*sample.length^rounds*N0^q+sample.length^(rounds+1)*(T-1)^q := by
  have escape := checked_history_adaptive_escape_sum_budget sample distinct strategy N0 T rounds
    sizes degrees initial positive sizeHalves degreeHalves regime h2
    fixed weights claim challenge
  have joint := finite_product_acceptance_budget (uniformTuples sample rounds)
    (uniformTuples (List.range N0) q) (checkedHistoryAccept strategy sizes degrees)
    (adaptivePathBad (checkedHistoryEscape strategy N0 T sizes degrees) [])
    sample.length ((T-1)^q*sample.length) (by
      intro path hp good
      have len := uniform_tuple_member_length sample rounds path hp
      have terminal := checked_history_terminal_acceptance_budget strategy N0 T q sizes degrees path
        (fun j hj=>positive j (by omega)) (fun j hj=>sizeHalves j (by omega)) noInitial good
      exact Nat.mul_le_mul_right sample.length terminal)
  rw [adaptive_failure_leaves_exact,uniform_tuples_length,uniform_tuples_length,List.length_range] at joint
  have scaled := Nat.mul_le_mul_right (N0^q) escape
  calc
    _ ≤ _ := joint
    _ ≤ ((List.range rounds).map (fun i=>max (sizes (i+1)) 2)).sum*sample.length^rounds*N0^q+sample.length^(rounds+1)*(T-1)^q := by
      simp only [Nat.pow_succ]
      grind

end NearCompression
