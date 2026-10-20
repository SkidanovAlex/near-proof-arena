import NearCompression.AdaptiveRoundBudget
import NearCompression.GlobalChainMass

/-! Exact Cartesian sample counts for independent uniform draws WITH
replacement. No Fiat--Shamir, random-oracle, or concentration theorem. -/
namespace NearCompression
open Lean.Grind ArenaCore.Security

def uniformTuples {A : Type} (sample : List A) : Nat → List (List A)
  | 0 => [[]]
  | n+1 => sample.flatMap (fun a => (uniformTuples sample n).map (a::·))

def allQueriesPass {A : Type} (pass : A → Prop) (queries : List A) : Prop :=
  ∀ a∈queries,pass a

private theorem map_sum_const {A : Type} (xs : List A) (k : Nat) :
    (xs.map (fun _ => k)).sum=xs.length*k := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih]; grind

private theorem map_sum_event {A : Type} (xs : List A) (event : A → Prop) [DecidablePred event] (k : Nat) :
    (xs.map (fun x => if event x then k else 0)).sum=count xs event*k := by
  classical
  induction xs with
  | nil => simp [count]
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,count,List.countP_cons] at ih ⊢
    by_cases h : event x <;> simp_all <;> grind

theorem uniform_tuples_length {A : Type} (sample : List A) (n : Nat) :
    (uniformTuples sample n).length=sample.length^n := by
  induction n with
  | zero => simp [uniformTuples]
  | succ n ih =>
    simp only [uniformTuples,List.length_flatMap,List.length_map,ih]
    rw [map_sum_const,Nat.pow_succ]
    exact Nat.mul_comm _ _

private theorem count_cons_queries {A : Type} (tails : List (List A)) (a : A) (pass : A → Prop) [DecidablePred pass] :
    count (tails.map (a::·)) (allQueriesPass pass)=
      if pass a then count tails (allQueriesPass pass) else 0 := by
  classical
  unfold count
  rw [List.countP_map]
  by_cases h : pass a
  · simp [Function.comp_def,allQueriesPass,h]
    congr 1
    funext xs
    exact decide_eq_decide.mpr Iff.rfl
  · simp [Function.comp_def,allQueriesPass,h]

/-- Exact count, including repeated seeds, q=0, and an empty alphabet. -/
theorem independent_query_count {A : Type} (sample : List A) (pass : A → Prop) (q : Nat) :
    count (uniformTuples sample q) (allQueriesPass pass)=(count sample pass)^q := by
  classical
  induction q with
  | zero => simp [uniformTuples,count,allQueriesPass]
  | succ q ih =>
    change count (sample.flatMap (fun a => (uniformTuples sample q).map (a::·))) _=_
    simp only [count,List.countP_flatMap]
    change (sample.map (fun a => count ((uniformTuples sample q).map (a::·)) (allQueriesPass pass))).sum=_
    simp only [count_cons_queries,ih]
    rw [map_sum_event,Nat.pow_succ]
    exact Nat.mul_comm _ _

def adaptivePathBad {A : Type} (bad : List A → A → Prop) : List A → List A → Prop
  | _,[] => False
  | history,a::rest => bad history a ∨ adaptivePathBad bad (history++[a]) rest

private theorem count_cons_bad {A : Type} (tails : List (List A))
    (bad : List A → A → Prop) (history : List A) (a : A) [DecidablePred (bad history)] :
    count (tails.map (a::·)) (adaptivePathBad bad history)=
      if bad history a then tails.length else count tails (adaptivePathBad bad (history++[a])) := by
  classical
  unfold count
  rw [List.countP_map]
  by_cases h : bad history a <;> simp [Function.comp_def,adaptivePathBad,h]

/-- The adaptive recurrence counts the actual bad transcript paths. -/
theorem adaptive_failure_leaves_exact {A : Type} (sample : List A)
    (bad : List A → A → Prop) (history : List A) (n : Nat) :
    count (uniformTuples sample n) (adaptivePathBad bad history)=
      adaptiveFailureLeaves sample bad history n := by
  classical
  induction n generalizing history with
  | zero =>
    have h : ¬adaptivePathBad bad history [] := fun h => h
    change count [[]] (adaptivePathBad bad history)=0
    simp only [count,List.countP_cons,List.countP_nil,Nat.add_zero,
      decide_eq_false h,Bool.false_eq_true,ite_false]
  | succ n ih =>
    change count (sample.flatMap (fun a => (uniformTuples sample n).map (a::·))) _=_
    simp only [count,List.countP_flatMap]
    change (sample.map (fun a => count ((uniformTuples sample n).map (a::·))
      (adaptivePathBad bad history))).sum=_
    simp only [count_cons_bad,uniform_tuples_length,ih]
    rfl

private theorem conditional_query_sum {A B : Type} (paths : List A) (queries : List B)
    (bad : A → Prop) (accept : A → B → Prop) (limit : Nat)
    (good : ∀ path∈paths,¬bad path → count queries (accept path)≤limit) :
    (paths.map (fun path => count queries (accept path))).sum ≤
      count paths bad*queries.length+paths.length*limit := by
  classical
  induction paths with
  | nil => simp [count]
  | cons path paths ih =>
    have tail := ih (fun t ht => good t (by simp [ht]))
    have head := good path (by simp)
    have maximum : count queries (accept path)≤queries.length := List.countP_le_length
    simp only [List.map_cons,List.sum_cons,count,List.countP_cons,List.length_cons] at tail head maximum ⊢
    by_cases h : bad path <;> simp_all <;> grind

/-- Total accepted pairs of challenge transcript paths and subsequent query
vectors. The sum is the exact count of the corresponding Cartesian experiment. -/
noncomputable def interactiveAcceptedCount {A B : Type} (challenges : List A)
    (queries : List B) (history : List A) (rounds q : Nat)
    (pass : List A → B → Prop) : Nat :=
  ((uniformTuples challenges rounds).map (fun path =>
    count (uniformTuples queries q) (allQueriesPass (pass (history++path))))).sum

theorem interactive_accepted_cartesian {A B : Type} (challenges : List A)
    (queries : List B) (history : List A) (rounds q : Nat) (pass : List A → B → Prop) :
    count ((uniformTuples challenges rounds).flatMap (fun path =>
      (uniformTuples queries q).map (fun qs => (path,qs))))
      (fun pair => allQueriesPass (pass (history++pair.1)) pair.2)=
      interactiveAcceptedCount challenges queries history rounds q pass := by
  classical
  simp only [count,List.countP_flatMap,List.countP_map,Function.comp_def,interactiveAcceptedCount]

/-- Combined interactive bound without division:
accepted*|S| <= sum(errors)*|S|^n*|Q|^q + |S|^(n+1)*B^q.
Dividing by |S| times the experiment size |S|^n*|Q|^q gives the usual
probability bound sum(errors)/|S| + (B/|Q|)^q for nonempty alphabets. -/
theorem interactive_round_query_budget {A B : Type}
    (challenges : List A) (queries : List B) (bad : List A → A → Prop)
    (history : List A) (errors : List Nat) (q limit : Nat) (pass : List A → B → Prop)
    (roundBounds : AdaptiveRoundBounds challenges bad history errors)
    (goodQueries : ∀ path∈uniformTuples challenges errors.length,
      ¬adaptivePathBad bad history path → count queries (pass (history++path))≤limit) :
    interactiveAcceptedCount challenges queries history errors.length q pass*challenges.length ≤
      errors.sum*challenges.length^errors.length*queries.length^q+
        challenges.length^(errors.length+1)*limit^q := by
  have localBound : ∀ path∈uniformTuples challenges errors.length,
      ¬adaptivePathBad bad history path →
      count (uniformTuples queries q) (allQueriesPass (pass (history++path)))≤limit^q := by
    intro path hp good
    rw [independent_query_count]
    exact Nat.pow_le_pow_left (goodQueries path hp good) q
  have total := conditional_query_sum (uniformTuples challenges errors.length) (uniformTuples queries q)
    (adaptivePathBad bad history) (fun path => allQueriesPass (pass (history++path))) (limit^q) localBound
  rw [adaptive_failure_leaves_exact,uniform_tuples_length,uniform_tuples_length] at total
  have scaled := Nat.mul_le_mul_right challenges.length total
  have round := adaptive_round_failure_budget challenges bad history errors roundBounds
  have rounded := Nat.mul_le_mul_right (queries.length^q) round
  change interactiveAcceptedCount challenges queries history errors.length q pass ≤ _ at total
  simp only [Nat.pow_succ]
  unfold interactiveAcceptedCount
  grind

/-- The actual modulo-chain verifier supplies the per-seed predicate directly. -/
theorem global_chain_repeated_query_count (N0 q stage : Nat) (sizes : Nat → Nat)
    (check : Nat → Nat → Prop) :
    count (uniformTuples (List.range N0) q)
      (allQueriesPass (globalChainPass sizes check stage))=
      (count (List.range N0) (globalChainPass sizes check stage))^q :=
  independent_query_count _ _ _

end NearCompression
