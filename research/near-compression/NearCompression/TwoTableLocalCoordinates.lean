import NearCompression.GKRFullPCSExperiment
namespace NearCompression
open Lean.Grind ArenaCore.Security ZkFormal.Algebra

/-- The literal slice has two tables. This identity retains both complete
local challenge prefixes while regrouping their independent ideal draws.
It exchanges counting sums, not the order in which messages are sent. -/
theorem two_table_local_regroup {K R : Type} [Field K]
    (sample : List K) (firstRows secondRows : Nat) (continuations : List R)
    (event : LocalChallengePrefix K → LocalChallengePrefix K → R → Prop) :
    count ((decodedLocalPrefixes sample firstRows).flatMap (fun p =>
      (decodedLocalPrefixes sample secondRows).flatMap (fun q =>
        continuations.map (fun r => (p,q,r))))) (fun x => event x.1 x.2.1 x.2.2)=
    count ((airLocalInitialChallenges sample firstRows).flatMap (fun first =>
      (airLocalInitialChallenges sample secondRows).flatMap (fun second =>
        (uniformTuples sample firstRows).flatMap (fun left =>
          (uniformTuples sample secondRows).flatMap (fun right =>
            continuations.map (fun r => ((first,left),(second,right),r)))))))
      (fun x => event x.1 x.2.1 x.2.2) := by
  classical
  simp only [decodedLocalPrefixes,List.flatMap_assoc,List.flatMap_map]
  simp only [count,List.countP_flatMap,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro first _
  have exchange := gkr_finite_sample_exchange (uniformTuples sample firstRows)
    (airLocalInitialChallenges sample secondRows)
    (fun left second => (uniformTuples sample secondRows).flatMap (fun right =>
      continuations.map (fun r => ((first,left),(second,right),r))))
    (fun x => event x.1 x.2.1 x.2.2)
  simpa only [count,List.countP_flatMap,Function.comp_def] using exchange

/-- Both table row paths become one joint vector, with the same take/drop
partition used by chronological metadata offsets. All other randomness and
continuations remain in the event, so adaptive messages are not discarded. -/
theorem two_table_local_joint_coordinates {K R : Type} [Field K]
    (sample : List K) (firstRows secondRows : Nat) (continuations : List R)
    (event : LocalChallengePrefix K → LocalChallengePrefix K → R → Prop) :
    count ((decodedLocalPrefixes sample firstRows).flatMap (fun p =>
      (decodedLocalPrefixes sample secondRows).flatMap (fun q =>
        continuations.map (fun r => (p,q,r))))) (fun x => event x.1 x.2.1 x.2.2)=
    count ((airLocalInitialChallenges sample firstRows).flatMap (fun first =>
      (airLocalInitialChallenges sample secondRows).flatMap (fun second =>
        (uniformTuples sample (firstRows+secondRows)).flatMap (fun rows =>
          continuations.map (fun r => ((first,rows.take firstRows),(second,rows.drop firstRows),r))))))
      (fun x => event x.1 x.2.1 x.2.2) := by
  classical
  rw [two_table_local_regroup,uniform_tuples_append]
  simp only [List.flatMap_assoc,List.flatMap_map,count,List.countP_flatMap,List.countP_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro first _
  congr 1
  apply List.map_congr_left
  intro second _
  congr 1
  apply List.map_congr_left
  intro left hl
  have length := uniform_tuple_member_length sample firstRows left hl
  simp only [←length,List.take_append_length,List.drop_append_length]

private theorem uniform_sum_budget {A : Type} (xs : List A) (f : A → Nat) (scale budget : Nat)
    (each : ∀ x∈xs,f x*scale≤budget) : (xs.map f).sum*scale≤xs.length*budget := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have head := each x (by simp)
    have tail := ih (fun y hy => each y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul]
    omega

/-- A joint rowpoint bound for every pair of initial mixing/weighting draws
lifts to the chronological two-table experiment. It pays the exact initial
sample mass and never assumes a bound after fixing either table's rowpoint. -/
theorem two_table_local_joint_budget {K R : Type} [Field K]
    (sample : List K) (firstRows secondRows : Nat) (continuations : List R)
    (event : LocalChallengePrefix K → LocalChallengePrefix K → R → Prop)
    (scale budget : Nat)
    (joint : ∀ first∈airLocalInitialChallenges sample firstRows,
      ∀ second∈airLocalInitialChallenges sample secondRows,
      count ((uniformTuples sample (firstRows+secondRows)).flatMap (fun rows =>
        continuations.map (fun r => (rows,r))))
        (fun x => event (first,x.1.take firstRows) (second,x.1.drop firstRows) x.2)*scale≤budget) :
    count ((decodedLocalPrefixes sample firstRows).flatMap (fun p =>
      (decodedLocalPrefixes sample secondRows).flatMap (fun q =>
        continuations.map (fun r => (p,q,r))))) (fun x => event x.1 x.2.1 x.2.2)*scale≤
    (airLocalInitialChallenges sample firstRows).length*
      ((airLocalInitialChallenges sample secondRows).length*budget) := by
  classical
  rw [two_table_local_joint_coordinates]
  simp only [count,List.countP_flatMap,List.countP_map,Function.comp_def] at joint ⊢
  apply uniform_sum_budget
  intro first hf
  exact uniform_sum_budget _ _ scale budget (joint first hf)

end NearCompression
