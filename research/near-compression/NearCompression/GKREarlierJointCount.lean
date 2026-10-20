import NearCompression.GKRJointTerminalEvent
namespace NearCompression
open ArenaCore.Security

private theorem sum_add_map {A : Type} (xs : List A) (f g : A → Nat) :
    (xs.map (fun a => f a+g a)).sum=(xs.map f).sum+(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.map_cons,List.sum_cons,ih];omega

private theorem sum_exchange {A B : Type} (xs : List A) (ys : List B) (f : A → B → Nat) :
    (xs.map (fun a => (ys.map (f a)).sum)).sum=
      (ys.map (fun b => (xs.map (fun a => f a b)).sum)).sum := by
  induction xs with
  | nil =>
    simp only [List.map_nil,List.sum_nil]
    induction ys with
    | nil => rfl
    | cons b ys ih => simpa using ih
  | cons a xs ih =>
    simp only [List.map_cons,List.sum_cons,ih]
    rw [sum_add_map]

/-- Reorder finite sampling sums without changing any event or its adaptive
message dependencies. This is not permission to reorder protocol messages. -/
theorem gkr_finite_sample_exchange {A B C : Type} (xs : List A) (ys : List B)
    (continuation : A → B → List C) (event : C → Prop) :
    count (xs.flatMap (fun a => ys.flatMap (continuation a))) event=
      count (ys.flatMap (fun b => xs.flatMap (fun a => continuation a b))) event := by
  classical
  simp only [count,List.countP_flatMap,Function.comp_def]
  exact sum_exchange xs ys _

/-- Earlier GKR blocks can be fixed as a counting fiber while rowpoints,
final GKR coordinates and PCS point remain jointly sampled. Each predicate
retains the full earlier block sequence; no causal restriction is removed. -/
theorem gkr_earlier_joint_event_count {K R : Type} (sample : List K) (layout : GKRJointLayout)
    (earlierRounds : List Nat) (continuations : List R)
    (event : List (GKRBlock K) → List K → R → Prop) :
    count ((uniformTuples sample layout.rowCoordinates).flatMap (fun rows =>
      (gkrChallengePaths sample earlierRounds).flatMap (fun earlier =>
        (gkrChallengeBlocks sample layout.inputLog).flatMap (fun block =>
          (uniformTuples sample layout.commonLog).flatMap (fun z =>
            continuations.map (fun r => (earlier,(rows++gkrBlockCoordinates block)++z,r)))))))
      (fun item => event item.1 item.2.1 item.2.2)=
    ((gkrChallengePaths sample earlierRounds).map (fun earlier =>
      count ((uniformTuples sample (heterogeneousJointDimension layout)).flatMap
        (fun z => continuations.map (fun r => (z,r)))) (fun pair => event earlier pair.1 pair.2))).sum := by
  rw [gkr_finite_sample_exchange]
  classical
  simp only [count,List.countP_flatMap,List.countP_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro earlier _
  have exactCount := gkr_rows_block_pcs_event_count sample layout continuations (event earlier)
  simpa only [count,List.countP_flatMap,List.countP_map,Function.comp_def] using exactCount

/-- A PCS joint-event bound valid for every earlier GKR sequence lifts to the
full experiment, paying its exact sampling mass. Rowpoints are not fixed. -/
theorem gkr_earlier_joint_event_budget {K R : Type} (sample : List K) (layout : GKRJointLayout)
    (earlierRounds : List Nat) (continuations : List R)
    (event : List (GKRBlock K) → List K → R → Prop) (scale budget : Nat)
    (joint : ∀ earlier∈gkrChallengePaths sample earlierRounds,
      count ((uniformTuples sample (heterogeneousJointDimension layout)).flatMap
        (fun z => continuations.map (fun r => (z,r)))) (fun pair => event earlier pair.1 pair.2)*scale≤budget) :
    count ((uniformTuples sample layout.rowCoordinates).flatMap (fun rows =>
      (gkrChallengePaths sample earlierRounds).flatMap (fun earlier =>
        (gkrChallengeBlocks sample layout.inputLog).flatMap (fun block =>
          (uniformTuples sample layout.commonLog).flatMap (fun z =>
            continuations.map (fun r => (earlier,(rows++gkrBlockCoordinates block)++z,r)))))))
      (fun item => event item.1 item.2.1 item.2.2)*scale≤
    (gkrChallengePaths sample earlierRounds).length*budget := by
  rw [gkr_earlier_joint_event_count]
  generalize gkrChallengePaths sample earlierRounds=earliers at *
  induction earliers with
  | nil => simp
  | cons earlier rest ih =>
    have head := joint earlier (by simp)
    have tail := ih (fun a ha => joint a (by simp [ha]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul]
    omega

end NearCompression
