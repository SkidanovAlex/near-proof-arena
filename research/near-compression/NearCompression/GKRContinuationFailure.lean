import NearCompression.GKRTerminalFailure
import NearCompression.GKRRecoveredTerminal
namespace NearCompression
open Lean.Grind ArenaCore.Security ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Exposes the exact last GKR layer, retaining its complete preceding history.
No correctness of the final opening is assumed. -/
theorem gkr_terminal_mismatch_last
    (strategy : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (values : Nat → Nat → K) (rounds : List Nat) (blocks history : List (GKRBlock K))
    (sameLength : blocks.length=rounds.length) (depth m : Nat) (block : GKRBlock K) :
    gkrTerminalMismatch strategy values depth history (rounds++[m]) (blocks++[block]) ↔
      (strategy m (history++blocks)).a block.1 block.2.1+
        block.2.2*(strategy m (history++blocks)).b block.1 block.2.1≠
      gkrInputFunctional m (fun i => block.1.getD i 0) (fun i => block.2.1.getD i 0)
        block.2.2 (values (depth+rounds.length)) := by
  induction rounds generalizing blocks history depth with
  | nil =>
    have empty : blocks=[] := List.eq_nil_of_length_eq_zero sameLength
    subst blocks
    simp [gkrTerminalMismatch,gkr_next_queries]
  | cons n rest ih =>
    cases blocks with
    | nil => simp at sameLength
    | cons b tail =>
      have length : tail.length=rest.length := by simpa using sameLength
      cases rest with
      | nil =>
        have empty : tail=[] := List.eq_nil_of_length_eq_zero length
        subst tail
        simp [gkrTerminalMismatch,gkr_next_queries]
      | cons k rest =>
        simpa [gkrTerminalMismatch,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using ih tail (history++[b]) length (depth+1)

/-- The terminal mismatch is exactly the full recovered-input event when the
fixed circuit input is the decoded tuple plus the known constants. This
assignment equality is explicit; it must come from the upstream circuit model. -/
theorem gkr_terminal_recovered_mismatch
    (strategy : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (values : Nat → Nat → K) (rounds : List Nat) (blocks history : List (GKRBlock K))
    (sameLength : blocks.length=rounds.length) (depth : Nat) (block : GKRBlock K)
    (layout : GKRJointLayout) (entries : List (GKRSourceLane × Poly K))
    (rowpoints : GKRSourceLane → Nat → K) (constants : List (Nat × K))
    (assignment : values (depth+rounds.length)=fun i =>
      gkrScatter (recoveredPrivateSlots layout.commonLog entries rowpoints) i+gkrScatter constants i) :
    gkrTerminalMismatch strategy values depth history (rounds++[layout.inputLog]) (blocks++[block]) ↔
      (strategy layout.inputLog (history++blocks)).a block.1 block.2.1+
        block.2.2*(strategy layout.inputLog (history++blocks)).b block.1 block.2.1≠
      gkrInputFunctional layout.inputLog (fun i => block.1.getD i 0) (fun i => block.2.1.getD i 0)
        block.2.2 (fun i => gkrScatter (recoveredPrivateSlots layout.commonLog entries rowpoints) i+
          gkrScatter constants i) := by
  rw [gkr_terminal_mismatch_last strategy values rounds blocks history sameLength depth layout.inputLog block,assignment]

private theorem count_union {A : Type} (xs : List A) (p q : A → Prop) :
    count xs (fun x => p x ∨ q x)≤count xs p+count xs q := by
  classical
  induction xs with
  | nil => simp [count]
  | cons x xs ih =>
    simp only [count,List.countP_cons] at ih ⊢
    by_cases hp : p x <;> by_cases hq : q x <;> simp_all <;> omega

private theorem count_first {A B : Type} (xs : List A) (ys : List B) (p : A → Prop) :
    count (xs.flatMap (fun x => ys.map (fun y => (x,y)))) (fun pair => p pair.1)=
      count xs p*ys.length := by
  classical
  induction xs with
  | nil => simp [count]
  | cons x xs ih =>
    simp only [List.flatMap_cons,count,List.countP_append,List.countP_map,Function.comp_def] at ih ⊢
    rw [ih]
    by_cases h : p x <;> simp [h,Nat.add_mul,Nat.add_comm]

/-- A false circuit-output claim with arbitrary subsequent PCS randomness.
The PCS error is counted on the SAME joint experiment; no independence between
acceptance, GKR paths and opening failures is assumed. -/
theorem gkr_continuation_terminal_error_budget {R : Type}
    (sample : List K) (distinct : sample.Nodup)
    (strategy : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (values : Nat → Nat → K) (wiring : Nat → Nat → GKRWiringGate)
    (rounds : List Nat) (history : List (GKRBlock K)) (depth : Nat)
    (continuations : List R) (accepted : List (GKRBlock K) → R → Prop)
    (checks : ∀ blocks r,accepted blocks r → gkrCircuitVerifierPath strategy values wiring depth history rounds blocks)
    (wrong : ∀ m rest,rounds=m::rest → (strategy m history).wrong) :
    let experiment := (gkrChallengePaths sample rounds).flatMap
      (fun blocks => continuations.map (fun r => (blocks,r)))
    count experiment (fun pair => accepted pair.1 pair.2)*sample.length≤
      (rounds.map (fun m => 4*m+1)).sum*(gkrChallengePaths sample rounds).length*continuations.length+
      count experiment (fun pair => accepted pair.1 pair.2 ∧
        gkrTerminalMismatch strategy values depth history rounds pair.1)*sample.length := by
  dsimp only
  let experiment := (gkrChallengePaths sample rounds).flatMap
    (fun blocks => continuations.map (fun r => (blocks,r)))
  let correct := fun pair : List (GKRBlock K) × R =>
    gkrCircuitCheckedToInput strategy values wiring depth history rounds pair.1
  let failure := fun pair : List (GKRBlock K) × R => accepted pair.1 pair.2 ∧
    gkrTerminalMismatch strategy values depth history rounds pair.1
  have subset : count experiment (fun pair => accepted pair.1 pair.2)≤
      count experiment (fun pair => correct pair ∨ failure pair) := by
    apply count_mono
    intro pair accept
    rcases gkr_verifier_path_split strategy values wiring rounds pair.1 history depth
      (checks pair.1 pair.2 accept) with good|bad
    · exact Or.inl good
    · exact Or.inr ⟨accept,bad⟩
  have split := Nat.mul_le_mul_right sample.length
    (Nat.le_trans subset (count_union experiment correct failure))
  have good := gkr_circuit_checked_path_budget sample distinct strategy values wiring rounds history depth wrong
  have rectangle : count experiment correct=
      count (gkrChallengePaths sample rounds)
        (gkrCircuitCheckedToInput strategy values wiring depth history rounds)*continuations.length :=
    count_first _ _ _
  rw [Nat.add_mul,rectangle] at split
  have scaled := Nat.mul_le_mul_right continuations.length good
  have reorder : count (gkrChallengePaths sample rounds)
      (gkrCircuitCheckedToInput strategy values wiring depth history rounds)*continuations.length*sample.length=
      count (gkrChallengePaths sample rounds)
      (gkrCircuitCheckedToInput strategy values wiring depth history rounds)*sample.length*continuations.length := by ac_rfl
  rw [reorder] at split
  exact Nat.le_trans split (Nat.add_le_add_right scaled _)

end NearCompression
