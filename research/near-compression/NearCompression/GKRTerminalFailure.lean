import NearCompression.GKRCircuitPath
namespace NearCompression
open Lean.Grind ArenaCore.Security
variable {K : Type} [Field K]

/-- All GKR circuit and message checks, without assuming the terminal
opening is correct. This relation still needs executable-verifier refinement. -/
def gkrCircuitVerifierPath
    (strategy : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (values : Nat → Nat → K) (wiring : Nat → Nat → GKRWiringGate)
    (depth : Nat) (history : List (GKRBlock K)) : List Nat → List (GKRBlock K) → Prop
  | [],_ => False
  | _,[] => False
  | [m],[block] =>
      (strategy m history).values=values depth ∧
      (strategy m history).checked block
  | m::n::rest,block::tail =>
      (strategy m history).values=values depth ∧
      (strategy m history).checked block ∧
      (strategy n (history++[block])).values=values (depth+1) ∧
      (strategy n (history++[block])).gates=gkrWeightedLayer m (wiring depth)
        [(fun i => block.1.getD i 0,1),(fun i => block.2.1.getD i 0,block.2.2)] ∧
      (∀ i,i<2^m → values depth i=gkrLayerValues (values (depth+1)) (wiring depth) i) ∧
      (strategy n (history++[block])).claimLeft []=
        (strategy m history).a block.1 block.2.1+block.2.2*(strategy m history).b block.1 block.2.1 ∧
      gkrCircuitVerifierPath strategy values wiring (depth+1) (history++[block]) (n::rest) tail
  | _,_ => False


/-- Incorrect combined terminal opening against the fixed circuit input.
The predicate is false for malformed path lengths. -/
def gkrTerminalMismatch
    (strategy : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (values : Nat → Nat → K) (depth : Nat) (history : List (GKRBlock K)) :
    List Nat → List (GKRBlock K) → Prop
  | [m],[block] =>
      (strategy m history).a block.1 block.2.1+block.2.2*(strategy m history).b block.1 block.2.1≠
        gkrQueryFunctional m (values depth)
          [(fun i => block.1.getD i 0,1),(fun i => block.2.1.getD i 0,block.2.2)]
  | _::n::rest,block::tail => gkrTerminalMismatch strategy values (depth+1) (history++[block]) (n::rest) tail
  | _,_ => False

/-- Every checked circuit path either has a correct terminal functional or
exhibits the precise opening mismatch to be charged to PCS soundness. -/
theorem gkr_verifier_path_split
    (strategy : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (values : Nat → Nat → K) (wiring : Nat → Nat → GKRWiringGate)
    (rounds : List Nat) (blocks history : List (GKRBlock K)) (depth : Nat)
    (checks : gkrCircuitVerifierPath strategy values wiring depth history rounds blocks) :
    gkrCircuitCheckedToInput strategy values wiring depth history rounds blocks ∨
      gkrTerminalMismatch strategy values depth history rounds blocks := by
  classical
  induction rounds generalizing blocks history depth with
  | nil => simp [gkrCircuitVerifierPath] at checks
  | cons m rest ih =>
    cases blocks with
    | nil => simp [gkrCircuitVerifierPath] at checks
    | cons block tail =>
      cases rest with
      | nil =>
        cases tail with
        | nil =>
          by_cases terminal : gkrTerminalMismatch strategy values depth history [m] [block]
          · exact Or.inr terminal
          · apply Or.inl
            exact ⟨checks.1,checks.2,Classical.not_not.mp terminal⟩
        | cons _ _ => simp [gkrCircuitVerifierPath] at checks
      | cons n rest =>
        cases tail with
        | nil => simp [gkrCircuitVerifierPath] at checks
        | cons nextBlock tail =>
          obtain ⟨fixed,checked,nextFixed,queries,evaluation,claim,following⟩:=checks
          rcases ih (nextBlock::tail) (history++[block]) (depth+1) following with good|bad
          · exact Or.inl ⟨fixed,checked,nextFixed,queries,evaluation,claim,good⟩
          · exact Or.inr bad

private theorem count_or {A : Type} (sample : List A) (p q : A → Prop) :
    count sample (fun a => p a ∨ q a)≤count sample p+count sample q := by
  classical
  induction sample with
  | nil => simp [count]
  | cons a rest ih =>
    simp only [count,List.countP_cons] at ih ⊢
    by_cases hp : p a <;> by_cases hq : q a <;> simp_all <;> omega

/-- Acceptance with a false root claim is bounded by the proved GKR term
plus accepted incorrect terminal openings. No PCS error bound is assumed or
silently set to zero. The final predicate may include arbitrary PCS checks. -/
theorem gkr_verifier_terminal_error_budget (sample : List K) (distinct : sample.Nodup)
    (strategy : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (values : Nat → Nat → K) (wiring : Nat → Nat → GKRWiringGate)
    (rounds : List Nat) (history : List (GKRBlock K)) (depth : Nat)
    (accepted : List (GKRBlock K) → Prop)
    (checks : ∀ blocks,accepted blocks → gkrCircuitVerifierPath strategy values wiring depth history rounds blocks)
    (wrong : ∀ m rest,rounds=m::rest → (strategy m history).wrong) :
    count (gkrChallengePaths sample rounds) accepted*sample.length≤
      (rounds.map (fun m => 4*m+1)).sum*(gkrChallengePaths sample rounds).length+
      count (gkrChallengePaths sample rounds)
        (fun blocks => accepted blocks ∧ gkrTerminalMismatch strategy values depth history rounds blocks)*sample.length := by
  have subset : count (gkrChallengePaths sample rounds) accepted≤
      count (gkrChallengePaths sample rounds) (fun blocks =>
        gkrCircuitCheckedToInput strategy values wiring depth history rounds blocks ∨
        (accepted blocks ∧ gkrTerminalMismatch strategy values depth history rounds blocks)) := by
    apply count_mono
    intro blocks accept
    rcases gkr_verifier_path_split strategy values wiring rounds blocks history depth (checks blocks accept) with good|bad
    · exact Or.inl good
    · exact Or.inr ⟨accept,bad⟩
  have union:=count_or (gkrChallengePaths sample rounds)
    (gkrCircuitCheckedToInput strategy values wiring depth history rounds)
    (fun blocks => accepted blocks ∧ gkrTerminalMismatch strategy values depth history rounds blocks)
  have scaled:=Nat.mul_le_mul_right sample.length (Nat.le_trans subset union)
  have bound:=gkr_circuit_checked_path_budget sample distinct strategy values wiring rounds history depth wrong
  rw [Nat.add_mul] at scaled
  exact Nat.le_trans scaled (Nat.add_le_add_right bound _)
end NearCompression
