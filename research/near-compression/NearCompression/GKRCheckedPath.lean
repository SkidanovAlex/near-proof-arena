import NearCompression.GKRAdaptiveLayers
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def GKRLayerStrategy.checked {m : Nat} (s : GKRLayerStrategy K m) (block : GKRBlock K) : Prop :=
  weightedSumcheckChecks s.sentLeft s.claimLeft [] block.1 ∧
  s.claimRight block.1 []=s.claimLeft block.1 ∧
  weightedSumcheckChecks (s.sentRight block.1) (s.claimRight block.1) [] block.2.1 ∧
  gkrLayerWiring m s.gates (fun i => block.1.getD i 0) (fun i => block.2.1.getD i 0)
    (s.a block.1 block.2.1) (s.b block.1 block.2.1)=s.claimRight block.1 block.2.1

def GKRLayerStrategy.nextCorrect {m : Nat} (s : GKRLayerStrategy K m) (block : GKRBlock K) : Prop :=
  s.a block.1 block.2.1+block.2.2*s.b block.1 block.2.1=
    gkrInputFunctional m (fun i => block.1.getD i 0) (fun i => block.2.1.getD i 0) block.2.2 s.values

theorem gkr_checked_correct_repairs {m : Nat} (s : GKRLayerStrategy K m) (block : GKRBlock K)
    (wrong : s.wrong) (checked : s.checked block) (correct : s.nextCorrect block) :
    s.repair block :=
  ⟨wrong,checked.1,checked.2.1,checked.2.2.1,checked.2.2.2,correct⟩

/-- Explicit adjacent-layer binding: transmitted claim and honest functional
must refer to the same fixed circuit values. This lemma does not supply these
identities from an arbitrary transcript or a changing private assignment. -/
theorem gkr_adjacent_correctness {m n : Nat} (s : GKRLayerStrategy K m)
    (next : GKRLayerStrategy K n) (block : GKRBlock K)
    (claim : next.claimLeft []=s.a block.1 block.2.1+block.2.2*s.b block.1 block.2.1)
    (honest : (next.gates.map (fun item => item.2*gkrGateValue item.1.op
      (next.values item.1.left) (next.values item.1.right))).sum=
      gkrInputFunctional m (fun i => block.1.getD i 0) (fun i => block.2.1.getD i 0) block.2.2 s.values) :
    s.nextCorrect block ↔ ¬next.wrong := by
  simp only [GKRLayerStrategy.nextCorrect,GKRLayerStrategy.wrong,claim,honest,not_not]

/-- Checked route to a correct final input functional, with explicit adjacent
layer semantic linkage. The empty route cannot certify a false initial claim. -/
def gkrCheckedToInput (strategy : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (history : List (GKRBlock K)) : List Nat → List (GKRBlock K) → Prop
  | [],_ => False
  | _,[] => False
  | [m],[block] => (strategy m history).checked block ∧ (strategy m history).nextCorrect block
  | m::n::rest,block::tail => (strategy m history).checked block ∧
      ((strategy m history).nextCorrect block ↔ ¬(strategy n (history++[block])).wrong) ∧
      gkrCheckedToInput strategy (history++[block]) (n::rest) tail
  | _,_ => False

def gkrPathRepair (strategy : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (history : List (GKRBlock K)) : List Nat → List (GKRBlock K) → Prop
  | m::rest,block::tail => (strategy m history).repair block ∨
      gkrPathRepair strategy (history++[block]) rest tail
  | _,_ => False

/-- A false initial claim cannot reach a checked correct terminal functional
without one of the repair events already counted by the adaptive budget. -/
theorem gkr_checked_path_has_repair
    (strategy : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (rounds : List Nat) (blocks history : List (GKRBlock K))
    (checked : gkrCheckedToInput strategy history rounds blocks)
    (wrong : ∀ m rest,rounds=m::rest → (strategy m history).wrong) :
    gkrPathRepair strategy history rounds blocks := by
  classical
  induction rounds generalizing history blocks with
  | nil => simp [gkrCheckedToInput] at checked
  | cons m rest ih =>
    cases blocks with
    | nil => simp [gkrCheckedToInput] at checked
    | cons block tail =>
      cases rest with
      | nil =>
        cases tail with
        | nil => exact Or.inl (gkr_checked_correct_repairs _ _ (wrong m [] rfl) checked.1 checked.2)
        | cons _ _ => simp [gkrCheckedToInput] at checked
      | cons n rest =>
        cases tail with
        | nil => simp [gkrCheckedToInput] at checked
        | cons nextBlock tail =>
          change (strategy m history).checked block ∧ _ ∧ _ at checked
          by_cases nextWrong : (strategy n (history++[block])).wrong
          · apply Or.inr
            exact ih (nextBlock::tail) (history++[block]) checked.2.2 (by intro k ks eq;cases eq;exact nextWrong)
          · exact Or.inl (gkr_checked_correct_repairs _ _ (wrong m (n::rest) rfl)
              checked.1 (checked.2.1.mpr nextWrong))
end NearCompression
