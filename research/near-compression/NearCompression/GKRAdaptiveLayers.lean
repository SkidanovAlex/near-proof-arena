import NearCompression.GKRStrategyRepair
namespace NearCompression
open Lean.Grind ArenaCore.Security
variable {K : Type} [Field K]

abbrev GKRBlock (K : Type) := List K × List K × K

def gkrLayerStages (sample : List K) (rounds : List Nat) : List (List (GKRBlock K) × Nat) :=
  rounds.map (fun m => (gkrChallengeBlocks sample m,4*m+1))

/-- The prover selects each layer strategy using all earlier layer blocks.
Within the layer, the strategy's message types enforce challenge causality. -/
noncomputable def gkrAdaptiveLayerFailures (sample : List K)
    (strategy : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (history : List (GKRBlock K)) : List Nat → Nat := by
  classical
  exact fun rounds => match rounds with
    | [] => 0
    | m::rest => ((gkrChallengeBlocks sample m).map (fun block =>
        if (strategy m history).repair block then layerChallengeMass (gkrLayerStages sample rest)
        else gkrAdaptiveLayerFailures sample strategy (history++[block]) rest)).sum

private theorem sum_bounded {A : Type} (xs : List A) (f : A → Nat) (bound : Nat)
    (h : ∀ a∈xs,f a≤bound) : (xs.map f).sum≤xs.length*bound := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have head:=h a (by simp)
    have tail:=ih (by intro b hb;exact h b (by simp [hb]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem gkr_adaptive_layer_failures_bounded (sample : List K)
    (strategy : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (rounds : List Nat) (history : List (GKRBlock K)) :
    gkrAdaptiveLayerFailures sample strategy history rounds≤
      layerChallengeMass (gkrLayerStages sample rounds) := by
  classical
  induction rounds generalizing history with
  | nil => simp [gkrAdaptiveLayerFailures,gkrLayerStages,layerChallengeMass]
  | cons m rest ih =>
    apply sum_bounded
    intro block hb
    split
    · exact Nat.le_refl _
    · exact ih _

/-- Actual causal GKR repair-event union bound for arbitrarily many layers
with different axis lengths. All per-layer bounds are discharged from GKR;
there is no caller-supplied soundness premise. This counts repair events, not
yet whole-proof acceptance, and uses ideal uniform field challenges. -/
theorem gkr_adaptive_layers_repair_budget (sample : List K) (distinct : sample.Nodup)
    (strategy : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (rounds : List Nat) (history : List (GKRBlock K)) :
    gkrAdaptiveLayerFailures sample strategy history rounds*sample.length≤
      (rounds.map (fun m => 4*m+1)).sum*layerChallengeMass (gkrLayerStages sample rounds) := by
  classical
  induction rounds generalizing history with
  | nil => simp [gkrAdaptiveLayerFailures]
  | cons m rest ih =>
    let blocks:=gkrChallengeBlocks sample m
    let mass:=layerChallengeMass (gkrLayerStages sample rest)
    let f:=fun block => if (strategy m history).repair block then mass else
      gkrAdaptiveLayerFailures sample strategy (history++[block]) rest
    have total:=conditional_scaled_sum blocks (strategy m history).repair f mass sample.length
      ((rest.map (fun m => 4*m+1)).sum*mass)
      (by
        intro block hb
        dsimp [f]
        split
        · exact Nat.le_refl _
        · exact gkr_adaptive_layer_failures_bounded sample strategy rest _)
      (by
        intro block hb good
        simp only [f,if_neg good]
        exact ih _)
    have one:=gkr_strategy_repair_bound sample distinct m (strategy m history)
    have scaled:=Nat.mul_le_mul_right mass one
    change (blocks.map f).sum*sample.length≤
      (4*m+1+(rest.map (fun m => 4*m+1)).sum)*(blocks.length*mass)
    grind
end NearCompression
