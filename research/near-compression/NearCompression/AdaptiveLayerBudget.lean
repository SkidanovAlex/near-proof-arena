import NearCompression.GKRLayerBudget
namespace NearCompression
open Lean.Grind ArenaCore.Security

/-- Different layers may consume different numbers of field challenges. Each
sample entry is an entire layer block; repetitions retain their multiplicity. -/
def layerChallengeMass {A : Type} : List (List A × Nat) → Nat
  | [] => 1
  | (sample,_)::rest => sample.length * layerChallengeMass rest

noncomputable def adaptiveLayerFailures {A : Type} (bad : List A → A → Prop)
    (history : List A) : List (List A × Nat) → Nat := by
  classical
  exact fun stages => match stages with
    | [] => 0
    | (sample,_)::rest => (sample.map (fun a => if bad history a then
        layerChallengeMass rest else adaptiveLayerFailures bad (history++[a]) rest)).sum

def AdaptiveLayerBounds {A : Type} (scale : Nat) (bad : List A → A → Prop)
    (history : List A) : List (List A × Nat) → Prop
  | [] => True
  | (sample,error)::rest => count sample (bad history)*scale≤error*sample.length ∧
      ∀ a∈sample,AdaptiveLayerBounds scale bad (history++[a]) rest

private theorem bounded_sum {A : Type} (xs : List A) (f : A → Nat) (m : Nat)
    (h : ∀ a∈xs,f a≤m) : (xs.map f).sum≤xs.length*m := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have head := h a (by simp)
    have tail := ih (by intro b hb;exact h b (by simp [hb]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem adaptive_layer_failures_bounded {A : Type} (bad : List A → A → Prop)
    (stages : List (List A × Nat)) (history : List A) :
    adaptiveLayerFailures bad history stages≤layerChallengeMass stages := by
  classical
  induction stages generalizing history with
  | nil => simp [adaptiveLayerFailures,layerChallengeMass]
  | cons stage rest ih =>
    rcases stage with ⟨sample,error⟩
    apply bounded_sum
    intro a ha
    split
    · exact Nat.le_refl _
    · exact ih _

/-- Causal union bound across unequal layer challenge blocks, with a common
field-size denominator. This is an ideal finite-tree theorem, not a statement
about Fiat--Shamir, commitment binding, or whole-proof acceptance. -/
theorem adaptive_layer_failure_budget {A : Type} (scale : Nat)
    (bad : List A → A → Prop) (stages : List (List A × Nat)) (history : List A)
    (bounds : AdaptiveLayerBounds scale bad history stages) :
    adaptiveLayerFailures bad history stages*scale≤
      (stages.map Prod.snd).sum*layerChallengeMass stages := by
  classical
  induction stages generalizing history with
  | nil => simp [adaptiveLayerFailures]
  | cons stage rest ih =>
    rcases stage with ⟨sample,error⟩
    obtain ⟨head,tail⟩ := bounds
    let f := fun a => if bad history a then layerChallengeMass rest else
      adaptiveLayerFailures bad (history++[a]) rest
    have total := conditional_scaled_sum sample (bad history) f (layerChallengeMass rest)
      scale ((rest.map Prod.snd).sum*layerChallengeMass rest)
      (by
        intro a ha
        dsimp [f]
        split
        · exact Nat.le_refl _
        · exact adaptive_layer_failures_bounded bad rest _)
      (by
        intro a ha good
        simp only [f,if_neg good]
        exact ih _ (tail a ha))
    have scaled := Nat.mul_le_mul_right (layerChallengeMass rest) head
    change (sample.map f).sum*scale≤(error+(rest.map Prod.snd).sum)*
      (sample.length*layerChallengeMass rest)
    grind
end NearCompression
