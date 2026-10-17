import NearCompression.InstructionSumcheckSoundness
namespace NearCompression
open Lean.Grind ArenaCore.Security

private def sumNat {A : Type} (xs : List A) (f : A → Nat) : Nat := (xs.map f).sum
private theorem sumNat_add {A : Type} (xs : List A) (f g : A → Nat) :
    sumNat xs (fun x => f x+g x)=sumNat xs f+sumNat xs g := by
  induction xs with
  | nil => simp [sumNat]
  | cons x xs ih => simp only [sumNat,List.map_cons,List.sum_cons] at ih ⊢; omega
private theorem sumNat_mul {A : Type} (xs : List A) (f : A → Nat) (k : Nat) :
    sumNat xs (fun x => f x*k)=sumNat xs f*k := by
  induction xs with
  | nil => simp [sumNat]
  | cons x xs ih => simp only [sumNat,List.map_cons,List.sum_cons] at ih ⊢; grind
private theorem sumNat_mono {A : Type} (xs : List A) (f g : A → Nat)
    (bound : ∀ x∈xs,f x≤g x) : sumNat xs f≤sumNat xs g := by
  induction xs with
  | nil => simp [sumNat]
  | cons x xs ih =>
    have h := bound x (by simp)
    have t := ih (fun y hy => bound y (by simp [hy]))
    simp only [sumNat,List.map_cons,List.sum_cons] at t ⊢; omega
private theorem sumNat_const {A : Type} (xs : List A) (k : Nat) :
    sumNat xs (fun _ => k)=xs.length*k := by
  induction xs with
  | nil => simp [sumNat]
  | cons x xs ih => simp only [sumNat,List.map_cons,List.sum_cons,List.length_cons] at ih ⊢; grind
private theorem sumNat_event {A : Type} (xs : List A) (event : A → Prop) [DecidablePred event] (k : Nat) :
    sumNat xs (fun x => if event x then k else 0)=count xs event*k := by
  classical
  induction xs with
  | nil => simp [sumNat,count]
  | cons x xs ih =>
    simp only [sumNat,List.map_cons,List.sum_cons,count,List.countP_cons] at ih ⊢
    by_cases h : event x <;> simp_all <;> grind

/-- Number of failing leaves in the complete uniform challenge tree. Once a
bad event happens, every continuation is failing. Predicates may depend on the
ENTIRE prior history, allowing a fixed adaptive prover strategy. -/
noncomputable def adaptiveFailureLeaves {A : Type} (sample : List A)
    (bad : List A → A → Prop) (history : List A) : Nat → Nat := by
  classical
  exact fun depth => match depth with
    | 0 => 0
    | n+1 => sumNat sample (fun a => if bad history a then sample.length^n else
        adaptiveFailureLeaves sample bad (history++[a]) n)

/-- Per-history conditional bounds, not marginal per-round bounds. Requiring
this only at reachable prefixes is possible but unnecessary here. -/
def AdaptiveRoundBounds {A : Type} (sample : List A) (bad : List A → A → Prop)
    (history : List A) : List Nat → Prop
  | [] => True
  | e::es => count sample (bad history)≤e ∧
      ∀ a∈sample,AdaptiveRoundBounds sample bad (history++[a]) es

/-- Cross-multiplied union bound for independent uniform draws with replacement:
P(any bad round) <= sum(errors)/|sample|. No nonadaptive transcript assumption.
This is a finite tree count; it is not a Fiat--Shamir/QROM statement. -/
theorem adaptive_round_failure_budget {A : Type} (sample : List A)
    (bad : List A → A → Prop) (history : List A) (errors : List Nat)
    (bounds : AdaptiveRoundBounds sample bad history errors) :
    adaptiveFailureLeaves sample bad history errors.length*sample.length ≤
      errors.sum*sample.length^errors.length := by
  classical
  induction errors generalizing history with
  | nil => simp [adaptiveFailureLeaves]
  | cons e es ih =>
    obtain ⟨head,tail⟩ := bounds
    have inductionBound : ∀ a∈sample,
        adaptiveFailureLeaves sample bad (history++[a]) es.length*sample.length≤
          es.sum*sample.length^es.length := fun a ha => ih _ (tail a ha)
    have point : ∀ a∈sample,
        (if bad history a then sample.length^es.length else
          adaptiveFailureLeaves sample bad (history++[a]) es.length)*sample.length ≤
        (if bad history a then sample.length^es.length*sample.length else 0)+
          es.sum*sample.length^es.length := by
      intro a ha
      have h := inductionBound a ha
      by_cases hb : bad history a <;> simp_all <;> omega
    have sum := sumNat_mono sample _ _ point
    rw [sumNat_mul,sumNat_add,sumNat_event,sumNat_const] at sum
    have headScaled := Nat.mul_le_mul_right (sample.length^es.length*sample.length) head
    simp only [adaptiveFailureLeaves,List.length_cons,List.sum_cons,Nat.pow_succ]
    grind

end NearCompression
