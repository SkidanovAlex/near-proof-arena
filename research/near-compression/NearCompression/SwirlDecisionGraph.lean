import NearCompression.SwirlGkrVerifierArithmetic

namespace NearCompression
open Lean.Grind

/-- Ordered decision view. A shared DAG may be unfolded to this view; skip
records a variable omitted because both cofactors are identical. -/
inductive SwirlDecision : Nat → Type where
  | terminal {n : Nat} (value : Bool) : SwirlDecision n
  | branch {n : Nat} (low high : SwirlDecision n) : SwirlDecision (n + 1)
  | skip {n : Nat} (child : SwirlDecision n) : SwirlDecision (n + 1)

def swirlDecisionTruth {n : Nat} (t : SwirlDecision n) (x : Fin n → Bool) : Bool :=
  match t with
  | .terminal b => b
  | .branch lo hi => if x 0 then swirlDecisionTruth hi (fun i => x i.succ)
                    else swirlDecisionTruth lo (fun i => x i.succ)
  | .skip child => swirlDecisionTruth child (fun i => x i.succ)

def swirlDecisionEval {K : Type} [Field K] {n : Nat}
    (t : SwirlDecision n) (r : Fin n → K) : K :=
  match t with
  | .terminal b => if b then 1 else 0
  | .branch lo hi =>
      let a := swirlDecisionEval lo (fun i => r i.succ)
      let b := swirlDecisionEval hi (fun i => r i.succ)
      a + r 0 * (b - a)
  | .skip child => swirlDecisionEval child (fun i => r i.succ)

/-- Dense multilinear extension in the declared coordinate order. -/
def swirlBooleanMLE {K : Type} [Field K] :
    (n : Nat) → ((Fin n → Bool) → K) → (Fin n → K) → K
  | 0, f, _ => f Fin.elim0
  | n + 1, f, r =>
      (1 - r 0) * swirlBooleanMLE n (fun x => f (Fin.cases false x)) (fun i => r i.succ) +
      r 0 * swirlBooleanMLE n (fun x => f (Fin.cases true x)) (fun i => r i.succ)

theorem swirl_boolean_mle_constant {K : Type} [Field K]
    (n : Nat) (v : K) (r : Fin n → K) :
    swirlBooleanMLE n (fun _ => v) r = v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [swirlBooleanMLE, ih]
    grind

/-- Structural correctness of branches, constant subtrees and skipped
variables. Sharing is immaterial once the ordered DAG has this unfolding. -/
theorem swirl_decision_eval_eq_mle {K : Type} [Field K] {n : Nat}
    (t : SwirlDecision n) (r : Fin n → K) :
    swirlDecisionEval t r =
      swirlBooleanMLE n (fun x => if swirlDecisionTruth t x then 1 else 0) r := by
  induction t with
  | terminal b =>
    exact (swirl_boolean_mle_constant _ (if b then (1 : K) else 0) r).symm
  | branch lo hi ilo ihi =>
    simp only [swirlDecisionEval, swirlBooleanMLE, swirlDecisionTruth, Fin.cases_zero,
      Fin.cases_succ, Bool.false_eq_true, ↓reduceIte, ilo, ihi]
    exact (swirl_shannon_interpolation (r 0) _ _).symm
  | skip child ih =>
    simp only [swirlDecisionEval, swirlBooleanMLE, swirlDecisionTruth, Fin.cases_succ, ih]
    exact (swirl_shannon_equal_children (r 0) _).symm

/-- A separately established Boolean-support correspondence transfers to all
field evaluation points, not only the Boolean cube. -/
theorem swirl_decision_support_refinement {K : Type} [Field K] {n : Nat}
    (t : SwirlDecision n) (support : (Fin n → Bool) → Bool)
    (h : ∀ x, swirlDecisionTruth t x = support x) (r : Fin n → K) :
    swirlDecisionEval t r =
      swirlBooleanMLE n (fun x => if support x then 1 else 0) r := by
  rw [swirl_decision_eval_eq_mle]
  congr 1
  funext x
  rw [h x]

end NearCompression
