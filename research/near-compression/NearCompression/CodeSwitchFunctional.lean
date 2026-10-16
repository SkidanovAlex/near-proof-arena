import NearCompression.RepeatedAffineFold

/-! Exact coefficient-functional update for code-switch OOD/query answers.
All answers and mixing scalars are explicit. These identities neither bind a
new commitment nor bound a malicious prover's chance of cancellation. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Powers begin at `power` and are multiplied by the evaluation point.
The coefficient coordinate stays fixed; only its functional weight changes. -/
def switchInjectPairs (point mixer power : K) : List (K × K) → List (K × K)
  | [] => []
  | (c,w)::rest => (c,w+mixer*power)::switchInjectPairs point mixer (power*point) rest

theorem switch_inject_coefficients (xs : List (K × K)) (point mixer power : K) :
    (switchInjectPairs point mixer power xs).map Prod.fst=xs.map Prod.fst := by
  induction xs generalizing power with
  | nil => rfl
  | cons a xs ih => simp only [switchInjectPairs,List.map_cons,ih]

/-- Evaluation constraints use monomial powers, not Boolean equality weights. -/
theorem switch_inject_dot (xs : List (K × K)) (point mixer power : K) :
    affineFoldDot (switchInjectPairs point mixer power xs)=affineFoldDot xs+
      mixer*power*(Poly.mk (xs.map Prod.fst)).eval point := by
  induction xs generalizing power with
  | nil => simp only [switchInjectPairs,affineFoldDot,List.map_nil,Poly.eval,Poly.evalL]; grind
  | cons a xs ih =>
    simp only [switchInjectPairs,affineFoldDot,List.map_cons,Poly.eval,Poly.evalL] at ih ⊢
    rw [ih]
    grind

structure SwitchConstraint (K : Type) where
  point : K
  answer : K
  mixer : K

def switchInjectAll (xs : List (K × K)) (claim : K) : List (SwitchConstraint K) → List (K × K) × K
  | [] => (xs,claim)
  | c::rest => switchInjectAll (switchInjectPairs c.point c.mixer 1 xs)
      (claim+c.mixer*c.answer) rest

def switchResidualSum (coefficients : List K) : List (SwitchConstraint K) → K
  | [] => 0
  | c::rest => c.mixer*((Poly.mk coefficients).eval c.point-c.answer)+switchResidualSum coefficients rest

/-- Arbitrary wrong claims and answers are covered, not just honest inputs.
This is the exact algebra needed by a later random-mixing error argument. -/
theorem switch_inject_all_residual (xs : List (K × K)) (claim : K)
    (constraints : List (SwitchConstraint K)) :
    affineFoldDot (switchInjectAll xs claim constraints).1-(switchInjectAll xs claim constraints).2=
      affineFoldDot xs-claim+switchResidualSum (xs.map Prod.fst) constraints := by
  induction constraints generalizing xs claim with
  | nil => simp only [switchInjectAll,switchResidualSum]; grind
  | cons c rest ih =>
    simp only [switchInjectAll]
    rw [ih,switch_inject_coefficients,switch_inject_dot]
    simp only [switchResidualSum]
    grind

theorem switch_honest_residual_zero (coefficients : List K) (constraints : List (SwitchConstraint K))
    (honest : ∀ c ∈ constraints,c.answer=(Poly.mk coefficients).eval c.point) :
    switchResidualSum coefficients constraints=0 := by
  induction constraints with
  | nil => rfl
  | cons c rest ih =>
    have hc:=honest c (List.mem_cons_self ..)
    have hr:=ih (fun d hd=>honest d (List.mem_cons_of_mem _ hd))
    simp only [switchResidualSum,hc,hr]
    grind

/-- The continuing functional remains true when every injected evaluation is
true and the previous functional is true. Arbitrary point locations allowed. -/
theorem switch_inject_all_honest (xs : List (K × K)) (claim : K)
    (constraints : List (SwitchConstraint K))
    (initial : affineFoldDot xs=claim)
    (honest : ∀ c ∈ constraints,c.answer=(Poly.mk (xs.map Prod.fst)).eval c.point) :
    affineFoldDot (switchInjectAll xs claim constraints).1=(switchInjectAll xs claim constraints).2 := by
  have residual:=switch_inject_all_residual xs claim constraints
  rw [initial,switch_honest_residual_zero _ _ honest] at residual
  grind
/-- With fixed prior claim and one wrong evaluation, at most one scalar can
cancel the residual. Using this probabilistically requires the answer and
prior claim to be fixed before an independent uniform mixer is sampled. -/
theorem switch_wrong_answer_unique_mixer (xs : List (K × K)) (claim point answer a b : K)
    (wrong : answer≠(Poly.mk (xs.map Prod.fst)).eval point)
    (acceptA : affineFoldDot (switchInjectPairs point a 1 xs)=claim+a*answer)
    (acceptB : affineFoldDot (switchInjectPairs point b 1 xs)=claim+b*answer) : a=b := by
  rw [switch_inject_dot] at acceptA acceptB
  grind
end NearCompression
