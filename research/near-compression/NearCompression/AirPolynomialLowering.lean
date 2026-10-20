import ZkFormal.Air.Basic
import ZkFormal.Algebra.PolyLemmas

/-! Full AIR expression substitution into univariate polynomials. These are
deterministic algebraic bridges; no commitment or probabilistic claim is made.
A univariate environment can describe one coordinate of a multilinear witness
after the other coordinates have been fixed. Binding that environment to the
actual trace (especially next rows and selectors) is a separate obligation. -/
namespace NearCompression

open ZkFormal.Air ZkFormal.Algebra

structure AirPolynomialInputs (K : Type) where
  col : Nat → Bool → Poly K
  pub : Nat → Poly K
  isFirst : Poly K
  isLast : Poly K
  isTransition : Poly K

variable {K : Type} [Lean.Grind.CommRing K]

def airPolynomialEnv (p : AirPolynomialInputs K) : Env (Poly K) where
  ofNat := fun n => Poly.C (@Nat.cast K Lean.Grind.Semiring.natCast n)
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  col := p.col
  pub := p.pub
  isFirst := p.isFirst
  isLast := p.isLast
  isTransition := p.isTransition

/-- Total lowering, including next columns, publics and all three selectors. -/
def airPolynomialLower (p : AirPolynomialInputs K) (e : Expr) : Poly K :=
  e.evalWith (airPolynomialEnv p)

def airPolynomialPointEnv (p : AirPolynomialInputs K) (x : K) : Env K where
  ofNat := fun n => (@Nat.cast K Lean.Grind.Semiring.natCast n)
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  col := fun c nx => (p.col c nx).eval x
  pub := fun i => (p.pub i).eval x
  isFirst := p.isFirst.eval x
  isLast := p.isLast.eval x
  isTransition := p.isTransition.eval x

theorem air_polynomial_lower_eval (p : AirPolynomialInputs K) (e : Expr) (x : K) :
    (airPolynomialLower p e).eval x = e.evalWith (airPolynomialPointEnv p x) := by
  induction e with
  | const n => exact Poly.eval_C _ _
  | col c nx => rfl
  | pub i => rfl
  | isFirst => rfl
  | isLast => rfl
  | isTransition => rfl
  | add a b ha hb =>
      change (airPolynomialLower p a + airPolynomialLower p b).eval x = _
      rw [Poly.eval_add, ha, hb]
      rfl
  | mul a b ha hb =>
      change (airPolynomialLower p a * airPolynomialLower p b).eval x = _
      rw [Poly.eval_mul, ha, hb]
      rfl
  | neg a ha => exact (Poly.eval_neg _ _).trans (congrArg Neg.neg ha)

/-- Public values must be constant in the sumcheck variable, as Expr.degree
assigns them degree zero. Columns and selectors may be affine. -/
structure AirPolynomialAffine (p : AirPolynomialInputs K) : Prop where
  col : ∀ c nx, (p.col c nx).DegLt 2
  pub : ∀ i, (p.pub i).DegLt 1
  isFirst : p.isFirst.DegLt 2
  isLast : p.isLast.DegLt 2
  isTransition : p.isTransition.DegLt 2

theorem air_polynomial_lower_degree (p : AirPolynomialInputs K)
    (h : AirPolynomialAffine p) (e : Expr) :
    (airPolynomialLower p e).DegLt (e.degree + 1) := by
  induction e with
  | const n => exact Poly.degLt_length (Poly.C (@Nat.cast K Lean.Grind.Semiring.natCast n))
  | col c nx => exact h.col c nx
  | pub i => exact h.pub i
  | isFirst => exact h.isFirst
  | isLast => exact h.isLast
  | isTransition => exact h.isTransition
  | add a b ha hb =>
      exact Poly.degLt_add
        (ha.mono (Nat.add_le_add_right (Nat.le_max_left _ _) 1))
        (hb.mono (Nat.add_le_add_right (Nat.le_max_right _ _) 1))
  | mul a b ha hb => exact Poly.degLt_mul ha hb
  | neg a ha => exact Poly.degLt_neg ha

/-- A supplied environment equality binds all AIR leaves, not just columns. -/
theorem air_polynomial_lower_trace_eval (p : AirPolynomialInputs K)
    (tr : Trace K) (t r : Nat) (pub : List K) (x : K)
    (bound : airPolynomialPointEnv p x = rowEnv tr t r pub) (e : Expr) :
    (airPolynomialLower p e).eval x = e.eval tr t r pub := by
  rw [air_polynomial_lower_eval, bound]
  rfl

theorem air_polynomial_lower_trace_zero (p : AirPolynomialInputs K)
    (tr : Trace K) (t r : Nat) (pub : List K) (x : K)
    (bound : airPolynomialPointEnv p x = rowEnv tr t r pub) (e : Expr)
    (valid : e.eval tr t r pub = 0) : (airPolynomialLower p e).eval x = 0 := by
  rw [air_polynomial_lower_trace_eval p tr t r pub x bound e, valid]

/-- Output-minus-expression gate semantics, in both directions. -/
theorem air_polynomial_output_gate (p : AirPolynomialInputs K) (e : Expr)
    (output : Poly K) (x : K) :
    (output - airPolynomialLower p e).eval x = 0 ↔
      output.eval x = e.evalWith (airPolynomialPointEnv p x) := by
  rw [Poly.eval_sub, air_polynomial_lower_eval]
  constructor <;> intro h <;> grind

theorem air_polynomial_honest_output_gate (p : AirPolynomialInputs K) (e : Expr) (x : K) :
    (airPolynomialLower p e - airPolynomialLower p e).eval x = 0 := by
  rw [air_polynomial_output_gate]
  exact air_polynomial_lower_eval p e x

/-- Concrete trace binding baseline, including cyclic next-row reads. This
constant specialization is useful for compiler conformance; multilinear
sumcheck environments must separately establish their Boolean-point binding. -/
def airPolynomialRowInputs (tr : Trace K) (t r : Nat) (pub : List K) :
    AirPolynomialInputs K where
  col := fun c nx => Poly.C ((rowEnv tr t r pub).col c nx)
  pub := fun i => Poly.C ((rowEnv tr t r pub).pub i)
  isFirst := Poly.C ((rowEnv tr t r pub).isFirst)
  isLast := Poly.C ((rowEnv tr t r pub).isLast)
  isTransition := Poly.C ((rowEnv tr t r pub).isTransition)

theorem air_polynomial_row_env (tr : Trace K) (t r : Nat) (pub : List K) (x : K) :
    airPolynomialPointEnv (airPolynomialRowInputs tr t r pub) x = rowEnv tr t r pub := by
  simp only [airPolynomialPointEnv, airPolynomialRowInputs, Poly.eval_C]
  rfl

theorem air_polynomial_row_eval (tr : Trace K) (t r : Nat) (pub : List K)
    (e : Expr) (x : K) :
    (airPolynomialLower (airPolynomialRowInputs tr t r pub) e).eval x =
      e.eval tr t r pub :=
  air_polynomial_lower_trace_eval _ tr t r pub x (air_polynomial_row_env tr t r pub x) e

theorem air_polynomial_row_affine (tr : Trace K) (t r : Nat) (pub : List K) :
    AirPolynomialAffine (airPolynomialRowInputs tr t r pub) := by
  have hc (v : K) : (Poly.C v).DegLt 1 := Poly.degLt_length _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c nx; exact (hc _).mono (by decide)
  · intro i; exact hc _
  · exact (hc _).mono (by decide)
  · exact (hc _).mono (by decide)
  · exact (hc _).mono (by decide)

end NearCompression
