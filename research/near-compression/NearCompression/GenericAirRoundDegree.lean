import NearCompression.AirPolynomialLowering
import NearCompression.InstructionSumcheckSoundness

/-! Actual AST lowering, constraint batching and suffix summation retain the
per-coordinate degree bound. This derives the honest round bound used by a
single-round root count; it does not claim complete protocol soundness. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra

section Ring
variable {K : Type} [Lean.Grind.CommRing K]

theorem generic_air_weighted_lower_degree (p : AirPolynomialInputs K)
    (affine : AirPolynomialAffine p) (weight : Poly K) (hw : weight.DegLt 2)
    (e : Expr) (d : Nat) (he : e.degree ≤ d) :
    (weight * airPolynomialLower p e).DegLt (d+2) := by
  have h := Poly.degLt_mul hw ((air_polynomial_lower_degree p affine e).mono
    (Nat.add_le_add_right he 1))
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- Scalar coefficients are the already-fixed constraint batching weights. -/
def genericAirConstraintPolynomial (p : AirPolynomialInputs K) : List (K × Expr) → Poly K
  | [] => Poly.zero
  | (c,e)::rest => Poly.smul c (airPolynomialLower p e) + genericAirConstraintPolynomial p rest

def genericAirConstraintValue (p : AirPolynomialInputs K) (x : K) : List (K × Expr) → K
  | [] => 0
  | (c,e)::rest => c*e.evalWith (airPolynomialPointEnv p x) + genericAirConstraintValue p x rest

theorem generic_air_constraint_polynomial_eval (p : AirPolynomialInputs K)
    (es : List (K × Expr)) (x : K) :
    (genericAirConstraintPolynomial p es).eval x = genericAirConstraintValue p x es := by
  induction es with
  | nil => rfl
  | cons ce rest ih =>
    obtain ⟨c,e⟩ := ce
    simp only [genericAirConstraintPolynomial, genericAirConstraintValue,
      Poly.eval_add, Poly.eval_smul, air_polynomial_lower_eval, ih]

theorem generic_air_constraint_polynomial_degree (p : AirPolynomialInputs K)
    (affine : AirPolynomialAffine p) (es : List (K × Expr)) (d : Nat)
    (degrees : ∀ ce ∈ es, ce.2.degree ≤ d) :
    (genericAirConstraintPolynomial p es).DegLt (d+1) := by
  induction es with
  | nil => exact (Poly.degLt_length Poly.zero).mono (Nat.zero_le _)
  | cons ce rest ih =>
    obtain ⟨c,e⟩ := ce
    exact Poly.degLt_add
      (Poly.degLt_smul c ((air_polynomial_lower_degree p affine e).mono
        (Nat.add_le_add_right (degrees _ (List.mem_cons_self ..)) 1)))
      (ih (fun ce hc => degrees ce (List.mem_cons_of_mem _ hc)))

/-- One entry per suffix assignment: its affine AIR environment and affine
equality weight in the remaining sumcheck variable. -/
def genericAirRoundPolynomial (es : List (K × Expr)) :
    List (AirPolynomialInputs K × Poly K) → Poly K
  | [] => Poly.zero
  | (p,w)::rest => w*genericAirConstraintPolynomial p es + genericAirRoundPolynomial es rest

def genericAirRoundValue (es : List (K × Expr)) (x : K) :
    List (AirPolynomialInputs K × Poly K) → K
  | [] => 0
  | (p,w)::rest => w.eval x*genericAirConstraintValue p x es + genericAirRoundValue es x rest

theorem generic_air_round_polynomial_eval (es : List (K × Expr))
    (slices : List (AirPolynomialInputs K × Poly K)) (x : K) :
    (genericAirRoundPolynomial es slices).eval x = genericAirRoundValue es x slices := by
  induction slices with
  | nil => rfl
  | cons pw rest ih =>
    obtain ⟨p,w⟩ := pw
    simp only [genericAirRoundPolynomial, genericAirRoundValue,
      Poly.eval_add, Poly.eval_mul, generic_air_constraint_polynomial_eval, ih]

theorem generic_air_round_polynomial_degree (es : List (K × Expr))
    (slices : List (AirPolynomialInputs K × Poly K)) (d : Nat)
    (degrees : ∀ ce ∈ es, ce.2.degree ≤ d)
    (affine : ∀ pw ∈ slices, AirPolynomialAffine pw.1 ∧ pw.2.DegLt 2) :
    (genericAirRoundPolynomial es slices).DegLt (d+2) := by
  induction slices with
  | nil => exact (Poly.degLt_length Poly.zero).mono (Nat.zero_le _)
  | cons pw rest ih =>
    obtain ⟨p,w⟩ := pw
    obtain ⟨hp,hw⟩ := affine _ (List.mem_cons_self ..)
    have h := Poly.degLt_mul hw (generic_air_constraint_polynomial_degree p hp es d degrees)
    apply Poly.degLt_add
    · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
    · exact ih (fun pw hm => affine pw (List.mem_cons_of_mem _ hm))

end Ring

/-- A false round has at most d+1 distinct accepting challenges. The honest
degree premise is derived from real source expressions and concrete sums. -/
theorem generic_air_round_bad_roots {K : Type} [Lean.Grind.Field K]
    (es : List (K × Expr)) (slices : List (AirPolynomialInputs K × Poly K))
    (d : Nat) (degrees : ∀ ce ∈ es, ce.2.degree ≤ d)
    (affine : ∀ pw ∈ slices, AirPolynomialAffine pw.1 ∧ pw.2.DegLt 2)
    (sent : Poly K) (sentDegree : sent.DegLt (d+2))
    (wrong : sent.eval 0 + sent.eval 1 ≠
      genericAirRoundValue es 0 slices + genericAirRoundValue es 1 slices)
    (candidates : List K) (distinct : candidates.Nodup) :
    ArenaCore.Security.count candidates
      (fun r => sent.eval r = genericAirRoundValue es r slices) ≤ d+1 := by
  have hwrong : sent.eval 0 + sent.eval 1 ≠
      (genericAirRoundPolynomial es slices).eval 0 + (genericAirRoundPolynomial es slices).eval 1 := by
    simpa only [generic_air_round_polynomial_eval] using wrong
  have bound := instruction_round_bad_roots_degree sent (genericAirRoundPolynomial es slices)
    (d+2) sentDegree (generic_air_round_polynomial_degree es slices d degrees affine)
    hwrong candidates distinct
  simp only [generic_air_round_polynomial_eval] at bound
  omega

end NearCompression
