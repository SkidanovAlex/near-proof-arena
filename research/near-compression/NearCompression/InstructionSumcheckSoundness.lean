import ZkFormal.Algebra.PolyLemmas
import ZkFormal.Algebra.PolyRoots

/-! Deterministic sumcheck round soundness over an arbitrary field. A false
Boolean-sum claim forces a nonzero difference polynomial, so only a bounded
number of distinct challenge values can conceal the discrepancy. No sampling,
Fiat–Shamir, commitment, or quantum-security assumptions are introduced here. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

/-- A discrepancy in the claimed Boolean sum is a concrete witness that the
sent and honest polynomials differ. -/
theorem instruction_round_difference_nonzero {K : Type} [Field K]
    (sent honest : Poly K)
    (wrong : sent.eval 0 + sent.eval 1 ≠ honest.eval 0 + honest.eval 1) :
    ¬ (sent-honest).IsZero := by
  intro zero
  have h0 := Poly.eval_of_isZero zero (0 : K)
  have h1 := Poly.eval_of_isZero zero (1 : K)
  rw [Poly.eval_sub] at h0 h1
  apply wrong
  grind

/-- Degree-generic round bound. `D` is a strict degree bound, so this also
handles the impossible degree-zero discrepancy without truncated subtraction. -/
theorem instruction_round_bad_roots_degree {K : Type} [Field K]
    (sent honest : Poly K) (D : Nat)
    (sentDegree : sent.DegLt D) (honestDegree : honest.DegLt D)
    (wrong : sent.eval 0 + sent.eval 1 ≠ honest.eval 0 + honest.eval 1)
    (candidates : List K) (distinct : candidates.Nodup) :
    count candidates (fun r => sent.eval r=honest.eval r)+1≤D := by
  have nonzero := instruction_round_difference_nonzero sent honest wrong
  have degree := Poly.degLt_sub sentDegree honestDegree
  have roots := PolyRoots.cardRootsLe_of polyEval polyDeg quotFacts isZeroEval
    K (sent-honest) D candidates nonzero degree distinct
  have subset : count candidates (fun r => sent.eval r=honest.eval r)≤
      count candidates (fun r => (sent-honest).eval r=0) := by
    apply count_mono
    intro r eq
    rw [Poly.eval_sub,eq]
    grind
  omega

/-- The executable instruction experiment sends four coefficients per round.
For polynomials of degree at most three, at most three distinct challenges
can make a round with a false Boolean sum agree with the honest polynomial. -/
theorem instruction_round_bad_roots {K : Type} [Field K]
    (sent honest : Poly K)
    (sentDegree : sent.DegLt 4) (honestDegree : honest.DegLt 4)
    (wrong : sent.eval 0 + sent.eval 1 ≠ honest.eval 0 + honest.eval 1)
    (candidates : List K) (distinct : candidates.Nodup) :
    count candidates (fun r => sent.eval r=honest.eval r)≤3 := by
  have bound := instruction_round_bad_roots_degree sent honest 4 sentDegree honestDegree wrong candidates distinct
  omega

end NearCompression
