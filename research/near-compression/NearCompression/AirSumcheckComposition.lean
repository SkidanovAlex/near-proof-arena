import NearCompression.AirPolynomialLowering
import NearCompression.InstructionSumcheckSoundness

/-! Checked composition of the independent compiler and round-algebra lanes.
This is a single weighted constraint; summing rows, random batching, adaptive
rounds, authenticated evaluations and the quantum transform remain separate. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ArenaCore.Security

/-- An affine equality weight times a quadratic source AIR expression is cubic
in a sumcheck coordinate, under the shared affine environment contract. -/
theorem air_sumcheck_weighted_degree {K : Type} [Lean.Grind.CommRing K]
    (inputs : AirPolynomialInputs K) (affine : AirPolynomialAffine inputs)
    (e : Expr) (degree : e.degree ≤ 2) (weight : Poly K)
    (weightDegree : weight.DegLt 2) :
    (weight * airPolynomialLower inputs e).DegLt 4 := by
  have hd : (airPolynomialLower inputs e).DegLt 3 :=
    (air_polynomial_lower_degree inputs affine e).mono (by omega)
  exact Poly.degLt_mul weightDegree hd

/-- The compiler's computed polynomial supplies the honest side of the
round-root bound. No honest-degree assumption is duplicated at this boundary. -/
theorem air_sumcheck_weighted_bad_roots {K : Type} [Lean.Grind.Field K]
    (inputs : AirPolynomialInputs K) (affine : AirPolynomialAffine inputs)
    (e : Expr) (degree : e.degree ≤ 2) (weight : Poly K)
    (weightDegree : weight.DegLt 2) (sent : Poly K) (sentDegree : sent.DegLt 4)
    (wrong : sent.eval 0 + sent.eval 1 ≠
      (weight * airPolynomialLower inputs e).eval 0 +
      (weight * airPolynomialLower inputs e).eval 1)
    (candidates : List K) (distinct : candidates.Nodup) :
    count candidates (fun r => sent.eval r = (weight * airPolynomialLower inputs e).eval r) ≤ 3 :=
  instruction_round_bad_roots sent _ sentDegree
    (air_sumcheck_weighted_degree inputs affine e degree weight weightDegree) wrong candidates distinct

end NearCompression
