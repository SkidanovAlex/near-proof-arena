import NearCompression.GenericPackedGridCounting
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- The whole ordered residual vector, padded with zeros. This definition
has no output-challenge argument in its input vector. -/
def recursiveResidualEval (n : Nat) (residuals : List K) (point : List K) : K :=
  packedGridEval n (fun i => residuals.getD i 0) point

theorem recursive_residual_complete (n : Nat) (residuals : List K)
    (zero : ∀ x∈residuals,x=0) (point : List K) :
    recursiveResidualEval n residuals point=0 := by
  have values : (fun i => residuals.getD i 0)=(fun _ => (0:K)) := by
    funext i
    by_cases hi : i<residuals.length
    · simpa [List.getD,hi] using zero _ (List.getElem_mem hi)
    · simp [List.getD,hi]
  unfold recursiveResidualEval packedGridEval
  rw [values]
  exact generic_row_mle_zero n _

/-- Conditional ideal counting bound for the complete fixed vector. This
is not Fiat--Shamir soundness, nor a claim that GKR acceptance equals the
actual residual evaluation without its own input-binding/soundness proof. -/
theorem recursive_residual_false_zero_count (n : Nat) (residuals : List K)
    (fits : residuals.length≤2^(n+1)) (lane : Nat) (valid : lane<residuals.length)
    (wrong : residuals[lane]≠0) (sample : List K) (distinct : sample.Nodup) :
    count (packedGrid sample (n+1))
      (fun point => recursiveResidualEval (n+1) residuals point=0) ≤
      (n+1)*sample.length^n := by
  have bound := packed_claim_grid_bad_count n lane (fun i => residuals.getD i 0)
    (fun _ => (0:K)) (by omega) (by simpa [List.getD,valid] using wrong)
    sample distinct
  have zero (point : List K) : packedGridEval (n+1) (fun _ => (0:K)) point=0 :=
    generic_row_mle_zero _ _
  simpa only [recursiveResidualEval,zero] using bound
end NearCompression
