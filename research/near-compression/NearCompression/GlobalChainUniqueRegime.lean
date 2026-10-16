import NearCompression.IndexedUniqueExtraction
import NearCompression.GlobalChainWeightBounds

/-! Actual transcript cap/mass invariants instantiate the newly proved
weighted extraction theorem at EVERY halving stage. No extraction assumption.
Field/domain certificates, message degree, and regime inequality are explicit. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

theorem halving_degree_product (degrees : Nat → Nat) (stage : Nat)
    (halves : ∀ j<stage,degrees j=2*degrees (j+1)) :
    2^stage*degrees stage=degrees 0 := by
  induction stage with
  | zero => simp
  | succ i ih =>
    have prior := ih (fun j hj => halves j (by omega))
    have step := halves i (by omega)
    rw [step] at prior
    rw [Nat.pow_succ]
    grind

/-- One stage's explicit concentration bad-event count, directly for the
actual oracle-indexed fold and transcript-generated consistency weights. -/
theorem global_chain_unique_bad_count {K : Type} [Field K]
    (sample : List K) (sampleDistinct : sample.Nodup)
    (N0 : Nat) (sizes degrees : Nat → Nat) (roots challenges : Nat → K)
    (oracles : Nat → Nat → K) (stage T : Nat)
    (initial : sizes 0=N0) (positive : ∀ j≤stage,0<sizes j)
    (sizeHalves : ∀ j≤stage,sizes j=2*sizes (j+1))
    (degreeHalves : ∀ j≤stage,degrees j=2*degrees (j+1))
    (pointInjective : ∀ a<sizes (stage+1),∀ b<sizes (stage+1),
      roots (stage+1)^a=roots (stage+1)^b → a=b)
    (weights : List K) (w0 w1 : K) (sent : Poly K) (sentDegree : sent.DegLt 3)
    (regime : 2*N0+degrees 0<3*T) :
    count sample (indexedFoldBad (sizes (stage+1)) (degrees (stage+1)) T
      (globalChainWeight (List.range N0) sizes (globalRSChainCheck sizes roots challenges oracles) stage)
      (oracles stage) (roots stage) (roots (stage+1)) weights w0 w1 sent)≤max (sizes (stage+1)) 2 := by
  let check := globalRSChainCheck sizes roots challenges oracles
  have cap := global_chain_projected_cap N0 sizes check stage initial sizeHalves
  have mass := global_chain_projected_mass_bound N0 sizes check stage positive sizeHalves
  have product := halving_degree_product degrees (stage+1) (fun j hj => degreeHalves j (by omega))
  have degreeBound : 2^(stage+1)*(degrees (stage+1)-1)≤degrees 0 := by
    rw [←product]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  apply indexed_unique_bad_count sample sampleDistinct (sizes (stage+1)) (degrees (stage+1)) T
    (2^(stage+1)) _ _ _ _ weights w0 w1 sent pointInjective cap sentDegree
  omega

end NearCompression
