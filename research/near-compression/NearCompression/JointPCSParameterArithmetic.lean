import NearCompression.GKRConcretePCSCount
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace NearCompression

/-- Arithmetic only for the retained 193-instruction geometry: N=16384,
C=12, history=43, joint dimension=55, and T-1=12288. This does not construct
an extension field or prove native verifier/theorem correspondence. -/
def literal193MergedChallengeNumerator : Nat :=
  ((List.range 12).map (fun i => max (16384/2^(i+1)) 2)).sum+max (2*12) (55*16384)

def literal193MergedBoundMeets (extension bits queries : Nat) : Bool :=
  decide (2^bits*(literal193MergedChallengeNumerator*16384^queries+
    2013265921^extension*12288^queries)≤2013265921^extension*16384^queries)

/-- Exact coefficient and challenge-only obstructions. Failure of an upper
bound to certify a target is not a cryptanalytic lower bound. -/
theorem joint_pcs_challenge_arithmetic :
    literal193MergedChallengeNumerator=917500 ∧
    2013265921^4<917500*2^128 ∧
    2013265921^8<917500*2^256 := by decide +kernel

/-- Adjacent query counts bracket the target using exact integer arithmetic.
These are conditional ideal PCS component targets, not full/PQ profiles. -/
theorem joint_pcs_query_arithmetic :
    literal193MergedBoundMeets 8 128 308=false ∧
    literal193MergedBoundMeets 8 128 309=true ∧
    literal193MergedBoundMeets 8 192 462=false ∧
    literal193MergedBoundMeets 8 192 463=true ∧
    literal193MergedBoundMeets 12 256 616=false ∧
    literal193MergedBoundMeets 12 256 617=true := by decide +kernel

end NearCompression
