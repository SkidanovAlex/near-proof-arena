import NearCompression.JointPCSParameterArithmetic
namespace NearCompression

/-- Literal count formulas with S field-sample values, H history coordinates,
C PCS coordinates, N domain points, k queries, A folding-round numerator and
R=T-1. The scale factor S from the theorem is included only in the denominator. -/
def jointPCSNearBudget (S H C N k A R : Nat) : Nat :=
  S^H*((2*C)*S^C*(S^C*N^k)+S^C*(A*S^C*N^k+S^(C+1)*R^k))

def jointPCSFarBudget (S H C N k A R : Nat) : Nat :=
  (H+C)*max N 2*S^(H+C-1)*(S^C*N^k)*S+
    S^(H+C)*(A*S^C*N^k+S^(C+1)*R^k)

theorem joint_pcs_near_factor (S H C N k A R : Nat) :
    jointPCSNearBudget S H C N k A R=
      S^(H+2*C)*(((2*C)+A)*N^k+S*R^k) := by
  unfold jointPCSNearBudget
  rw [show H+2*C=H+(C+C) by omega]
  simp only [Nat.pow_add,Nat.pow_succ,Nat.mul_add,Nat.add_assoc,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

theorem joint_pcs_far_factor (S H C N k A R : Nat) (dimension : 0<H+C) :
    jointPCSFarBudget S H C N k A R=
      S^(H+2*C)*(((H+C)*max N 2+A)*N^k+S*R^k) := by
  have power : S^(H+C-1)*S=S^(H+C) := by
    rw [←Nat.pow_succ]
    congr 1
    omega
  unfold jointPCSFarBudget
  have term : (H+C)*max N 2*S^(H+C-1)*(S^C*N^k)*S=
      (H+C)*max N 2*S^(H+C)*(S^C*N^k) := by
    rw [show (H+C)*max N 2*S^(H+C-1)*(S^C*N^k)*S=
      (H+C)*max N 2*(S^(H+C-1)*S)*(S^C*N^k) by
        simp only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm],power]
  rw [term,show H+2*C=H+(C+C) by omega]
  simp only [Nat.pow_add,Nat.pow_succ,Nat.add_mul,Nat.mul_add,Nat.add_assoc,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

/-- Exact factorization of the maximum, not a union-bound replacement. -/
theorem joint_pcs_merged_factor (S H C N k A R : Nat) (dimension : 0<H+C) :
    max (jointPCSNearBudget S H C N k A R) (jointPCSFarBudget S H C N k A R)=
      S^(H+2*C)*((A+max (2*C) ((H+C)*max N 2))*N^k+S*R^k) := by
  rw [joint_pcs_near_factor,joint_pcs_far_factor S H C N k A R dimension,
    Nat.mul_max_mul_left,Nat.add_max_add_right,Nat.mul_max_mul_right,Nat.add_max_add_right]
  rw [Nat.add_comm (max (2*C) ((H+C)*max N 2)) A]

/-- The normalized integer target test is equivalent to the original count
budget divided by the exact experiment mass and scale. S must be positive;
no division by zero or approximate logarithm is used. -/
theorem joint_pcs_normalized_target (S H C N k A R bits : Nat)
    (samplePositive : 0<S) (dimension : 0<H+C) :
    2^bits*max (jointPCSNearBudget S H C N k A R) (jointPCSFarBudget S H C N k A R)≤
      S^(H+2*C+1)*N^k ↔
    2^bits*((A+max (2*C) ((H+C)*max N 2))*N^k+S*R^k)≤S*N^k := by
  rw [joint_pcs_merged_factor S H C N k A R dimension,Nat.pow_succ]
  have lhs : 2^bits*(S^(H+2*C)*((A+max (2*C) ((H+C)*max N 2))*N^k+S*R^k))=
      S^(H+2*C)*(2^bits*((A+max (2*C) ((H+C)*max N 2))*N^k+S*R^k)) := by
    simp only [Nat.mul_comm,Nat.mul_left_comm]
  rw [lhs,Nat.mul_assoc]
  exact Nat.mul_le_mul_left_iff (Nat.pow_pos samplePositive)

/-- The concrete kernel-tested Boolean screen is equivalent to the original
merged count-budget target for the retained geometry, at any extension degree,
bit target and query count. This remains an arithmetic correspondence. -/
theorem literal193_original_merged_target (extension bits queries : Nat) :
    2^bits*max (jointPCSNearBudget (2013265921^extension) 43 12 16384 queries 16380 12288)
      (jointPCSFarBudget (2013265921^extension) 43 12 16384 queries 16380 12288)≤
      (2013265921^extension)^(43+2*12+1)*16384^queries ↔
    literal193MergedBoundMeets extension bits queries=true := by
  rw [joint_pcs_normalized_target (2013265921^extension) 43 12 16384 queries 16380 12288 bits
    (Nat.pow_pos (by decide)) (by decide)]
  simp only [literal193MergedBoundMeets,decide_eq_true_eq]
  rfl

end NearCompression
