namespace NearCompression

/-- With N=4D, unique-decoding recovery needs agreement at least 5/8 of N. -/
theorem rate_four_unique_separation (D T : Nat) (threshold : T≤4*D) :
    2*(4*D-T)+D≤4*D ↔ 5*D≤2*T := by omega

theorem rate_four_unique_minimum (D T : Nat) (threshold : T≤4*D) :
    2*(4*D-T)+D≤4*D ↔ (5*D+1)/2≤T := by omega

/-- Strict finite tensor extraction condition; integer rounding matters at
T=3D. This is an arithmetic side condition, not acceptance-to-proximity. -/
theorem rate_four_far_minimum (D T : Nat) (positive : 0<D) :
    2*(4*D)+D-1<3*T ↔ 3*D≤T := by omega

/-- The far-extraction threshold already implies near-case separation. -/
theorem rate_four_joint_minimum (D T : Nat) (positive : 0<D) (threshold : T≤4*D) :
    (2*(4*D-T)+D≤4*D ∧ 2*(4*D)+D-1<3*T) ↔ 3*D≤T := by omega
end NearCompression
