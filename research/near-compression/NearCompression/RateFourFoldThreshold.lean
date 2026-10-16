import NearCompression.RateFourRepresentativeThreshold
namespace NearCompression

/-- The existing folding concentration theorem uses a stricter inequality
than tensor reconstruction, hence the extra one at rate four. -/
theorem rate_four_fold_minimum (D T : Nat) :
    2*(4*D)+D<3*T ↔ 3*D+1≤T := by omega

theorem rate_four_complete_regime (D T : Nat) (positive : 0<D) (threshold : T≤4*D) :
    (2*(4*D-T)+D≤4*D ∧ 2*(4*D)+D-1<3*T ∧ 2*(4*D)+D<3*T) ↔ 3*D+1≤T := by omega
end NearCompression
