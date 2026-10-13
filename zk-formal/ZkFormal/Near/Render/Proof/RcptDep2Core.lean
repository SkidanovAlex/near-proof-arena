import ZkFormal.Near.Render.Proof.RcptNat

/-! Declarations of `ZkFormal.Near.Render.Proof.RcptDep2` split out (unchanged names and statements) so that
  importers needing only these do not pull in the rest of the module (certificate pruning). -/

/-!
# ZkFormal.Near.Render.Proof.RcptDep2 — `cDep` on a `DEP` row: `aft`, `tot`, `q`, `tot − q`
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false

namespace RcptP

open RcptGen

theorem convS_row (v : Nat → Nat) (i : Nat) : conv Rcpt.S_LE v i =
    232 * (if 2 ≤ i then v (i - 2) else 0) + 137 * (if 3 ≤ i then v (i - 3) else 0) +
      4 * (if 4 ≤ i then v (i - 4) else 0) + 35 * (if 5 ≤ i then v (i - 5) else 0) +
      199 * (if 6 ≤ i then v (i - 6) else 0) + 138 * (if 7 ≤ i then v (i - 7) else 0) := by
  rw [conv_eq]
  simp only [sumR, Rcpt.S_LE, List.length_cons, List.length_nil, List.getD_cons_zero, List.getD_cons_succ]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ 7 ≤ i by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  any_goals simp
  all_goals simp only [show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega,
    show 5 ≤ i by omega, show 6 ≤ i by omega, show 7 ≤ i by omega, show 0 ≤ i by omega, ↓reduceIte]
  all_goals omega

end RcptP
end ZkFormal.Near.Render
