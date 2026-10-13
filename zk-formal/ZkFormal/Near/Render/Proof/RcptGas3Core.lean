import ZkFormal.Near.Render.Proof.RcptNat

/-! Declarations of `ZkFormal.Near.Render.Proof.RcptGas3` split out (unchanged names and statements) so that
  importers needing only these do not pull in the rest of the module (certificate pruning). -/

/-!
# ZkFormal.Near.Render.Proof.RcptGas3 — `cGas`: `burnt = G·p`, `ramt = G·surplus`, running tokens;
`gasFam : FamOk cGas`
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false

namespace RcptP

open RcptGen

/-- The convolution by `G` on row `i`, with the delay line `[j < i] v (i − 1 − j)`. -/
theorem convG_row (v : Nat → Nat) (i : Nat) : conv (Rcpt.G_LE.take 5) v i =
    196 * v i + 164 * (if 0 < i then v (i - 1 - 0) else 0) + 183 * (if 1 < i then v (i - 1 - 1) else 0) +
      246 * (if 2 < i then v (i - 1 - 2) else 0) + 51 * (if 3 < i then v (i - 1 - 3) else 0) := by
  rw [conv_eq]
  simp only [sumR, Rcpt.G_LE, List.take, List.length_cons, List.length_nil, List.getD_cons_zero,
    List.getD_cons_succ, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i by omega) with rfl | rfl | rfl | rfl | h
  · simp
  · simp
  · simp
  · simp
  · simp only [show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega,
      show 0 < i by omega, show 1 < i by omega, show 2 < i by omega, show 3 < i by omega, ↓reduceIte,
      show i - 1 - 0 = i - 1 by omega, show i - 1 - 1 = i - 2 by omega, show i - 1 - 2 = i - 3 by omega,
      show i - 1 - 3 = i - 4 by omega]
    omega

end RcptP
end ZkFormal.Near.Render
