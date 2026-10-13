import ZkFormal.Near.Extract.RcptCount
import ZkFormal.Near.Extract.RcptChain

/-! Declarations of `ZkFormal.Near.Extract.RcptArith` split out (unchanged names and statements) so that
  importers needing only these do not pull in the rest of the module (certificate pruning). -/

/-!
# ZkFormal.Near.Extract.RcptArith — the arithmetic facts of a receipt (`RcptV.Wf.arith`)
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

theorem leN'_rows (f : Nat → Nat) (h : ∀ k, k < 16 → f k < 256) :
    leN' ((List.range 16).map f) = sumL f 16 := by
  rw [leN', le256_eq_leNat _ (fun y hy => by
    simp only [List.mem_map, List.mem_range] at hy; obtain ⟨k, hk, rfl⟩ := hy; exact h k hk), le256_map_range]

theorem bytes_rows (f : Nat → Nat) (h : Bytes8 ((List.range 16).map f)) : ∀ k, k < 16 → f k < 256 :=
  fun k hk => h _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)

theorem two128 : NearSpec.Params.two128 = 256 ^ 16 := by decide

theorem sumL16_lt (f : Nat → Nat) (h : ∀ k, k < 16 → f k < 256) : sumL f 16 < NearSpec.Params.two128 := by
  rw [two128]; exact sumL_lt f 16 h

theorem sumL_max (f : Nat → Nat) : ∀ L, (∀ j, j < L → f j ≤ 255) → sumL f L + 1 ≤ 256 ^ L := by
  intro L
  induction L with
  | zero => intro _; simp [sumL]
  | succ L ih =>
    intro hf
    have i1 := ih (fun j hj => hf j (by omega))
    have m1 : 256 ^ L * f L ≤ 256 ^ L * 255 := Nat.mul_le_mul_left _ (hf L (by omega))
    simp only [sumL, Nat.pow_succ]; omega

theorem sumL_max2 (f : Nat → Nat) : ∀ L, (∀ j, j < L → f j ≤ 255) → ∀ k, k < L → f k ≤ 254 →
    sumL f L + 2 ≤ 256 ^ L := by
  intro L
  induction L with
  | zero => intro _ k hk; omega
  | succ L ih =>
    intro hf k hk hfk
    have p1 : 0 < 256 ^ L := Nat.pow_pos (by omega)
    simp only [sumL, Nat.pow_succ]
    rcases Nat.lt_or_ge k L with h1 | h1
    · have i1 := ih (fun j hj => hf j (by omega)) k h1 hfk
      have m1 : 256 ^ L * f L ≤ 256 ^ L * 255 := Nat.mul_le_mul_left _ (hf L (by omega))
      omega
    · have : k = L := by omega
      subst this
      have i1 := sumL_max f k (fun j hj => hf j (by omega))
      have m1 : 256 ^ k * f k ≤ 256 ^ k * 254 := Nat.mul_le_mul_left _ hfk
      omega

theorem sumL16_notmax (f : Nat → Nat) (h : ∀ k, k < 16 → f k < 256) (k : Nat) (hk : k < 16) (hne : f k ≠ 255) :
    sumL f 16 < NearSpec.Params.u128Max := by
  have := sumL_max2 f 16 (fun j hj => Nat.le_of_lt_succ (h j hj)) k hk (by have := h k hk; omega)
  have e : NearSpec.Params.u128Max + 1 = 256 ^ 16 := by decide
  omega

end ZkFormal.Near.RcptProof
