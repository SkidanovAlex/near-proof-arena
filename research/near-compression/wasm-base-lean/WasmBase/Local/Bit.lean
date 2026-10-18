import WasmBase.Local.Add
/-!
# Local soundness of BIT (i32/i64 and, or, xor)

The byte facts come from the BYTE lookups (`[kind, ab_k, bb_k, rb_k]` is a BYTE table row, so
`ab_k, bb_k < 256` and `rb_k = byteF kind ab_k bb_k`).
-/
namespace WasmBase.Local
open ZkFormal.Algebra WasmBase.Chips NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

theorem bit_sound (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P)
    (hc : ∀ e ∈ Bit.constraints, e.eval (natRow c rw) = 0)
    (hact : c Bit.fAnd + c Bit.fOr + c Bit.fXor = 1)
    (hlk : ∀ k, k < 8 → c (Bit.ab + k) < 256 ∧ c (Bit.bb + k) < 256 ∧
      c (Bit.rb + k) = byteF (c Bit.fAnd + 2 * c Bit.fOr + 3 * c Bit.fXor) (c (Bit.ab + k)) (c (Bit.bb + k))) :
    (c Bit.is64 = 0 ∨ c Bit.is64 = 1) ∧
    (c Bit.is64 = 0 → ∀ k, 4 ≤ k → k < 8 → c (Bit.ab + k) = 0 ∧ c (Bit.bb + k) = 0 ∧ c (Bit.rb + k) = 0) ∧
    Num.binop (32 + 32 * c Bit.is64) (7 + c Bit.fOr + 2 * c Bit.fXor)
      (val8 fun k => c (Bit.ab + k)) (val8 fun k => c (Bit.bb + k)) =
      some (val8 fun k => c (Bit.rb + k)) := by
  simp only [Bit.constraints, List.forall_mem_append, List.forall_mem_flatMap, List.mem_range,
    List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, Chips.bool, v, Expr.eval_add',
    Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', Expr.eval_col, natRow] at hc
  obtain ⟨⟨bA, bO, bX, b64, _, _, _⟩, hup⟩ := hc
  have b64' := bool_nat (hP _) b64
  have hA := bool_nat (hP _) bA; have hO := bool_nat (hP _) bO; have hX := bool_nat (hP _) bX
  -- upper bytes of i32 operands/result are zero
  have hupper : c Bit.is64 = 0 → ∀ k, 4 ≤ k → k < 8 →
      c (Bit.ab + k) = 0 ∧ c (Bit.bb + k) = 0 ∧ c (Bit.rb + k) = 0 := by
    intro h0 k hk1 hk2
    have hz := hup (k - 4) (by omega)
    simp only [h0,
      show Bit.ab + 4 + (k - 4) = Bit.ab + k by unfold Bit.ab; omega,
      show Bit.bb + 4 + (k - 4) = Bit.bb + k by unfold Bit.bb; omega,
      show Bit.rb + 4 + (k - 4) = Bit.rb + k by unfold Bit.rb; omega] at hz
    exact ⟨zero_of_sel0 (hP _) hz.1, zero_of_sel0 (hP _) hz.2.1, zero_of_sel0 (hP _) hz.2.2⟩
  refine ⟨b64', hupper, ?_⟩
  have hab := fun k hk => (hlk k hk).1
  have hbb := fun k hk => (hlk k hk).2.1
  have h8 : (256 : Nat) = 2 ^ 8 := rfl
  rcases (show (c Bit.fAnd = 1 ∧ c Bit.fOr = 0 ∧ c Bit.fXor = 0) ∨ (c Bit.fAnd = 0 ∧ c Bit.fOr = 1 ∧ c Bit.fXor = 0) ∨
      (c Bit.fAnd = 0 ∧ c Bit.fOr = 0 ∧ c Bit.fXor = 1) by omega) with ⟨a1, o0, x0⟩ | ⟨a0, o1, x0⟩ | ⟨a0, o0, x1⟩
  · have hr : ∀ k, k < 8 → c (Bit.rb + k) = c (Bit.ab + k) &&& c (Bit.bb + k) := by
      intro k hk; rw [(hlk k hk).2.2, a1, o0, x0]; simp [byteF]
    rcases b64' with w | w <;> simp only [w, a1, o0, x0, Num.binop] <;>
    · congr 1
      exact val8_byteop (· && ·) (· &&& ·) (fun x y i => Nat.testBit_and x y i) _ _ _
        (fun k hk => h8 ▸ hab k hk) (fun k hk => h8 ▸ hbb k hk) hr
        (fun k hk => and_byte (h8 ▸ hab k hk))
  · have hr : ∀ k, k < 8 → c (Bit.rb + k) = c (Bit.ab + k) ||| c (Bit.bb + k) := by
      intro k hk; rw [(hlk k hk).2.2, a0, o1, x0]; simp [byteF]
    rcases b64' with w | w <;> simp only [w, a0, o1, x0, Num.binop] <;>
    · congr 1
      exact val8_byteop (· || ·) (· ||| ·) (fun x y i => Nat.testBit_or x y i) _ _ _
        (fun k hk => h8 ▸ hab k hk) (fun k hk => h8 ▸ hbb k hk) hr
        (fun k hk => or_byte (h8 ▸ hab k hk) (h8 ▸ hbb k hk))
  · have hr : ∀ k, k < 8 → c (Bit.rb + k) = c (Bit.ab + k) ^^^ c (Bit.bb + k) := by
      intro k hk; rw [(hlk k hk).2.2, a0, o0, x1]; simp [byteF]
    rcases b64' with w | w <;> simp only [w, a0, o0, x1, Num.binop] <;>
    · congr 1
      exact val8_byteop (fun a b => a ^^ b) (· ^^^ ·) (fun x y i => Nat.testBit_xor x y i) _ _ _
        (fun k hk => h8 ▸ hab k hk) (fun k hk => h8 ▸ hbb k hk) hr
        (fun k hk => xor_byte (h8 ▸ hab k hk) (h8 ▸ hbb k hk))

end WasmBase.Local
