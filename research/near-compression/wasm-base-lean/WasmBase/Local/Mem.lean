import WasmBase.Local.Div
import WasmBase.StepMem
/-!
# Local soundness of LOAD / STORE (linear memory)

* `onehot_sum`: with one-hot flags, a flag sum (`Load.sumF`, `Store.sumF`) evaluates to the
  indicator of the selected op.
* `load_sem`: the little-endian / sign-extension arithmetic of the 12 integer loads, as the result
  limbs the LOAD chip computes from the bytes and the top bit.
* `store_bytes`: the bytes of a value given by its limbs split into checked byte pairs.
-/
namespace WasmBase.Local
open ZkFormal.Algebra WasmBase.Chips NearSpecV3.Wasm
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

/-- A fold of flag columns over distinct indices, with one-hot flags. -/
theorem fold_flags (c : Nat → Nat) (rw : Row) (fl : Nat → Nat) (k0 : Nat) :
    ∀ (l : List Nat) (acc : Expr), l.Nodup → (∀ k ∈ l, c (fl k) = if k = k0 then 1 else 0) →
      (l.foldl (fun acc k => acc + v (fl k)) acc).eval (natRow c rw) =
        acc.eval (natRow c rw) + ((if k0 ∈ l then 1 else 0 : Nat) : F) := by
  intro l
  induction l with
  | nil => intro acc _ _; simp only [List.foldl_nil, List.not_mem_nil, ite_false]; grind
  | cons k l ih =>
    intro acc hnd hone
    rw [List.nodup_cons] at hnd
    rw [List.foldl_cons, ih _ hnd.2 (fun k' hk' => hone k' (List.mem_cons_of_mem _ hk'))]
    simp only [Expr.eval_add', v, Expr.eval_col, natRow, hone k List.mem_cons_self, List.mem_cons]
    by_cases hk : k = k0
    · subst hk
      simp only [ite_true, true_or, hnd.1, ite_false]
      grind
    · have : ¬ k0 = k := fun h => hk h.symm
      simp only [hk, this, ite_false, false_or]
      grind

theorem load_sumF (c : Nat → Nat) (rw : Row) (k0 : Nat) (hk0 : k0 < 12)
    (hone : ∀ k, k < 12 → c (Load.fl k) = if k = k0 then 1 else 0) (p : Nat × Nat × Bool × Bool → Bool) :
    (Load.sumF p).eval (natRow c rw) = ((if p (Load.ops.getD k0 default) then 1 else 0 : Nat) : F) := by
  unfold Load.sumF
  rw [fold_flags c rw Load.fl k0 _ 0 (List.nodup_range.filter _)
    (fun k hk => hone k (List.mem_range.mp (List.mem_filter.mp hk).1))]
  have e : (k0 ∈ (List.range 12).filter fun k => p (Load.ops.getD k default)) ↔ p (Load.ops.getD k0 default) := by
    simp [hk0]
  by_cases hp : p (Load.ops.getD k0 default) <;> simp only [e, hp, ite_true, ite_false, Bool.false_eq_true] <;>
    simp only [Expr.eval_ofNat'] <;> grind

theorem store_sumF (c : Nat → Nat) (rw : Row) (k0 : Nat) (hk0 : k0 < 7)
    (hone : ∀ k, k < 7 → c (Store.fl k) = if k = k0 then 1 else 0) (p : Nat × Nat × Bool → Bool) :
    (Store.sumF p).eval (natRow c rw) = ((if p (Store.ops.getD k0 default) then 1 else 0 : Nat) : F) := by
  unfold Store.sumF
  rw [fold_flags c rw Store.fl k0 _ 0 (List.nodup_range.filter _)
    (fun k hk => hone k (List.mem_range.mp (List.mem_filter.mp hk).1))]
  have e : (k0 ∈ (List.range 7).filter fun k => p (Store.ops.getD k default)) ↔ p (Store.ops.getD k0 default) := by
    simp [hk0]
  by_cases hp : p (Store.ops.getD k0 default) <;> simp only [e, hp, ite_true, ite_false, Bool.false_eq_true] <;>
    simp only [Expr.eval_ofNat'] <;> grind

theorem fold_coef (c : Nat → Nat) (rw : Row) (fl g : Nat → Nat) (k0 : Nat) :
    ∀ (l : List Nat) (acc : Expr), l.Nodup → (∀ k ∈ l, c (fl k) = if k = k0 then 1 else 0) →
      (l.foldl (fun acc k => acc + Expr.c (g k) * v (fl k)) acc).eval (natRow c rw) =
        acc.eval (natRow c rw) + ((if k0 ∈ l then g k0 else 0 : Nat) : F) := by
  intro l
  induction l with
  | nil => intro acc _ _; simp only [List.foldl_nil, List.not_mem_nil, ite_false]; grind
  | cons k l ih =>
    intro acc hnd hone
    rw [List.nodup_cons] at hnd
    rw [List.foldl_cons, ih _ hnd.2 (fun k' hk' => hone k' (List.mem_cons_of_mem _ hk'))]
    simp only [Expr.eval_add', Expr.eval_mul', Expr.eval_c, v, Expr.eval_col, natRow, hone k List.mem_cons_self,
      List.mem_cons]
    by_cases hk : k = k0
    · subst hk
      simp only [ite_true, true_or, hnd.1, ite_false]
      grind
    · have : ¬ k0 = k := fun h => hk h.symm
      simp only [hk, this, ite_false, false_or]
      grind

theorem load_op_eval (c : Nat → Nat) (rw : Row) (k0 : Nat) (hk0 : k0 < 12)
    (hone : ∀ k, k < 12 → c (Load.fl k) = if k = k0 then 1 else 0) :
    Load.op.eval (natRow c rw) = (((Load.ops.getD k0 default).1 : Nat) : F) := by
  unfold Load.op
  rw [fold_coef c rw Load.fl (fun k => (Load.ops.getD k default).1) k0 _ 0 List.nodup_range
    (fun k hk => hone k (List.mem_range.mp hk))]
  simp only [List.mem_range, hk0, ite_true, Expr.eval_ofNat']; grind

theorem store_op_eval (c : Nat → Nat) (rw : Row) (k0 : Nat) (hk0 : k0 < 7)
    (hone : ∀ k, k < 7 → c (Store.fl k) = if k = k0 then 1 else 0) :
    Store.op.eval (natRow c rw) = (((Store.ops.getD k0 default).1 : Nat) : F) := by
  unfold Store.op
  rw [fold_coef c rw Store.fl (fun k => (Store.ops.getD k default).1) k0 _ 0 List.nodup_range
    (fun k hk => hone k (List.mem_range.mp hk))]
  simp only [List.mem_range, hk0, ite_true, Expr.eval_ofNat']; grind

/-- Byte `i` of a LOAD result: the loaded byte below the width, else the sign fill (signed loads,
within the result width) or 0. -/
def loadB (k : Nat) (b : Nat → Nat) (s i : Nat) : Nat :=
  if i < (Load.ops.getD k default).2.1 then b i
  else (if (Load.ops.getD k default).2.2.1 then s * 255 else 0) *
    (if i < 4 then 1 else if (Load.ops.getD k default).2.2.2 then 1 else 0)

theorem extendS_64_32 (x : Nat) (hx : x < 2 ^ 32) :
    Num.extendS 64 32 x = if 2 ^ 31 ≤ x then x + (2 ^ 64 - 2 ^ 32) else x := by
  unfold Num.extendS Num.signed
  rw [Nat.mod_eq_of_lt hx]
  split
  · rename_i h
    rw [show ((x : Int) - 2 ^ 32) = -(((2 ^ 32 - x : Nat) : Int)) by omega, wrap_neg (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rename_i h
    rw [wrap_nat (by omega)]

/-- The statement of `load_sem` for one op. -/
def LoadSem (k : Nat) : Prop :=
  ∀ (b : Nat → Nat), (∀ i, i < 8 → b i < 256) → ∀ (s low : Nat), s ≤ 1 → low < 128 →
    b ((Load.ops.getD k default).2.1 - 1) = 128 * s + low →
    vNum (loadVal (Load.ops.getD k default).1 (leVal b 0 (Load.ops.getD k default).2.1)) =
      val4 (loadB k b s 0 + 256 * loadB k b s 1) (loadB k b s 2 + 256 * loadB k b s 3)
        (loadB k b s 4 + 256 * loadB k b s 5) (loadB k b s 6 + 256 * loadB k b s 7) ∧
    vTag (loadVal (Load.ops.getD k default).1 (leVal b 0 (Load.ops.getD k default).2.1)) =
      if (Load.ops.getD k default).2.2.2 then 1 else 0

theorem load_sem0 : LoadSem 0 := by
  intro b hb s low hs hl htop
  have b0 := hb 0 (by omega); have b1 := hb 1 (by omega); have b2 := hb 2 (by omega)
  have b3 := hb 3 (by omega); have b4 := hb 4 (by omega); have b5 := hb 5 (by omega)
  have b6 := hb 6 (by omega); have b7 := hb 7 (by omega)
  simp only [Load.ops, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub] at htop ⊢
  simp only [loadB, Load.ops, List.getD_cons_zero, List.getD_cons_succ, loadVal, loadSpec, leVal, vTag, vNum,
    Num.extendS, Num.signed, Num.wrap, val4]
  simp
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;>
  first
    | omega
    | (rw [if_neg (by omega)]; omega)
    | (rw [if_pos (by omega)]; omega)

theorem load_sem1 : LoadSem 1 := by
  intro b hb s low hs hl htop
  have b0 := hb 0 (by omega); have b1 := hb 1 (by omega); have b2 := hb 2 (by omega)
  have b3 := hb 3 (by omega); have b4 := hb 4 (by omega); have b5 := hb 5 (by omega)
  have b6 := hb 6 (by omega); have b7 := hb 7 (by omega)
  simp only [Load.ops, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub] at htop ⊢
  simp only [loadB, Load.ops, List.getD_cons_zero, List.getD_cons_succ, loadVal, loadSpec, leVal, vTag, vNum,
    Num.extendS, Num.signed, Num.wrap, val4]
  simp
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;>
  first
    | omega
    | (rw [if_neg (by omega)]; omega)
    | (rw [if_pos (by omega)]; omega)

theorem load_sem2 : LoadSem 2 := by
  intro b hb s low hs hl htop
  have b0 := hb 0 (by omega); have b1 := hb 1 (by omega); have b2 := hb 2 (by omega)
  have b3 := hb 3 (by omega); have b4 := hb 4 (by omega); have b5 := hb 5 (by omega)
  have b6 := hb 6 (by omega); have b7 := hb 7 (by omega)
  simp only [Load.ops, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub] at htop ⊢
  simp only [loadB, Load.ops, List.getD_cons_zero, List.getD_cons_succ, loadVal, loadSpec, leVal, vTag, vNum,
    Num.extendS, Num.signed, Num.wrap, val4]
  simp
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;>
  first
    | omega
    | (rw [if_neg (by omega)]; omega)
    | (rw [if_pos (by omega)]; omega)

theorem load_sem3 : LoadSem 3 := by
  intro b hb s low hs hl htop
  have b0 := hb 0 (by omega); have b1 := hb 1 (by omega); have b2 := hb 2 (by omega)
  have b3 := hb 3 (by omega); have b4 := hb 4 (by omega); have b5 := hb 5 (by omega)
  have b6 := hb 6 (by omega); have b7 := hb 7 (by omega)
  simp only [Load.ops, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub] at htop ⊢
  simp only [loadB, Load.ops, List.getD_cons_zero, List.getD_cons_succ, loadVal, loadSpec, leVal, vTag, vNum,
    Num.extendS, Num.signed, Num.wrap, val4]
  simp
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;>
  first
    | omega
    | (rw [if_neg (by omega)]; omega)
    | (rw [if_pos (by omega)]; omega)

theorem load_sem4 : LoadSem 4 := by
  intro b hb s low hs hl htop
  have b0 := hb 0 (by omega); have b1 := hb 1 (by omega); have b2 := hb 2 (by omega)
  have b3 := hb 3 (by omega); have b4 := hb 4 (by omega); have b5 := hb 5 (by omega)
  have b6 := hb 6 (by omega); have b7 := hb 7 (by omega)
  simp only [Load.ops, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub] at htop ⊢
  simp only [loadB, Load.ops, List.getD_cons_zero, List.getD_cons_succ, loadVal, loadSpec, leVal, vTag, vNum,
    Num.extendS, Num.signed, Num.wrap, val4]
  simp
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;>
  first
    | omega
    | (rw [if_neg (by omega)]; omega)
    | (rw [if_pos (by omega)]; omega)

theorem load_sem5 : LoadSem 5 := by
  intro b hb s low hs hl htop
  have b0 := hb 0 (by omega); have b1 := hb 1 (by omega); have b2 := hb 2 (by omega)
  have b3 := hb 3 (by omega); have b4 := hb 4 (by omega); have b5 := hb 5 (by omega)
  have b6 := hb 6 (by omega); have b7 := hb 7 (by omega)
  simp only [Load.ops, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub] at htop ⊢
  simp only [loadB, Load.ops, List.getD_cons_zero, List.getD_cons_succ, loadVal, loadSpec, leVal, vTag, vNum,
    Num.extendS, Num.signed, Num.wrap, val4]
  simp
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;>
  first
    | omega
    | (rw [if_neg (by omega)]; omega)
    | (rw [if_pos (by omega)]; omega)

theorem load_sem6 : LoadSem 6 := by
  intro b hb s low hs hl htop
  have b0 := hb 0 (by omega); have b1 := hb 1 (by omega); have b2 := hb 2 (by omega)
  have b3 := hb 3 (by omega); have b4 := hb 4 (by omega); have b5 := hb 5 (by omega)
  have b6 := hb 6 (by omega); have b7 := hb 7 (by omega)
  simp only [Load.ops, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub] at htop ⊢
  simp only [loadB, Load.ops, List.getD_cons_zero, List.getD_cons_succ, loadVal, loadSpec, leVal, vTag, vNum,
    Num.extendS, Num.signed, Num.wrap, val4]
  simp
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;>
  first
    | omega
    | (rw [if_neg (by omega)]; omega)
    | (rw [if_pos (by omega)]; omega)

theorem load_sem7 : LoadSem 7 := by
  intro b hb s low hs hl htop
  have b0 := hb 0 (by omega); have b1 := hb 1 (by omega); have b2 := hb 2 (by omega)
  have b3 := hb 3 (by omega); have b4 := hb 4 (by omega); have b5 := hb 5 (by omega)
  have b6 := hb 6 (by omega); have b7 := hb 7 (by omega)
  simp only [Load.ops, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub] at htop ⊢
  simp only [loadB, Load.ops, List.getD_cons_zero, List.getD_cons_succ, loadVal, loadSpec, leVal, vTag, vNum,
    Num.extendS, Num.signed, Num.wrap, val4]
  simp
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;>
  first
    | omega
    | (rw [if_neg (by omega)]; omega)
    | (rw [if_pos (by omega)]; omega)

theorem load_sem8 : LoadSem 8 := by
  intro b hb s low hs hl htop
  have b0 := hb 0 (by omega); have b1 := hb 1 (by omega); have b2 := hb 2 (by omega)
  have b3 := hb 3 (by omega); have b4 := hb 4 (by omega); have b5 := hb 5 (by omega)
  have b6 := hb 6 (by omega); have b7 := hb 7 (by omega)
  simp only [Load.ops, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub] at htop ⊢
  simp only [loadB, Load.ops, List.getD_cons_zero, List.getD_cons_succ, loadVal, loadSpec, leVal, vTag, vNum,
    Num.extendS, Num.signed, Num.wrap, val4]
  simp
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;>
  first
    | omega
    | (rw [if_neg (by omega)]; omega)
    | (rw [if_pos (by omega)]; omega)

theorem load_sem9 : LoadSem 9 := by
  intro b hb s low hs hl htop
  have b0 := hb 0 (by omega); have b1 := hb 1 (by omega); have b2 := hb 2 (by omega)
  have b3 := hb 3 (by omega); have b4 := hb 4 (by omega); have b5 := hb 5 (by omega)
  have b6 := hb 6 (by omega); have b7 := hb 7 (by omega)
  simp only [Load.ops, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub] at htop ⊢
  simp only [loadB, Load.ops, List.getD_cons_zero, List.getD_cons_succ, loadVal, loadSpec, leVal, vTag, vNum,
    Num.extendS, Num.signed, Num.wrap, val4]
  simp
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;>
  first
    | omega
    | (rw [if_neg (by omega)]; omega)
    | (rw [if_pos (by omega)]; omega)

theorem load_sem10 : LoadSem 10 := by
  intro b hb s low hs hl htop
  have b0 := hb 0 (by omega); have b1 := hb 1 (by omega); have b2 := hb 2 (by omega)
  have b3 := hb 3 (by omega)
  simp only [Load.ops, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub] at htop ⊢
  simp only [loadB, Load.ops, List.getD_cons_zero, List.getD_cons_succ, loadVal, loadSpec, leVal, vTag, vNum,
    val4, ite_true, Nat.reduceMul, Nat.reduceAdd, Nat.zero_add]
  rw [extendS_64_32 _ (by omega)]
  simp
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
  · rw [if_neg (by omega)]; omega
  · rw [if_pos (by omega)]; omega

theorem load_sem11 : LoadSem 11 := by
  intro b hb s low hs hl htop
  have b0 := hb 0 (by omega); have b1 := hb 1 (by omega); have b2 := hb 2 (by omega)
  have b3 := hb 3 (by omega); have b4 := hb 4 (by omega); have b5 := hb 5 (by omega)
  have b6 := hb 6 (by omega); have b7 := hb 7 (by omega)
  simp only [Load.ops, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub] at htop ⊢
  simp only [loadB, Load.ops, List.getD_cons_zero, List.getD_cons_succ, loadVal, loadSpec, leVal, vTag, vNum,
    Num.extendS, Num.signed, Num.wrap, val4]
  simp
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;>
  first
    | omega
    | (rw [if_neg (by omega)]; omega)
    | (rw [if_pos (by omega)]; omega)

/-- **Load semantics**: the value a load pushes is the LOAD chip's result (little-endian bytes and
sign fill), and its tag is `is64`. -/
theorem load_sem (k : Nat) (hk : k < 12) : LoadSem k := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11
    by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact load_sem0
  · exact load_sem1
  · exact load_sem2
  · exact load_sem3
  · exact load_sem4
  · exact load_sem5
  · exact load_sem6
  · exact load_sem7
  · exact load_sem8
  · exact load_sem9
  · exact load_sem10
  · exact load_sem11

/-- A value given by four 16-bit limbs encodes to those limbs. -/
theorem enc_limbs {v : Val} {r0 r1 r2 r3 : Nat} (h0 : r0 < 65536) (h1 : r1 < 65536) (h2 : r2 < 65536)
    (h3 : r3 < 65536) (hv : vNum v = val4 r0 r1 r2 r3) (sp sl tp : Nat) :
    enc sp sl v tp = ⟨sp, sl, vTag v, r0, r1, r2, r3, tp⟩ := by
  simp only [enc, hv, val4, Msg.mk.injEq, true_and, and_true, Nat.reducePow]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The bytes of a value given by limbs that are checked byte pairs. -/
theorem store_bytes (vb : Nat → Nat) (hvb : ∀ i, i < 8 → vb i < 256) (i : Nat) (hi : i < 8) :
    vb i = val4 (vb 0 + 256 * vb 1) (vb 2 + 256 * vb 3) (vb 4 + 256 * vb 5) (vb 6 + 256 * vb 7) / 256 ^ i % 256 := by
  have b0 := hvb 0 (by omega); have b1 := hvb 1 (by omega); have b2 := hvb 2 (by omega)
  have b3 := hvb 3 (by omega); have b4 := hvb 4 (by omega); have b5 := hvb 5 (by omega)
  have b6 := hvb 6 (by omega); have b7 := hvb 7 (by omega)
  simp only [val4, Nat.reducePow]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

end WasmBase.Local
