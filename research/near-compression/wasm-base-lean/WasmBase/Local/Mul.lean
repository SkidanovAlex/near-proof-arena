import WasmBase.Local.Add
/-!
# Local soundness of MUL (i32/i64 mul, byte limbs)

Byte ranges come from the BYTE pair-range lookups, carry ranges from RANGE16.
-/
namespace WasmBase.Local
open ZkFormal.Algebra WasmBase.Chips NearSpecV3.Wasm
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000


/-- Schoolbook product of byte vectors with carries (8 limbs). -/
theorem mul8_key (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 r0 r1 r2 r3 r4 r5 r6 r7 c0 c1 c2 c3 c4 c5 c6 c7 : Nat)
    (E0 : a0 * b0 = r0 + 256 * c0) (E1 : a0 * b1 + a1 * b0 + c0 = r1 + 256 * c1) (E2 : a0 * b2 + a1 * b1 + a2 * b0 + c1 = r2 + 256 * c2) (E3 : a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 + c2 = r3 + 256 * c3) (E4 : a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0 + c3 = r4 + 256 * c4) (E5 : a0 * b5 + a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1 + a5 * b0 + c4 = r5 + 256 * c5) (E6 : a0 * b6 + a1 * b5 + a2 * b4 + a3 * b3 + a4 * b2 + a5 * b1 + a6 * b0 + c5 = r6 + 256 * c6) (E7 : a0 * b7 + a1 * b6 + a2 * b5 + a3 * b4 + a4 * b3 + a5 * b2 + a6 * b1 + a7 * b0 + c6 = r7 + 256 * c7) :
    (a0 + 256 * a1 + 2 ^ 16 * a2 + 2 ^ 24 * a3 + 2 ^ 32 * a4 + 2 ^ 40 * a5 + 2 ^ 48 * a6 + 2 ^ 56 * a7) * (b0 + 256 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3 + 2 ^ 32 * b4 + 2 ^ 40 * b5 + 2 ^ 48 * b6 + 2 ^ 56 * b7) = (r0 + 256 * r1 + 2 ^ 16 * r2 + 2 ^ 24 * r3 + 2 ^ 32 * r4 + 2 ^ 40 * r5 + 2 ^ 48 * r6 + 2 ^ 56 * r7) + 2 ^ 64 * (c7 + 1 * (a1 * b7) + 1 * (a2 * b6) + 256 * (a2 * b7) + 1 * (a3 * b5) + 256 * (a3 * b6) + 65536 * (a3 * b7) + 1 * (a4 * b4) + 256 * (a4 * b5) + 65536 * (a4 * b6) + 16777216 * (a4 * b7) + 1 * (a5 * b3) + 256 * (a5 * b4) + 65536 * (a5 * b5) + 16777216 * (a5 * b6) + 4294967296 * (a5 * b7) + 1 * (a6 * b2) + 256 * (a6 * b3) + 65536 * (a6 * b4) + 16777216 * (a6 * b5) + 4294967296 * (a6 * b6) + 1099511627776 * (a6 * b7) + 1 * (a7 * b1) + 256 * (a7 * b2) + 65536 * (a7 * b3) + 16777216 * (a7 * b4) + 4294967296 * (a7 * b5) + 1099511627776 * (a7 * b6) + 281474976710656 * (a7 * b7)) := by
  grind

/-- 4-limb version (i32: upper bytes zero). -/
theorem mul4_key (a0 a1 a2 a3 b0 b1 b2 b3 r0 r1 r2 r3 c0 c1 c2 c3 : Nat)
    (E0 : a0 * b0 = r0 + 256 * c0) (E1 : a0 * b1 + a1 * b0 + c0 = r1 + 256 * c1) (E2 : a0 * b2 + a1 * b1 + a2 * b0 + c1 = r2 + 256 * c2) (E3 : a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 + c2 = r3 + 256 * c3) :
    (a0 + 256 * a1 + 2 ^ 16 * a2 + 2 ^ 24 * a3) * (b0 + 256 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3) =
      (r0 + 256 * r1 + 2 ^ 16 * r2 + 2 ^ 24 * r3) + 2 ^ 32 * (c3 + 1 * (a1 * b3) + 1 * (a2 * b2) + 256 * (a2 * b3) + 1 * (a3 * b1) + 256 * (a3 * b2) + 65536 * (a3 * b3)) := by
  grind


theorem mulLimb0 (x0 y0 r cy : Nat) (s : Nat)
    (h : ((s : Nat) : F) * (((0 : Nat) : F) + (x0 : F) * (y0 : F) + ((0 : Nat) : F) - (r : F) - ((256 : Nat) : F) * (cy : F)) = 0)
    (hs : s = 1) :
    ((x0 * y0 : Nat) : F) = ((r + 256 * cy : Nat) : F) := by
  subst hs; fp_ring

theorem mulLimb1 (x0 y0 x1 y1 cin r cy : Nat) (s : Nat)
    (h : ((s : Nat) : F) * (((0 : Nat) : F) + (x0 : F) * (y0 : F) + (x1 : F) * (y1 : F) + (cin : F) - (r : F) - ((256 : Nat) : F) * (cy : F)) = 0)
    (hs : s = 1) :
    ((x0 * y0 + x1 * y1 + cin : Nat) : F) = ((r + 256 * cy : Nat) : F) := by
  subst hs; fp_ring

theorem mulLimb2 (x0 y0 x1 y1 x2 y2 cin r cy : Nat) (s : Nat)
    (h : ((s : Nat) : F) * (((0 : Nat) : F) + (x0 : F) * (y0 : F) + (x1 : F) * (y1 : F) + (x2 : F) * (y2 : F) + (cin : F) - (r : F) - ((256 : Nat) : F) * (cy : F)) = 0)
    (hs : s = 1) :
    ((x0 * y0 + x1 * y1 + x2 * y2 + cin : Nat) : F) = ((r + 256 * cy : Nat) : F) := by
  subst hs; fp_ring

theorem mulLimb3 (x0 y0 x1 y1 x2 y2 x3 y3 cin r cy : Nat) (s : Nat)
    (h : ((s : Nat) : F) * (((0 : Nat) : F) + (x0 : F) * (y0 : F) + (x1 : F) * (y1 : F) + (x2 : F) * (y2 : F) + (x3 : F) * (y3 : F) + (cin : F) - (r : F) - ((256 : Nat) : F) * (cy : F)) = 0)
    (hs : s = 1) :
    ((x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3 + cin : Nat) : F) = ((r + 256 * cy : Nat) : F) := by
  subst hs; fp_ring

theorem mulLimb4 (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 cin r cy : Nat) (s : Nat)
    (h : ((s : Nat) : F) * (((0 : Nat) : F) + (x0 : F) * (y0 : F) + (x1 : F) * (y1 : F) + (x2 : F) * (y2 : F) + (x3 : F) * (y3 : F) + (x4 : F) * (y4 : F) + (cin : F) - (r : F) - ((256 : Nat) : F) * (cy : F)) = 0)
    (hs : s = 1) :
    ((x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4 + cin : Nat) : F) = ((r + 256 * cy : Nat) : F) := by
  subst hs; fp_ring

theorem mulLimb5 (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 cin r cy : Nat) (s : Nat)
    (h : ((s : Nat) : F) * (((0 : Nat) : F) + (x0 : F) * (y0 : F) + (x1 : F) * (y1 : F) + (x2 : F) * (y2 : F) + (x3 : F) * (y3 : F) + (x4 : F) * (y4 : F) + (x5 : F) * (y5 : F) + (cin : F) - (r : F) - ((256 : Nat) : F) * (cy : F)) = 0)
    (hs : s = 1) :
    ((x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4 + x5 * y5 + cin : Nat) : F) = ((r + 256 * cy : Nat) : F) := by
  subst hs; fp_ring

theorem mulLimb6 (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 cin r cy : Nat) (s : Nat)
    (h : ((s : Nat) : F) * (((0 : Nat) : F) + (x0 : F) * (y0 : F) + (x1 : F) * (y1 : F) + (x2 : F) * (y2 : F) + (x3 : F) * (y3 : F) + (x4 : F) * (y4 : F) + (x5 : F) * (y5 : F) + (x6 : F) * (y6 : F) + (cin : F) - (r : F) - ((256 : Nat) : F) * (cy : F)) = 0)
    (hs : s = 1) :
    ((x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4 + x5 * y5 + x6 * y6 + cin : Nat) : F) = ((r + 256 * cy : Nat) : F) := by
  subst hs; fp_ring

theorem mulLimb7 (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 x7 y7 cin r cy : Nat) (s : Nat)
    (h : ((s : Nat) : F) * (((0 : Nat) : F) + (x0 : F) * (y0 : F) + (x1 : F) * (y1 : F) + (x2 : F) * (y2 : F) + (x3 : F) * (y3 : F) + (x4 : F) * (y4 : F) + (x5 : F) * (y5 : F) + (x6 : F) * (y6 : F) + (x7 : F) * (y7 : F) + (cin : F) - (r : F) - ((256 : Nat) : F) * (cy : F)) = 0)
    (hs : s = 1) :
    ((x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4 + x5 * y5 + x6 * y6 + x7 * y7 + cin : Nat) : F) = ((r + 256 * cy : Nat) : F) := by
  subst hs; fp_ring

theorem mul_sound (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P)
    (hc : ∀ e ∈ Mul.constraints, e.eval (natRow c rw) = 0)
    (hact : c Mul.act = 1)
    (hab : ∀ k, k < 8 → c (Mul.ab + k) < 256) (hbb : ∀ k, k < 8 → c (Mul.bb + k) < 256)
    (hrb : ∀ k, k < 8 → c (Mul.rb + k) < 256) (hcy : ∀ k, k < 8 → c (Mul.cy + k) < 65536) :
    (c Mul.is64 = 0 ∨ c Mul.is64 = 1) ∧
    (c Mul.is64 = 0 → ∀ k, 4 ≤ k → k < 8 → c (Mul.ab + k) = 0 ∧ c (Mul.bb + k) = 0 ∧ c (Mul.rb + k) = 0) ∧
    Num.binop (32 + 32 * c Mul.is64) 2 (val8 fun k => c (Mul.ab + k)) (val8 fun k => c (Mul.bb + k)) =
      some (val8 fun k => c (Mul.rb + k)) := by
  simp only [Mul.constraints, List.forall_mem_append, List.forall_mem_flatMap, List.forall_mem_map,
    List.mem_range, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, Chips.bool, v,
    Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', Expr.eval_col, natRow] at hc
  obtain ⟨⟨⟨⟨_, b64⟩, hup⟩, hlo⟩, hhi⟩ := hc
  have b64' := bool_nat (hP _) b64
  have hupper : c Mul.is64 = 0 → ∀ k, 4 ≤ k → k < 8 →
      c (Mul.ab + k) = 0 ∧ c (Mul.bb + k) = 0 ∧ c (Mul.rb + k) = 0 := by
    intro h0 k hk1 hk2
    have hz := hup (k - 4) (by omega)
    simp only [h0, show Mul.ab + 4 + (k - 4) = Mul.ab + k by unfold Mul.ab; omega,
      show Mul.bb + 4 + (k - 4) = Mul.bb + k by unfold Mul.bb; omega,
      show Mul.rb + 4 + (k - 4) = Mul.rb + k by unfold Mul.rb; omega] at hz
    exact ⟨zero_of_sel0 (hP _) hz.1, zero_of_sel0 (hP _) hz.2.1, zero_of_sel0 (hP _) hz.2.2.1⟩
  refine ⟨b64', hupper, ?_⟩
  simp only [Mul.ab, Mul.bb, Mul.rb, Mul.cy, Mul.is64, Mul.act] at *
  have a := hab; have b := hbb; have r := hrb; have cy := hcy
  have hP' := P_val
  have l0 := hlo 0 (by decide); have l1 := hlo 1 (by decide); have l2 := hlo 2 (by decide)
  have l3 := hlo 3 (by decide)
  simp only [Mul.limbEq, Mul.conv, Mul.carryIn, Mul.ab, Mul.bb, Mul.rb, Mul.cy, List.range, List.range.loop, List.map, List.foldl,
    Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', Expr.eval_col, Expr.eval_c, natRow, v,
    Nat.reduceAdd, Nat.reduceSub, ite_true, ite_false, Nat.add_zero, Nat.zero_add, show (1 : Nat) ≠ 0 from by decide,
    show (2 : Nat) ≠ 0 from by decide, show (3 : Nat) ≠ 0 from by decide] at l0 l1 l2 l3
  have a0 := a 0 (by decide); have a1 := a 1 (by decide); have a2 := a 2 (by decide); have a3 := a 3 (by decide)
  have a4 := a 4 (by decide); have a5 := a 5 (by decide); have a6 := a 6 (by decide); have a7 := a 7 (by decide)
  have b0 := b 0 (by decide); have b1 := b 1 (by decide); have b2 := b 2 (by decide); have b3 := b 3 (by decide)
  have b4 := b 4 (by decide); have b5 := b 5 (by decide); have b6 := b 6 (by decide); have b7 := b 7 (by decide)
  have r0 := r 0 (by decide); have r1 := r 1 (by decide); have r2 := r 2 (by decide); have r3 := r 3 (by decide)
  have r4 := r 4 (by decide); have r5 := r 5 (by decide); have r6 := r 6 (by decide); have r7 := r 7 (by decide)
  have c0 := cy 0 (by decide); have c1 := cy 1 (by decide); have c2 := cy 2 (by decide); have c3 := cy 3 (by decide)
  have c4 := cy 4 (by decide); have c5 := cy 5 (by decide); have c6 := cy 6 (by decide); have c7 := cy 7 (by decide)
  simp only [Nat.reduceAdd, Nat.add_zero] at a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 r0 r1 r2 r3 r4 r5 r6 r7 c0 c1 c2 c3 c4 c5 c6 c7
  have mb : ∀ x y : Nat, x < 256 → y < 256 → x * y ≤ 65025 := fun x y hx hy =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)) (by decide)
  have p00 := mb _ _ a0 b0
  have p01 := mb _ _ a0 b1
  have p02 := mb _ _ a0 b2
  have p03 := mb _ _ a0 b3
  have p04 := mb _ _ a0 b4
  have p05 := mb _ _ a0 b5
  have p06 := mb _ _ a0 b6
  have p07 := mb _ _ a0 b7
  have p10 := mb _ _ a1 b0
  have p11 := mb _ _ a1 b1
  have p12 := mb _ _ a1 b2
  have p13 := mb _ _ a1 b3
  have p14 := mb _ _ a1 b4
  have p15 := mb _ _ a1 b5
  have p16 := mb _ _ a1 b6
  have p20 := mb _ _ a2 b0
  have p21 := mb _ _ a2 b1
  have p22 := mb _ _ a2 b2
  have p23 := mb _ _ a2 b3
  have p24 := mb _ _ a2 b4
  have p25 := mb _ _ a2 b5
  have p30 := mb _ _ a3 b0
  have p31 := mb _ _ a3 b1
  have p32 := mb _ _ a3 b2
  have p33 := mb _ _ a3 b3
  have p34 := mb _ _ a3 b4
  have p40 := mb _ _ a4 b0
  have p41 := mb _ _ a4 b1
  have p42 := mb _ _ a4 b2
  have p43 := mb _ _ a4 b3
  have p50 := mb _ _ a5 b0
  have p51 := mb _ _ a5 b1
  have p52 := mb _ _ a5 b2
  have p60 := mb _ _ a6 b0
  have p61 := mb _ _ a6 b1
  have p70 := mb _ _ a7 b0
  have E0 : c 7 * c 17 = c 27 + 256 * c 35 :=
    natEq (by fp_ring) (by omega) (by omega)
  have E1 : c 7 * c 18 + c 8 * c 17 + c 35 = c 28 + 256 * c 36 :=
    natEq (by fp_ring) (by omega) (by omega)
  have E2 : c 7 * c 19 + c 8 * c 18 + c 9 * c 17 + c 36 = c 29 + 256 * c 37 :=
    natEq (by fp_ring) (by omega) (by omega)
  have E3 : c 7 * c 20 + c 8 * c 19 + c 9 * c 18 + c 10 * c 17 + c 37 = c 30 + 256 * c 38 :=
    natEq (by fp_ring) (by omega) (by omega)
  rcases b64' with w | w
  · -- i32
    obtain ⟨u4, v4, _⟩ := hupper w 4 (by decide) (by decide)
    obtain ⟨u5, v5, _⟩ := hupper w 5 (by decide) (by decide)
    obtain ⟨u6, v6, _⟩ := hupper w 6 (by decide) (by decide)
    obtain ⟨u7, v7, _⟩ := hupper w 7 (by decide) (by decide)
    obtain ⟨_, _, z4⟩ := hupper w 4 (by decide) (by decide)
    obtain ⟨_, _, z5⟩ := hupper w 5 (by decide) (by decide)
    obtain ⟨_, _, z6⟩ := hupper w 6 (by decide) (by decide)
    obtain ⟨_, _, z7⟩ := hupper w 7 (by decide) (by decide)
    simp only [Nat.reduceAdd] at u4 u5 u6 u7 v4 v5 v6 v7 z4 z5 z6 z7
    have key := mul4_key (c 7) (c 8) (c 9) (c 10) (c 17) (c 18) (c 19) (c 20) (c 27) (c 28) (c 29) (c 30)
      (c 35) (c 36) (c 37) (c 38) E0 E1 E2 E3
    have hr : (val8 fun k => c (Mul.rb + k)) < 2 ^ 32 := by
      simp only [val8, Mul.rb, Nat.add_zero, Nat.reduceAdd, z4, z5, z6, z7, Nat.reducePow]; omega
    simp only [w, Num.binop, Option.some.injEq, val8, Mul.ab, Mul.bb, Mul.rb, Nat.reduceAdd, Nat.add_zero] at hr ⊢
    simp only [u4, u5, u6, u7, v4, v5, v6, v7, z4, z5, z6, z7, Nat.mul_zero, Nat.add_zero] at hr ⊢
    rw [key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  · -- i64
    have h4 := hhi 0 (by decide); have h5 := hhi 1 (by decide); have h6 := hhi 2 (by decide)
    have h7 := hhi 3 (by decide)
    clear hhi hlo hup hupper l0 l1 l2 l3 b64 a b r cy hab hbb hrb hcy hP mb
    simp only [w, Mul.limbEq, Mul.conv, Mul.carryIn, Mul.ab, Mul.bb, Mul.rb, Mul.cy, List.range, List.range.loop, List.map, List.foldl,
      Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', Expr.eval_col, Expr.eval_c, natRow, v,
      Nat.reduceAdd, Nat.reduceSub, ite_true, ite_false, Nat.add_zero, Nat.zero_add, ↓reduceIte, Nat.reduceEqDiff] at h4
    have E4 : c 7 * c 21 + c 8 * c 20 + c 9 * c 19 + c 10 * c 18 + c 11 * c 17 + c 38 = c 31 + 256 * c 39 :=
      natEq (mulLimb4 (h := h4) (hs := rfl)) (by omega) (by omega)
    simp only [w, Mul.limbEq, Mul.conv, Mul.carryIn, Mul.ab, Mul.bb, Mul.rb, Mul.cy, List.range, List.range.loop, List.map, List.foldl,
      Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', Expr.eval_col, Expr.eval_c, natRow, v,
      Nat.reduceAdd, Nat.reduceSub, ite_true, ite_false, Nat.add_zero, Nat.zero_add, ↓reduceIte, Nat.reduceEqDiff] at h5
    have E5 : c 7 * c 22 + c 8 * c 21 + c 9 * c 20 + c 10 * c 19 + c 11 * c 18 + c 12 * c 17 + c 39 = c 32 + 256 * c 40 :=
      natEq (mulLimb5 (h := h5) (hs := rfl)) (by omega) (by omega)
    simp only [w, Mul.limbEq, Mul.conv, Mul.carryIn, Mul.ab, Mul.bb, Mul.rb, Mul.cy, List.range, List.range.loop, List.map, List.foldl,
      Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', Expr.eval_col, Expr.eval_c, natRow, v,
      Nat.reduceAdd, Nat.reduceSub, ite_true, ite_false, Nat.add_zero, Nat.zero_add, ↓reduceIte, Nat.reduceEqDiff] at h6
    have E6 : c 7 * c 23 + c 8 * c 22 + c 9 * c 21 + c 10 * c 20 + c 11 * c 19 + c 12 * c 18 + c 13 * c 17 + c 40 = c 33 + 256 * c 41 :=
      natEq (mulLimb6 (h := h6) (hs := rfl)) (by omega) (by omega)
    simp only [w, Mul.limbEq, Mul.conv, Mul.carryIn, Mul.ab, Mul.bb, Mul.rb, Mul.cy, List.range, List.range.loop, List.map, List.foldl,
      Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', Expr.eval_col, Expr.eval_c, natRow, v,
      Nat.reduceAdd, Nat.reduceSub, ite_true, ite_false, Nat.add_zero, Nat.zero_add, ↓reduceIte, Nat.reduceEqDiff] at h7
    have E7 : c 7 * c 24 + c 8 * c 23 + c 9 * c 22 + c 10 * c 21 + c 11 * c 20 + c 12 * c 19 + c 13 * c 18 + c 14 * c 17 + c 41 = c 34 + 256 * c 42 :=
      natEq (mulLimb7 (h := h7) (hs := rfl)) (by omega) (by omega)
    have key := mul8_key (c 7) (c 8) (c 9) (c 10) (c 11) (c 12) (c 13) (c 14) (c 17) (c 18) (c 19) (c 20) (c 21) (c 22) (c 23) (c 24) (c 27) (c 28) (c 29) (c 30) (c 31) (c 32) (c 33) (c 34) (c 35) (c 36) (c 37) (c 38) (c 39) (c 40) (c 41) (c 42)
      E0 E1 E2 E3 E4 E5 E6 E7
    have hr : (val8 fun k => c (Mul.rb + k)) < 2 ^ 64 := by
      simp only [val8, Mul.rb, Nat.add_zero, Nat.reduceAdd, Nat.reducePow]; omega
    simp only [w, Num.binop, Option.some.injEq, val8, Mul.ab, Mul.bb, Mul.rb, Nat.reduceAdd, Nat.add_zero] at hr ⊢
    rw [key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

end WasmBase.Local
