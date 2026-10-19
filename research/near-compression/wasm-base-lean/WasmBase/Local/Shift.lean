import WasmBase.Local.Add
import WasmBase.Local.ShiftSem
import WasmBase.Local.ShiftBytes
/-!
# Local soundness of SHIFT (i32/i64 shl, shr_s, shr_u, rotl, rotr)

(1) bits, the one-hot byte offset `t` and `pow = 2^eb` from the constraints; (2) the byte chain
`P_j + 256 cy_j = pow · A_{j-t} + cy_{j-1}` computes `P = (A · 2^e) mod 2^(2w)` with `e = 8t + eb`
(`chain_prod`, generic in the length); (3) the selected half (or the sum of both halves) is the
spec result (`WasmBase.Local.ShiftSem`); for rotations the halves have disjoint bits, so the result
bytes stay bytes (`byte_disjoint`).
-/
namespace WasmBase.Local
open ZkFormal.Algebra WasmBase.Chips NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

/-- Natural-number mirror of `Shift.A` (byte `i` of the `2w`-bit extension of `a`). -/
def shA (c : Nat → Nat) (i : Nat) : Nat :=
  if i < 4 then c (11 + i)
  else if i < 8 then c 10 * c (11 + i) + (1 - c 10) * (255 * c 46 * c 6)
  else if i < 16 then c 10 * (255 * c 46 * c 6) else 0

/-- Natural-number mirror of `Shift.M`. -/
def shM (c : Nat → Nat) (j : Nat) : Nat :=
  ((List.range 9).filterMap fun t => if t ≤ j then some (c (37 + t) * shA c (j - t)) else none).foldl (· + ·) 0

/-- The result bytes of the SHIFT row as naturals (mirror of `Shift.rbyte`). -/
def shiftR (c : Nat → Nat) (j : Nat) : Nat :=
  if j < 4 then (c 5 + c 8 + c 9) * c (48 + j) +
      (c 6 + c 7 + c 8 + c 9) * (c 10 * c (48 + j + 8) + (1 - c 10) * c (48 + j + 4))
  else c 10 * ((c 5 + c 8 + c 9) * c (48 + j) + (c 6 + c 7 + c 8 + c 9) * c (48 + j + 8))

theorem shA_eval (c : Nat → Nat) (rw : Row) (h10 : c 10 ≤ 1) (i : Nat) :
    (Shift.A i).eval (natRow c rw) = ((shA c i : Nat) : F) := by
  rcases (show c 10 = 0 ∨ c 10 = 1 by omega) with h | h <;>
  · unfold Shift.A shA
    by_cases h1 : i < 4
    · simp [h1, v, natRow, Shift.ab]
    · by_cases h2 : i < 8
      · simp only [h1, h2, ite_false, ite_true, Shift.fill, v, Expr.eval_add', Expr.eval_mul', Expr.eval_sub',
          Expr.eval_col, Expr.eval_ofNat', natRow, Shift.is64, Shift.ab, Shift.sgn, Shift.fShrS, h]
        first | fp_ring | simp only [Lean.Grind.Semiring.natCast_mul, Lean.Grind.Semiring.natCast_add]
      · by_cases h3 : i < 16
        · simp only [h1, h2, h3, ite_false, ite_true, Shift.fill, v, Expr.eval_add', Expr.eval_mul', Expr.eval_sub',
            Expr.eval_col, Expr.eval_ofNat', natRow, Shift.is64, Shift.sgn, Shift.fShrS, h]
          first | fp_ring | simp only [Lean.Grind.Semiring.natCast_mul, Lean.Grind.Semiring.natCast_add]
        · simp [h1, h2, h3]

theorem foldl_filterMap_eval (rw : Row) (j : Nat) (E : Nat → Expr) (N : Nat → Nat)
    (hEN : ∀ t, (E t).eval rw = ((N t : Nat) : F)) :
    ∀ (L : List Nat) (acc : Expr) (accN : Nat), acc.eval rw = ((accN : Nat) : F) →
      ((L.filterMap fun t => if t ≤ j then some (E t) else none).foldl (· + ·) acc).eval rw =
        ((((L.filterMap fun t => if t ≤ j then some (N t) else none).foldl (· + ·) accN) : Nat) : F) := by
  intro L
  induction L with
  | nil => intro acc accN h; simpa using h
  | cons t L ih =>
    intro acc accN h
    by_cases ht : t ≤ j
    · simp only [List.filterMap_cons, ht, ite_true, List.foldl_cons]
      exact ih _ _ (by rw [Expr.eval_add', h, hEN, Lean.Grind.Semiring.natCast_add])
    · simp only [List.filterMap_cons, ht, ite_false, List.foldl_cons]
      exact ih _ _ h

theorem shM_eval (c : Nat → Nat) (rw : Row) (h10 : c 10 ≤ 1) (j : Nat) :
    (Shift.M j).eval (natRow c rw) = ((shM c j : Nat) : F) := by
  unfold Shift.M shM
  exact foldl_filterMap_eval _ j _ _ (fun t => by
    rw [Expr.eval_mul', shA_eval c rw h10, Lean.Grind.Semiring.natCast_mul]; rfl) _ _ _ rfl

/-! ## One-hot selection -/

theorem foldl_add_acc (L : List Nat) (a : Nat) : L.foldl (· + ·) a = a + L.foldl (· + ·) 0 := by
  induction L generalizing a with
  | nil => simp
  | cons x L ih => simp only [List.foldl_cons]; rw [ih (a + x), ih (0 + x)]; omega

theorem foldl_filterMap_eq_map (j : Nat) (N : Nat → Nat) (L : List Nat) :
    (L.filterMap fun t => if t ≤ j then some (N t) else none).foldl (· + ·) 0 =
      (L.map fun t => if t ≤ j then N t else 0).foldl (· + ·) 0 := by
  induction L with
  | nil => rfl
  | cons t L ih =>
    by_cases ht : t ≤ j
    · simp only [List.filterMap_cons, ht, ite_true, List.map_cons, List.foldl_cons]
      rw [foldl_add_acc _ (0 + N t), foldl_add_acc _ (0 + N t), ih]
    · simp only [List.filterMap_cons, ht, ite_false, List.map_cons, List.foldl_cons, Nat.add_zero]
      exact ih

theorem sum_onehot (g : Nat → Nat) (t0 : Nat) : ∀ (L : List Nat), L.Nodup →
    (L.map fun t => if t = t0 then g t else 0).foldl (· + ·) 0 = if t0 ∈ L then g t0 else 0 := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons t L ih =>
    intro hnd
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.foldl_cons]
    rw [foldl_add_acc, ih hnd.2]
    by_cases h : t = t0
    · subst h; simp [hnd.1]
    · simp [h, Ne.symm h]

theorem shM_onehot (c : Nat → Nat) (t0 : Nat) (ht0 : t0 < 9)
    (hsel : ∀ t, t < 9 → c (37 + t) = if t = t0 then 1 else 0) (j : Nat) :
    shM c j = if t0 ≤ j then shA c (j - t0) else 0 := by
  unfold shM
  rw [foldl_filterMap_eq_map]
  have : (List.range 9).map (fun t => if t ≤ j then c (37 + t) * shA c (j - t) else 0) =
      (List.range 9).map (fun t => if t = t0 then (if t ≤ j then shA c (j - t) else 0) else 0) := by
    apply List.map_congr_left
    intro t ht
    rw [List.mem_range] at ht
    rw [hsel t ht]
    by_cases h1 : t = t0 <;> by_cases h2 : t ≤ j <;> simp [h1, h2]
  rw [this, sum_onehot _ t0 _ (List.nodup_range)]
  simp [ht0]

theorem onehot9 (c : Nat → Nat) (hb : ∀ t, t < 9 → c (37 + t) ≤ 1)
    (hs : c 37 + c 38 + c 39 + c 40 + c 41 + c 42 + c 43 + c 44 + c 45 = 1) :
    ∃ t0, t0 < 9 ∧ ∀ t, t < 9 → c (37 + t) = if t = t0 then 1 else 0 := by
  have b0 := hb 0 (by decide); have b1 := hb 1 (by decide); have b2 := hb 2 (by decide)
  have b3 := hb 3 (by decide); have b4 := hb 4 (by decide); have b5 := hb 5 (by decide)
  have b6 := hb 6 (by decide); have b7 := hb 7 (by decide); have b8 := hb 8 (by decide)
  simp only [Nat.reduceAdd] at b0 b1 b2 b3 b4 b5 b6 b7 b8
  have key : ∀ t0, t0 < 9 → c (37 + t0) = 1 → ∀ t, t < 9 → c (37 + t) = if t = t0 then 1 else 0 := by
    intro t0 ht0 h1 t ht
    by_cases e : t = t0
    · subst e; simp [h1]
    · simp only [e, ite_false]
      have : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 := by omega
      have : t0 = 0 ∨ t0 = 1 ∨ t0 = 2 ∨ t0 = 3 ∨ t0 = 4 ∨ t0 = 5 ∨ t0 = 6 ∨ t0 = 7 ∨ t0 = 8 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases ‹t = 0 ∨ _› with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Nat.reduceAdd] at h1 ⊢ <;> omega
  have : c 37 = 1 ∨ c 38 = 1 ∨ c 39 = 1 ∨ c 40 = 1 ∨ c 41 = 1 ∨ c 42 = 1 ∨ c 43 = 1 ∨ c 44 = 1 ∨ c 45 = 1 := by
    omega
  rcases this with h | h | h | h | h | h | h | h | h
  · exact ⟨0, by decide, key 0 (by decide) h⟩
  · exact ⟨1, by decide, key 1 (by decide) h⟩
  · exact ⟨2, by decide, key 2 (by decide) h⟩
  · exact ⟨3, by decide, key 3 (by decide) h⟩
  · exact ⟨4, by decide, key 4 (by decide) h⟩
  · exact ⟨5, by decide, key 5 (by decide) h⟩
  · exact ⟨6, by decide, key 6 (by decide) h⟩
  · exact ⟨7, by decide, key 7 (by decide) h⟩
  · exact ⟨8, by decide, key 8 (by decide) h⟩

theorem pow3_bits (e0 e1 e2 : Nat) (h0 : e0 ≤ 1) (h1 : e1 ≤ 1) (h2 : e2 ≤ 1) :
    (1 + e0) * (1 + 3 * e1) * (1 + 15 * e2) = 2 ^ (e0 + 2 * e1 + 4 * e2) := by
  rcases (show e0 = 0 ∨ e0 = 1 by omega) with rfl | rfl <;>
  rcases (show e1 = 0 ∨ e1 = 1 by omega) with rfl | rfl <;>
  rcases (show e2 = 0 ∨ e2 = 1 by omega) with rfl | rfl <;> rfl

theorem shA_lt (c : Nat → Nat) (h10 : c 10 ≤ 1) (hab : ∀ k, k < 8 → c (11 + k) < 256)
    (h6 : c 6 ≤ 1) (h46 : c 46 ≤ 1) (i : Nat) : shA c i < 256 := by
  have hf : 255 * c 46 * c 6 ≤ 255 := by
    rcases (show c 46 = 0 ∨ c 46 = 1 by omega) with h | h <;>
    rcases (show c 6 = 0 ∨ c 6 = 1 by omega) with h' | h' <;> simp [h, h']
  unfold shA
  rcases (show c 10 = 0 ∨ c 10 = 1 by omega) with h | h <;>
  · by_cases h1 : i < 4
    · simp only [h1, ite_true]; exact hab i (by omega)
    · by_cases h2 : i < 8
      · simp only [h1, h2, ite_true, ite_false, h]
        have := hab i (by omega); omega
      · by_cases h3 : i < 16 <;> simp only [h1, h2, h3, ite_true, ite_false, h] <;> omega

/-- The constraint facts of an active SHIFT row, as naturals (one-hot offset `t0`). -/
theorem shift_facts (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P)
    (hc : ∀ e ∈ Shift.constraints, e.eval (natRow c rw) = 0)
    (hact : c 5 + c 6 + c 7 + c 8 + c 9 = 1)
    (hab : ∀ k, k < 8 → c (11 + k) < 256) (hb0 : c 21 < 65536) (hq : c 33 < 65536)
    (hrest : (2 * c 47) % P < 256)
    (hPb : ∀ j, j < 16 → c (48 + j) < 256) (hcy : ∀ j, j < 16 → c (64 + j) < 256) :
    c 5 ≤ 1 ∧ c 6 ≤ 1 ∧ c 7 ≤ 1 ∧ c 8 ≤ 1 ∧ c 9 ≤ 1 ∧ c 10 ≤ 1 ∧ c 46 ≤ 1 ∧
    (c 10 = 0 → (∀ k, 4 ≤ k → k < 8 → c (11 + k) = 0) ∧ c 23 = 0 ∧ c 24 = 0 ∧ c 32 = 0 ∧
      ∀ k, k < 8 → c (56 + k) = 0 ∧ c (72 + k) = 0) ∧
    c 21 = (c 27 + 2 * c 28 + 4 * c 29 + 8 * c 30 + 16 * c 31 + 32 * c 32) + (32 + 32 * c 10) * c 33 ∧
    c 27 + 2 * c 28 + 4 * c 29 + 8 * c 30 + 16 * c 31 + 32 * c 32 < 32 + 32 * c 10 ∧
    c 10 * c 18 + (1 - c 10) * c 14 = 128 * c 46 + c 47 ∧ c 47 < 128 ∧
    ∃ t0, t0 < 9 ∧ ∃ eb, eb < 8 ∧
      (c 5 + c 8 = 1 → c 27 + 2 * c 28 + 4 * c 29 + 8 * c 30 + 16 * c 31 + 32 * c 32 = eb + 8 * t0) ∧
      (c 6 + c 7 + c 9 = 1 → 32 + 32 * c 10 = c 27 + 2 * c 28 + 4 * c 29 + 8 * c 30 + 16 * c 31 + 32 * c 32 + (eb + 8 * t0)) ∧
      ∀ j, j < 8 + 8 * c 10 →
        2 ^ eb * (if t0 ≤ j then shA c (j - t0) else 0) + (if j = 0 then 0 else c (64 + (j - 1))) =
          c (48 + j) + 256 * c (64 + j) := by
  have hP' := P_val
  simp only [Shift.constraints, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range, List.forall_mem_flatMap] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := hc
  obtain ⟨bF0, bF1, bF2, bF3, bF4, b64, -, -⟩ := h1
  obtain ⟨zkb5, hbkq, -⟩ := h3
  obtain ⟨helsum, heq, bsgn, htop, -⟩ := h6
  obtain ⟨zb2, zb3, -⟩ := h8
  have bitOf : ∀ i, (Chips.bool (v i)).eval (natRow c rw) = 0 → c i ≤ 1 := by
    intro i h
    simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow] at h
    rcases bool_nat (hP i) h with h | h <;> omega
  have sel0 : ∀ i, ((1 - v Shift.is64) * v i).eval (natRow c rw) = 0 → c 10 = 0 → c i = 0 := by
    intro i h h0
    simp only [v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow, Shift.is64, h0] at h
    exact zero_of_sel0 (hP _) h
  have f0 : c 5 ≤ 1 := bitOf 5 bF0
  have f1 : c 6 ≤ 1 := bitOf 6 bF1
  have f2 : c 7 ≤ 1 := bitOf 7 bF2
  have f3 : c 8 ≤ 1 := bitOf 8 bF3
  have f4 : c 9 ≤ 1 := bitOf 9 bF4
  have w1 : c 10 ≤ 1 := bitOf 10 b64
  have sg : c 46 ≤ 1 := bitOf 46 bsgn
  have hk : ∀ j, j < 6 → c (27 + j) ≤ 1 := fun j hj => bitOf _ (h2 j hj)
  have hke : ∀ j, j < 3 → c (34 + j) ≤ 1 := fun j hj => bitOf _ (h4 j hj)
  have hl : ∀ j, j < 9 → c (37 + j) ≤ 1 := fun j hj => bitOf _ (h5 j hj)
  have k0 := hk 0 (by decide); have k1 := hk 1 (by decide); have k2 := hk 2 (by decide)
  have k3 := hk 3 (by decide); have k4 := hk 4 (by decide); have k5 := hk 5 (by decide)
  have e0 := hke 0 (by decide); have e1 := hke 1 (by decide); have e2 := hke 2 (by decide)
  simp only [Nat.reduceAdd] at k0 k1 k2 k3 k4 k5 e0 e1 e2
  have upper : c 10 = 0 → (∀ k, 4 ≤ k → k < 8 → c (11 + k) = 0) ∧ c 23 = 0 ∧ c 24 = 0 ∧ c 32 = 0 ∧
      ∀ k, k < 8 → c (56 + k) = 0 ∧ c (72 + k) = 0 := by
    intro h0
    refine ⟨fun k hk1 hk2 => ?_, sel0 _ zb2 h0, sel0 _ zb3 h0, sel0 _ zkb5 h0, fun k hk => ?_⟩
    · have := sel0 _ (h7 (k - 4) (by omega)) h0
      rwa [show Shift.ab + 4 + (k - 4) = 11 + k by simp only [Shift.ab]; omega] at this
    · exact ⟨sel0 _ (h9 k hk).1 h0, sel0 _ (h9 k hk).2.1 h0⟩
  -- the count: `b0 = k + w q`
  simp only [Shift.kval, Shift.w, List.range, List.range.loop, List.map, List.foldl, v, Expr.eval_add',
    Expr.eval_sub', Expr.eval_mul', Expr.eval_c, Expr.eval_col, Expr.eval_ofNat', natRow, Shift.b, Shift.kb,
    Shift.q, Shift.is64, Nat.reducePow, Nat.reduceAdd] at hbkq
  have hwq : (32 + 32 * c 10) * c 33 ≤ 64 * 65535 := Nat.mul_le_mul (by omega) (by omega)
  have hK : c 21 = (c 27 + 2 * c 28 + 4 * c 29 + 8 * c 30 + 16 * c 31 + 32 * c 32) + (32 + 32 * c 10) * c 33 :=
    natEq (by fp_ring) (by omega) (by omega)
  have hKw : c 27 + 2 * c 28 + 4 * c 29 + 8 * c 30 + 16 * c 31 + 32 * c 32 < 32 + 32 * c 10 := by
    rcases (show c 10 = 0 ∨ c 10 = 1 by omega) with h | h
    · have := (upper h).2.2.2.1; omega
    · omega
  -- the sign byte
  simp only [Shift.topByte, v, Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_col, Expr.eval_ofNat', natRow,
    Shift.is64, Shift.ab, Shift.sgn, Shift.rest, Nat.reduceAdd] at htop
  have a3 := hab 3 (by decide); have a7 := hab 7 (by decide)
  simp only [Nat.reduceAdd] at a3 a7
  -- `rest` is pinned by the top byte and the sign bit, so `2·rest mod p < 256` bounds it
  have pin : ∀ top, top < 256 → ((c 47 + 128 * c 46 : Nat) : F) = ((top : Nat) : F) →
      top = 128 * c 46 + c 47 ∧ c 47 < 128 := by
    intro top htp hcast
    have h47 := hP 47
    have this := congrArg Fp.toNat hcast
    rw [Fp.toNat_cast, Fp.toNat_cast, Nat.mod_eq_of_lt (show top < P by omega)] at this
    have hr := hrest
    rcases (show c 46 = 0 ∨ c 46 = 1 by omega) with g | g <;> simp only [g] at this ⊢
    · rw [Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt h47] at this
      subst this
      rw [Nat.mod_eq_of_lt (by omega)] at hr
      omega
    · by_cases hw : c 47 + 128 * 1 < P
      · rw [Nat.mod_eq_of_lt hw] at this; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at this
        exfalso
        by_cases ht : 128 ≤ top
        · omega
        · rw [show 2 * c 47 = (2 * top + P - 256) + P by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)] at hr
          omega
  have htopN : c 10 * c 18 + (1 - c 10) * c 14 = 128 * c 46 + c 47 ∧ c 47 < 128 := by
    rcases (show c 10 = 0 ∨ c 10 = 1 by omega) with h | h <;> simp only [h] at htop ⊢
    · have := pin (c 14) a3 (by fp_ring); omega
    · have := pin (c 18) a7 (by fp_ring); omega
  -- one-hot byte offset
  simp only [Shift.act, Shift.left, Shift.right, Shift.el, List.range, List.range.loop, List.map, List.foldl, v,
    Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_c, Expr.eval_col, Expr.eval_ofNat', natRow,
    Nat.reduceAdd, Shift.fShl, Shift.fShrS, Shift.fShrU, Shift.fRotl, Shift.fRotr] at helsum
  have l0 := hl 0 (by decide); have l1 := hl 1 (by decide); have l2 := hl 2 (by decide)
  have l3 := hl 3 (by decide); have l4 := hl 4 (by decide); have l5 := hl 5 (by decide)
  have l6 := hl 6 (by decide); have l7 := hl 7 (by decide); have l8 := hl 8 (by decide)
  simp only [Nat.reduceAdd] at l0 l1 l2 l3 l4 l5 l6 l7 l8
  have hsum : c 37 + c 38 + c 39 + c 40 + c 41 + c 42 + c 43 + c 44 + c 45 = 1 := by
    have := natEq (L := c 37 + c 38 + c 39 + c 40 + c 41 + c 42 + c 43 + c 44 + c 45)
      (R := c 5 + c 8 + (c 6 + c 7 + c 9)) (by fp_ring) (by omega) (by omega)
    omega
  obtain ⟨t0, ht0, hsel⟩ := onehot9 c hl hsum
  have hT : c 38 + 2 * c 39 + 3 * c 40 + 4 * c 41 + 5 * c 42 + 6 * c 43 + 7 * c 44 + 8 * c 45 = t0 := by
    have s1 := hsel 1 (by decide); have s2 := hsel 2 (by decide); have s3 := hsel 3 (by decide)
    have s4 := hsel 4 (by decide); have s5 := hsel 5 (by decide); have s6 := hsel 6 (by decide)
    have s7 := hsel 7 (by decide); have s8 := hsel 8 (by decide)
    simp only [Nat.reduceAdd] at s1 s2 s3 s4 s5 s6 s7 s8
    rw [s1, s2, s3, s4, s5, s6, s7, s8]
    have : t0 = 0 ∨ t0 = 1 ∨ t0 = 2 ∨ t0 = 3 ∨ t0 = 4 ∨ t0 = 5 ∨ t0 = 6 ∨ t0 = 7 ∨ t0 = 8 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  -- the exponent `e = eb + 8 t0`
  simp only [Shift.eval', Shift.ebval, Shift.tval, Shift.kval, Shift.w, Shift.left, Shift.right, List.range,
    List.range.loop, List.map, List.foldl, v, Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_c,
    Expr.eval_col, Expr.eval_ofNat', natRow, Nat.reduceAdd, Nat.reducePow, Shift.fShl, Shift.fShrS, Shift.fShrU,
    Shift.fRotl, Shift.fRotr, Shift.kb, Shift.eb, Shift.el, Shift.is64] at heq
  refine ⟨f0, f1, f2, f3, f4, w1, sg, upper, hK, hKw, htopN.1, htopN.2, t0, ht0,
    c 34 + 2 * c 35 + 4 * c 36, by omega, ?_, ?_, ?_⟩
  · intro hL
    have hR : c 6 + c 7 + c 9 = 0 := by omega
    have fL : ((c 5 : Nat) : F) + ((c 8 : Nat) : F) = 1 := by
      rw [← Lean.Grind.Semiring.natCast_add, hL]; rfl
    have fR : ((c 6 : Nat) : F) + ((c 7 : Nat) : F) + ((c 9 : Nat) : F) = 0 := by
      rw [← Lean.Grind.Semiring.natCast_add, ← Lean.Grind.Semiring.natCast_add, hR]; rfl
    rw [← hT]
    exact natEq (by simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul] at *; grind)
      (by omega) (by omega)
  · intro hR
    have hL : c 5 + c 8 = 0 := by omega
    have fL : ((c 5 : Nat) : F) + ((c 8 : Nat) : F) = 0 := by
      rw [← Lean.Grind.Semiring.natCast_add, hL]; rfl
    have fR : ((c 6 : Nat) : F) + ((c 7 : Nat) : F) + ((c 9 : Nat) : F) = 1 := by
      rw [← Lean.Grind.Semiring.natCast_add, ← Lean.Grind.Semiring.natCast_add, hR]; rfl
    rw [← hT]
    exact natEq (by simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul] at *; grind)
      (by omega) (by omega)
  · intro j hj
    have hpw := pow3_bits (c 34) (c 35) (c 36) e0 e1 e2
    have hpwle : 2 ^ (c 34 + 2 * c 35 + 4 * c 36) ≤ 128 :=
      Nat.le_trans (Nat.pow_le_pow_right (by decide) (show c 34 + 2 * c 35 + 4 * c 36 ≤ 7 by omega)) (by decide)
    have hE : (Shift.limbEq j).eval (natRow c rw) = 0 := by
      by_cases hj8 : j < 8
      · exact h10 j hj8
      · have h1' : c 10 = 1 := by omega
        have := h11 (j - 8) (by omega)
        rw [show j - 8 + 8 = j by omega, Expr.eval_mul'] at this
        have key : (v Shift.is64).eval (natRow c rw) = 1 := by
          simp only [v, Expr.eval_col, natRow, Shift.is64, h1']; rfl
        rw [key] at this
        grind
    simp only [Shift.limbEq, Shift.pow, Expr.eval_add', Expr.eval_sub', Expr.eval_mul', shM_eval c rw w1,
      shM_onehot c t0 ht0 hsel] at hE
    have hX : (if t0 ≤ j then shA c (j - t0) else 0) < 256 := by
      split
      · exact shA_lt c w1 hab f1 sg _
      · omega
    have hp := hPb j (by omega); have hcj := hcy j (by omega)
    have hmul : 2 ^ (c 34 + 2 * c 35 + 4 * c 36) * (if t0 ≤ j then shA c (j - t0) else 0) ≤ 128 * 255 :=
      Nat.mul_le_mul hpwle (by omega)
    rw [← hpw] at hmul ⊢
    by_cases hj0 : j = 0
    · simp only [hj0, Shift.carryIn, ite_true, v, Expr.eval_col, Expr.eval_ofNat', Expr.eval_c, natRow, Shift.eb,
        Shift.P, Shift.cy, Nat.reduceAdd, Nat.add_zero] at hE hp hcj hmul ⊢
      exact natEq (by fp_ring) (by omega) (by omega)
    · have hcp := hcy (j - 1) (by omega)
      simp only [Shift.carryIn, hj0, ite_false, v, Expr.eval_col, Expr.eval_ofNat', Expr.eval_c, natRow, Shift.eb,
        Shift.P, Shift.cy, Nat.reduceAdd] at hE ⊢
      rw [show 64 + j - 1 = 64 + (j - 1) by omega] at hE
      exact natEq (by fp_ring) (by omega) (by omega)
