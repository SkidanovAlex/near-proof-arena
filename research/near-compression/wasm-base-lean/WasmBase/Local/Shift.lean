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

/-! ## From the product to the spec result -/

theorem val8_bsum (f : Nat → Nat) : val8 f = bsum f 8 := by
  simp only [val8, bsum, Nat.reducePow]; omega

theorem bsum_byte (f : Nat → Nat) (n j : Nat) (hj : j < n) (hf : ∀ i, i < n → f i < 256) :
    bsum f n / 256 ^ j % 256 = f j := by
  obtain ⟨m, rfl⟩ : ∃ m, n = j + (m + 1) := ⟨n - j - 1, by omega⟩
  rw [bsum_split, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)),
    Nat.div_eq_of_lt (bsum_lt f j (fun i hi => hf i (by omega))), Nat.zero_add,
    show m + 1 = 1 + m by omega, bsum_split]
  simp only [bsum, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.pow_one, Nat.add_zero]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hf j (by omega))]

theorem bsum_const (x : Nat) : ∀ h, 255 * bsum (fun _ => x) h + x = x * 256 ^ h := by
  intro h
  induction h with
  | zero => simp [bsum]
  | succ h ih => simp only [bsum]; rw [Nat.pow_succ]; grind

theorem rot_halves (W a e lo hi : Nat) (he : e ≤ W) (ha : a < 2 ^ W) (hlo : lo < 2 ^ W)
    (h : lo + 2 ^ W * hi = (a * 2 ^ e) % 2 ^ (2 * W)) : lo % 2 ^ e = 0 ∧ hi < 2 ^ e := by
  have h1 := lo_of W _ lo hi hlo h
  have h2 := hi_of W _ lo hi hlo (mul_pow_lt he ha) h
  constructor
  · rw [h1, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 he), Nat.mul_mod_left]
  · rw [h2, Nat.div_lt_iff_lt_mul (two_pow_pos' W), Nat.mul_comm (2 ^ e)]
    exact Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_refl _) (two_pow_pos' e)

theorem count_mod (W b0 b1 b2 b3 : Nat) (hW : W = 32 ∨ W = 64) :
    val4 b0 b1 b2 b3 % W = b0 % W := by
  unfold val4
  rcases hW with rfl | rfl
  · rw [show b0 + 65536 * b1 + 2 ^ 32 * b2 + 2 ^ 48 * b3 = b0 + 32 * (2048 * b1 + 2 ^ 27 * b2 + 2 ^ 43 * b3) by
      simp only [Nat.reducePow]; omega, Nat.add_mul_mod_self_left]
  · rw [show b0 + 65536 * b1 + 2 ^ 32 * b2 + 2 ^ 48 * b3 = b0 + 64 * (1024 * b1 + 2 ^ 26 * b2 + 2 ^ 42 * b3) by
      simp only [Nat.reducePow]; omega, Nat.add_mul_mod_self_left]

theorem binop_shift_mod (W k a b : Nat) (op : Nat) (hop : 10 ≤ op ∧ op ≤ 14) (hk : b % W = k) :
    Num.binop W op a b = Num.binop W op a k ∧ k < W ∨ W = 0 := by
  by_cases hW : W = 0
  · exact Or.inr hW
  left
  have hkw : k < W := by rw [← hk]; exact Nat.mod_lt _ (by omega)
  refine ⟨?_, hkw⟩
  have hkk : k % W = k := Nat.mod_eq_of_lt hkw
  rcases (show op = 10 ∨ op = 11 ∨ op = 12 ∨ op = 13 ∨ op = 14 by omega) with rfl | rfl | rfl | rfl | rfl <;>
  simp only [Num.binop, Num.shl, Num.shrS, Num.shrU, Num.rotl, Num.rotr, hk, hkk]

theorem bsum_add (f g : Nat → Nat) (n : Nat) : bsum (fun j => f j + g j) n = bsum f n + bsum g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bsum]; rw [ih]; grind

theorem bsum_split_zero (f : Nat → Nat) (k m : Nat) (h : ∀ j, j < m → f (k + j) = 0) :
    bsum f (k + m) = bsum f k := by
  rw [bsum_split, bsum_zero_of (f := fun j => f (k + j)) h, Nat.mul_zero, Nat.add_zero]

/-- Width-generic shapes: `h` = bytes per word (4 or 8). -/
theorem shift_shapes (c : Nat → Nat) (w1 : c 10 ≤ 1) (h : Nat) (hh : h = 4 + 4 * c 10)
    (upper : c 10 = 0 → (∀ k, 4 ≤ k → k < 8 → c (11 + k) = 0) ∧ c 23 = 0 ∧ c 24 = 0 ∧ c 32 = 0 ∧
      ∀ k, k < 8 → c (56 + k) = 0 ∧ c (72 + k) = 0) :
    (∀ i, i < h → shA c i = c (11 + i)) ∧ (∀ j, j < h → shA c (h + j) = 255 * c 46 * c 6) ∧
    (val8 fun k => c (11 + k)) = bsum (fun i => c (11 + i)) h ∧
    (∀ j, j < 8 → shiftR c j =
      if j < h then (c 5 + c 8 + c 9) * c (48 + j) + (c 6 + c 7 + c 8 + c 9) * c (48 + (h + j)) else 0) := by
  rcases (show c 10 = 0 ∨ c 10 = 1 by omega) with g | g
  · have hh4 : h = 4 := by omega
    subst hh4
    obtain ⟨hz, -, -, -, -⟩ := upper g
    refine ⟨fun i hi => ?_, fun j hj => ?_, ?_, fun j hj => ?_⟩
    · simp [shA, hi]
    · simp only [shA, show ¬ (4 + j < 4) by omega, show 4 + j < 8 by omega, ite_false, ite_true, g]; omega
    · rw [val8_bsum, show (8 : Nat) = 4 + 4 from rfl]
      exact bsum_split_zero _ 4 4 (fun j hj => hz (4 + j) (by omega) (by omega))
    · unfold shiftR
      by_cases hj4 : j < 4
      · simp only [hj4, ite_true, g, Nat.zero_mul, Nat.zero_add, Nat.sub_zero, Nat.one_mul]
        rw [show 48 + j + 4 = 48 + (4 + j) by omega]
      · simp only [hj4, ite_false, g, Nat.zero_mul]
  · have hh8 : h = 8 := by omega
    subst hh8
    refine ⟨fun i hi => ?_, fun j hj => ?_, by rw [val8_bsum], fun j hj => ?_⟩
    · by_cases hi4 : i < 4
      · simp [shA, hi4]
      · simp only [shA, hi4, hi, ite_false, ite_true, g]; omega
    · simp only [shA, show ¬ (8 + j < 4) by omega, show ¬ (8 + j < 8) by omega, show 8 + j < 16 by omega,
        ite_false, ite_true, g]; omega
    · unfold shiftR
      by_cases hj4 : j < 4
      · simp only [hj4, hj, ite_true, g, Nat.one_mul, Nat.sub_self, Nat.zero_mul, Nat.add_zero]
        rw [show 48 + j + 8 = 48 + (8 + j) by omega]
      · simp only [hj4, hj, ite_false, ite_true, g, Nat.one_mul]
        rw [show 48 + j + 8 = 48 + (8 + j) by omega]

/-- **Local soundness of SHIFT.**  An active row computes the spec's `shl` / `shr_s` / `shr_u` /
`rotl` / `rotr` of its operands (count taken mod `w` from the low limb), and its result bytes are
bytes.  Hypotheses: the row's constraints, booleanity of the operation (count `= 1`), and the range
facts its lookups give (operand / product / carry bytes, `q < 2^16`, `2·rest mod p < 256`). -/
theorem shift_sound (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P)
    (hc : ∀ e ∈ Shift.constraints, e.eval (natRow c rw) = 0)
    (hact : c 5 + c 6 + c 7 + c 8 + c 9 = 1)
    (hab : ∀ k, k < 8 → c (11 + k) < 256) (hb0 : c 21 < 65536) (hq : c 33 < 65536)
    (hrest : (2 * c 47) % P < 256)
    (hPb : ∀ j, j < 16 → c (48 + j) < 256) (hcy : ∀ j, j < 16 → c (64 + j) < 256) :
    (c 10 = 0 ∨ c 10 = 1) ∧
    (c 10 = 0 → (∀ k, 4 ≤ k → k < 8 → c (11 + k) = 0) ∧ c 23 = 0 ∧ c 24 = 0) ∧
    (∀ j, j < 8 → shiftR c j < 256) ∧
    (c 10 = 0 → ∀ j, 4 ≤ j → j < 8 → shiftR c j = 0) ∧
    Num.binop (32 + 32 * c 10) (10 + c 6 + 2 * c 7 + 3 * c 8 + 4 * c 9)
      (val8 fun k => c (11 + k)) (val4 (c 21) (c 22) (c 23) (c 24)) = some (val8 (shiftR c)) := by
  obtain ⟨f0, f1, f2, f3, f4, w1, sg, upper, hK, hKw, htop, h47, t0, ht0, eb, heb, hLe, hRe, hlimb⟩ :=
    shift_facts c rw hP hc hact hab hb0 hq hrest hPb hcy
  obtain ⟨h, hh⟩ : ∃ h, h = 4 + 4 * c 10 := ⟨_, rfl⟩
  obtain ⟨hAlo, hAhi, ha8, hR⟩ := shift_shapes c w1 h hh upper
  have hW : 32 + 32 * c 10 = 8 * h := by omega
  have hWc : 8 * h = 32 ∨ 8 * h = 64 := by omega
  have hzero : c 10 = 0 → ∀ j, 4 ≤ j → j < 8 → shiftR c j = 0 := by
    intro h0 j hj1 hj2; rw [hR j hj2]; simp only [show ¬ (j < h) by omega, ite_false]
  refine ⟨by omega, fun h0 => ⟨(upper h0).1, (upper h0).2.1, (upper h0).2.2.1⟩, ?_⟩
  suffices H : (∀ j, j < 8 → shiftR c j < 256) ∧
      Num.binop (8 * h) (10 + c 6 + 2 * c 7 + 3 * c 8 + 4 * c 9)
        (val8 fun k => c (11 + k)) (val4 (c 21) (c 22) (c 23) (c 24)) = some (val8 (shiftR c)) by
    rw [hW]; exact ⟨H.1, hzero, H.2⟩
  generalize hKd : c 27 + 2 * c 28 + 4 * c 29 + 8 * c 30 + 16 * c 31 + 32 * c 32 = K at hK hKw hLe hRe
  rw [hW] at hK hKw hRe
  generalize ha : bsum (fun i => c (11 + i)) h = a at ha8
  have haW : a < 2 ^ (8 * h) := by
    rw [← ha, ← pow256]; exact bsum_lt _ h (fun i hi => hab i (by omega))
  obtain ⟨z, hz⟩ : ∃ z, z = c 46 * c 6 := ⟨_, rfl⟩
  -- the product
  have hprod : bsum (fun j => c (48 + j)) (h + h) =
      ((a + z * (2 ^ (2 * (8 * h)) - 2 ^ (8 * h))) * 2 ^ (eb + 8 * t0)) % 2 ^ (2 * (8 * h)) := by
    have := chain_prod (2 ^ eb) t0 (h + h) (shA c) (fun j => c (48 + j)) (fun j => c (64 + j)) (by omega)
      (fun j hj => hPb j (by omega)) (fun j _ => shA_lt c w1 hab f1 sg j) (fun j hj => hlimb j (by omega))
    rw [this, pow256 t0, ← Nat.pow_add, pow256, show 8 * (h + h) = 2 * (8 * h) by omega]
    congr 2
    rw [bsum_split, bsum_congr (fun i hi => hAlo i hi), ha, bsum_congr (fun j hj => hAhi j hj)]
    have hcst := bsum_const (255 * c 46 * c 6) h
    rw [show 255 * c 46 * c 6 = 255 * z by rw [hz, Nat.mul_assoc]] at hcst ⊢
    rw [pow256] at hcst ⊢
    rw [show 2 * (8 * h) = 8 * h + 8 * h by omega, Nat.pow_add]
    obtain ⟨X, hX⟩ : ∃ X, X = 2 ^ (8 * h) := ⟨_, rfl⟩
    rw [← hX] at hcst ⊢
    generalize bsum (fun _ => 255 * z) h = B at hcst ⊢
    rw [Nat.mul_assoc] at hcst
    have hB : B = z * X - z := by omega
    rw [hB, Nat.mul_sub, Nat.mul_sub, Nat.mul_left_comm X z X, Nat.mul_comm X z]
  -- halves
  generalize hlo : bsum (fun j => c (48 + j)) h = lo
  generalize hhi : bsum (fun j => c (48 + (h + j))) h = hi
  have hsplit : bsum (fun j => c (48 + j)) (h + h) = lo + 2 ^ (8 * h) * hi := by
    rw [bsum_split, hlo, ← pow256, ← hhi]
  have hloW : lo < 2 ^ (8 * h) := by
    rw [← hlo, ← pow256]; exact bsum_lt _ h (fun j hj => hPb j (by omega))
  rw [hsplit] at hprod
  -- the result value
  have hval : val8 (shiftR c) =
      bsum (fun j => (c 5 + c 8 + c 9) * c (48 + j) + (c 6 + c 7 + c 8 + c 9) * c (48 + (h + j))) h := by
    rw [val8_bsum, show bsum (shiftR c) 8 = bsum (shiftR c) (h + (8 - h)) by congr 1; omega,
      bsum_split_zero _ h (8 - h) (fun j hj => by
        rw [hR (h + j) (by omega)]; simp only [show ¬ (h + j < h) by omega, ite_false])]
    exact bsum_congr (fun j hj => by rw [hR j (by omega)]; simp only [hj, ite_true])
  -- the count
  have hcount : val4 (c 21) (c 22) (c 23) (c 24) % (8 * h) = K := by
    rw [count_mod _ _ _ _ _ hWc, hK, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hKw]
  have hbin := fun op hop => ((binop_shift_mod (8 * h) K a (val4 (c 21) (c 22) (c 23) (c 24)) op hop hcount).resolve_right
    (by omega)).1
  rw [ha8, hval]
  have hp8 : ∀ j, j < h → c (48 + j) < 256 := fun j hj => hPb j (by omega)
  have hph : ∀ j, j < h → c (48 + (h + j)) < 256 := fun j hj => hPb (h + j) (by omega)
  have hbL : ∀ j, j < h → lo / 2 ^ (8 * j) % 256 = c (48 + j) := fun j hj => by
    rw [← pow256, ← hlo]; exact bsum_byte _ h j hj hp8
  have hbH : ∀ j, j < h → hi / 2 ^ (8 * j) % 256 = c (48 + (h + j)) := fun j hj => by
    rw [← pow256, ← hhi]; exact bsum_byte _ h j hj hph
  have hrot : ∀ e, e ≤ 8 * h → lo + 2 ^ (8 * h) * hi = (a * 2 ^ e) % 2 ^ (2 * (8 * h)) →
      ∀ j, j < 8 → (if j < h then 1 * c (48 + j) + 1 * c (48 + (h + j)) else 0) < 256 := by
    intro e he hpr j hj
    obtain ⟨hl0, hh0⟩ := rot_halves (8 * h) a e lo hi he haW hloW hpr
    split
    · rw [Nat.one_mul, Nat.one_mul, ← hbL j ‹_›, ← hbH j ‹_›]
      exact byte_disjoint lo hi e (8 * j) hl0 hh0
    · omega
  rcases (show (c 5 = 1 ∧ c 6 = 0 ∧ c 7 = 0 ∧ c 8 = 0 ∧ c 9 = 0) ∨ (c 5 = 0 ∧ c 6 = 1 ∧ c 7 = 0 ∧ c 8 = 0 ∧ c 9 = 0) ∨
      (c 5 = 0 ∧ c 6 = 0 ∧ c 7 = 1 ∧ c 8 = 0 ∧ c 9 = 0) ∨ (c 5 = 0 ∧ c 6 = 0 ∧ c 7 = 0 ∧ c 8 = 1 ∧ c 9 = 0) ∨
      (c 5 = 0 ∧ c 6 = 0 ∧ c 7 = 0 ∧ c 8 = 0 ∧ c 9 = 1) by omega) with
    ⟨g5, g6, g7, g8, g9⟩ | ⟨g5, g6, g7, g8, g9⟩ | ⟨g5, g6, g7, g8, g9⟩ | ⟨g5, g6, g7, g8, g9⟩ | ⟨g5, g6, g7, g8, g9⟩
  · -- shl: e = k, result = low half
    have he : K = eb + 8 * t0 := hLe (by omega)
    rw [← he, hz, g6, Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at hprod
    have r := sem_shl (8 * h) a K lo hi hKw hloW hprod
    simp only [g5, g6, g7, g8, g9, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero, Nat.one_mul, Nat.zero_mul]
    refine ⟨?_, ?_⟩
    · intro j hj; rw [hR j hj]; split
      · simp only [g5, g6, g7, g8, g9, Nat.reduceAdd, Nat.one_mul, Nat.zero_mul, Nat.add_zero]; exact hp8 j ‹_›
      · omega
    · rw [hbin 10 (by omega)]; simp only [Num.binop, Option.some.injEq]; rw [hlo, r]
  · -- shr_s: e = w - k, sign-extended operand, result = high half
    have he : eb + 8 * t0 = 8 * h - K := by have := hRe (by omega); omega
    rw [he, hz, g6, Nat.mul_one] at hprod
    -- the operand's sign: the top byte is `128 sgn + rest`
    have htopb : c (11 + (h - 1)) = 128 * c 46 + c 47 := by
      rcases (show c 10 = 0 ∨ c 10 = 1 by omega) with g | g
      · rw [show 11 + (h - 1) = 14 by omega]; simp only [g] at htop; omega
      · rw [show 11 + (h - 1) = 18 by omega]; simp only [g] at htop; omega
    have hsplit' : a = bsum (fun i => c (11 + i)) (h - 1) + c (11 + (h - 1)) * 256 ^ (h - 1) := by
      rw [← ha, show h = (h - 1) + 1 by omega]; simp only [bsum]; rw [show h - 1 + 1 - 1 = h - 1 by omega]
    have hlow := bsum_lt (fun i => c (11 + i)) (h - 1) (fun i hi => hab i (by omega))
    have h128 : 128 * 256 ^ (h - 1) = 2 ^ (8 * h - 1) := by
      rw [pow256, show (128 : Nat) = 2 ^ 7 from rfl, ← Nat.pow_add]; congr 1; omega
    have hdec : a = 2 ^ (8 * h - 1) * c 46 + (bsum (fun i => c (11 + i)) (h - 1) + c 47 * 256 ^ (h - 1)) := by
      rw [hsplit', htopb, ← h128]; grind
    have hrest' : bsum (fun i => c (11 + i)) (h - 1) + c 47 * 256 ^ (h - 1) < 2 ^ (8 * h - 1) := by
      rw [← h128]
      have : c 47 * 256 ^ (h - 1) ≤ 127 * 256 ^ (h - 1) := Nat.mul_le_mul_right _ (by omega)
      omega
    have r := sem_shrs (8 * h) a K lo hi (c 46) _ hKw hdec sg hrest' hloW hprod
    simp only [g5, g6, g7, g8, g9, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero, Nat.one_mul, Nat.zero_mul,
      Nat.zero_add, Nat.mul_one]
    refine ⟨?_, ?_⟩
    · intro j hj; rw [hR j hj]; split
      · simp only [g5, g6, g7, g8, g9, Nat.reduceAdd, Nat.one_mul, Nat.zero_mul, Nat.zero_add]; exact hph j ‹_›
      · omega
    · rw [hbin 11 (by omega)]; simp only [Num.binop, Option.some.injEq]; rw [hhi, r]
  · -- shr_u: e = w - k, result = high half
    have he : eb + 8 * t0 = 8 * h - K := by have := hRe (by omega); omega
    rw [he, hz, g6, Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at hprod
    have r := sem_shru (8 * h) a K lo hi hKw haW hloW hprod
    simp only [g5, g6, g7, g8, g9, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero, Nat.one_mul, Nat.zero_mul,
      Nat.zero_add]
    refine ⟨?_, ?_⟩
    · intro j hj; rw [hR j hj]; split
      · simp only [g5, g6, g7, g8, g9, Nat.reduceAdd, Nat.one_mul, Nat.zero_mul, Nat.zero_add]; exact hph j ‹_›
      · omega
    · rw [hbin 12 (by omega)]; simp only [Num.binop, Option.some.injEq]; rw [hhi, r]
  · -- rotl: e = k, result = low + high half
    have he : K = eb + 8 * t0 := hLe (by omega)
    rw [← he, hz, g6, Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at hprod
    have r := sem_rotl (8 * h) a K lo hi hKw haW hloW hprod
    have hb := hrot K (by omega) hprod
    simp only [g5, g6, g7, g8, g9, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    refine ⟨fun j hj => by rw [hR j hj]; simpa only [g5, g6, g7, g8, g9, Nat.reduceAdd, Nat.zero_add] using hb j hj, ?_⟩
    rw [hbin 13 (by omega)]; simp only [Num.binop, Option.some.injEq, Nat.one_mul]
    rw [bsum_add, hlo, hhi, r]
  · -- rotr: e = w - k, result = low + high half
    have he : eb + 8 * t0 = 8 * h - K := by have := hRe (by omega); omega
    rw [he, hz, g6, Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at hprod
    have r := sem_rotr (8 * h) a K lo hi (by omega) hKw haW hloW hprod
    have hb := hrot (8 * h - K) (by omega) hprod
    simp only [g5, g6, g7, g8, g9, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    refine ⟨fun j hj => by rw [hR j hj]; simpa only [g5, g6, g7, g8, g9, Nat.reduceAdd, Nat.zero_add] using hb j hj, ?_⟩
    rw [hbin 14 (by omega)]; simp only [Num.binop, Option.some.injEq, Nat.one_mul]
    rw [bsum_add, hlo, hhi, r]
