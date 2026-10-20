import WasmBase.Local.Div
import WasmBase.Check
/-!
# WasmBase.Local.Call — the local constraints of CALL and RET as `Nat` facts
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local

/-- `Nat` sum of the cells `f j`, `j ∈ l`. -/
def cellSum (c : Nat → Nat) (f : Nat → Nat) (l : List Nat) : Nat := (l.map fun j => c (f j)).foldl (· + ·) 0

theorem foldl_add_acc (l : List Nat) (a : Nat) : l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp only [List.foldl_cons]; rw [ih (a + x), ih (0 + x)]; omega

theorem cellSum_cons (c f : Nat → Nat) (j : Nat) (l : List Nat) :
    cellSum c f (j :: l) = c (f j) + cellSum c f l := by
  simp only [cellSum, List.map_cons, List.foldl_cons, Nat.zero_add]
  exact foldl_add_acc _ _

theorem eval_sumE (c : Nat → Nat) (rw : Row) (f : Nat → Nat) :
    ∀ (l : List Nat) (a : Expr), ((l.map fun j => v (f j)).foldl (· + ·) a).eval (natRow c rw) =
      a.eval (natRow c rw) + ((cellSum c f l : Nat) : F)
  | [], a => by
    show _ = _ + ((0 : Nat) : F)
    grind
  | j :: l, a => by
    simp only [List.map_cons, List.foldl_cons]
    rw [eval_sumE c rw f l (a + v (f j)), cellSum_cons]
    simp only [Expr.eval_add', v, Expr.eval_col, natRow_cur, Lean.Grind.Semiring.natCast_add]
    grind

theorem cellSum_le (c f : Nat → Nat) (b : Nat) : ∀ (l : List Nat), (∀ j ∈ l, c (f j) ≤ b) →
    cellSum c f l ≤ b * l.length
  | [], _ => by simp [cellSum]
  | j :: l, h => by
    rw [cellSum_cons]
    have h1 := h j List.mem_cons_self
    have h2 := cellSum_le c f b l (fun i hi => h i (List.mem_cons_of_mem _ hi))
    simp only [List.length_cons, Nat.mul_succ]; omega

theorem prefix_down (b : Nat → Nat) (n : Nat) (hb : ∀ j, j < n + 1 → b j ≤ 1)
    (hp : ∀ j, j + 1 < n + 1 → b (j + 1) ≤ b j) (hn : b n = 1) : ∀ d j, j + d = n → b j = 1 := by
  intro d
  induction d with
  | zero => intro j hj; rw [Nat.add_zero] at hj; rw [hj]; exact hn
  | succ d ih =>
    intro j hj
    have h1 := ih (j + 1) (by omega)
    have := hp j (by omega); have := hb j (by omega); omega

/-- A prefix-closed bit vector: bit `j` is set iff `j` is below the number of set bits. -/
theorem prefix_bits (b : Nat → Nat) : ∀ (n : Nat), (∀ j, j < n → b j ≤ 1) → (∀ j, j + 1 < n → b (j + 1) ≤ b j) →
    ∀ j, j < n → (b j = 1 ↔ j < cellSum b id (List.range n))
  | 0, _, _, j, hj => absurd hj (by omega)
  | n + 1, hb, hp, j, hj => by
    have ih := prefix_bits b n (fun j hj => hb j (by omega)) (fun j hj => hp j (by omega))
    have hs : cellSum b id (List.range (n + 1)) = cellSum b id (List.range n) + b n := by
      simp only [cellSum, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
        List.foldl_cons, List.foldl_nil, id]
    have hle : cellSum b id (List.range n) ≤ n := by
      have := cellSum_le b id 1 (List.range n) (fun i hi => hb i (by rw [List.mem_range] at hi; omega))
      simpa using this
    rw [hs]
    have hbn := hb n (by omega)
    rcases (show b n = 0 ∨ b n = 1 by omega) with h0 | h1
    · rw [h0, Nat.add_zero]
      by_cases hjn : j < n
      · exact ih j hjn
      · have : j = n := by omega
        subst this; rw [h0]; omega
    · have all1 : ∀ i, i ≤ n → b i = 1 := fun i hi => prefix_down b n hb hp h1 (n - i) i (by omega)
      have hsum : cellSum b id (List.range n) = n := by
        rcases Nat.lt_or_ge (cellSum b id (List.range n)) n with hlt | hge
        · have := (ih _ hlt).mp (all1 _ (by omega))
          omega
        · omega
      rw [hsum, h1, all1 j (by omega)]
      omega

/-- Weighted `Nat` sum `Σ w i · c (g i)`, `i ∈ l`. -/
def wSum (c : Nat → Nat) (w g : Nat → Nat) (l : List Nat) : Nat := (l.map fun i => w i * c (g i)).foldl (· + ·) 0

theorem wSum_cons (c w g : Nat → Nat) (i : Nat) (l : List Nat) :
    wSum c w g (i :: l) = w i * c (g i) + wSum c w g l := by
  simp only [wSum, List.map_cons, List.foldl_cons, Nat.zero_add]
  exact foldl_add_acc _ _

theorem eval_wSum (c : Nat → Nat) (rw : Row) (w g : Nat → Nat) :
    ∀ (l : List Nat) (a : Expr), ((l.map fun i => Expr.c (w i) * v (g i)).foldl (· + ·) a).eval (natRow c rw) =
      a.eval (natRow c rw) + ((wSum c w g l : Nat) : F)
  | [], a => by
    show _ = _ + ((0 : Nat) : F)
    grind
  | i :: l, a => by
    simp only [List.map_cons, List.foldl_cons]
    rw [eval_wSum c rw w g l (a + Expr.c (w i) * v (g i)), wSum_cons]
    simp only [Expr.eval_add', Expr.eval_mul', Expr.eval_c, v, Expr.eval_col, natRow_cur,
      Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
    grind

theorem wSum_le (c w g : Nat → Nat) : ∀ (l : List Nat), (∀ i ∈ l, c (g i) ≤ 1) →
    wSum c w g l ≤ (l.map w).foldl (· + ·) 0
  | [], _ => by simp [wSum]
  | i :: l, h => by
    rw [wSum_cons]
    simp only [List.map_cons, List.foldl_cons, Nat.zero_add]
    rw [foldl_add_acc]
    have h1 := h i List.mem_cons_self
    have h2 := wSum_le c w g l (fun j hj => h j (List.mem_cons_of_mem _ hj))
    have : w i * c (g i) ≤ w i := by
      rcases (show c (g i) = 0 ∨ c (g i) = 1 by omega) with e | e <;> rw [e] <;> simp
    omega

theorem le_of_mulsub {c : Nat → Nat} {rw : Row} (hP : ∀ i, c i < P) {x y : Nat} (hx : c x ≤ 1) (hy : c y ≤ 1)
    (h : (v x * (1 - v y)).eval (natRow c rw) = 0) : c x ≤ c y := by
  simp only [v, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Expr.eval_col, natRow_cur] at h
  rcases mul_eq_zero' h with h0 | h1
  · have := natEq (h0.trans (by rfl : (0 : F) = ((0 : Nat) : F))) (hP x) (by decide); omega
  · have : ((c y : Nat) : F) = ((1 : Nat) : F) := by grind
    have := natEq this (hP y) (by decide); omega

/-- The CALL constraints as `Nat` facts (the field equations of the budget, the new base and the
clock are kept as field equations: their bounds come from range lookups). -/
theorem call_sound (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P)
    (hc : ∀ e ∈ Call.constraints, e.eval (natRow c rw) = 0) :
    c Call.act ≤ 1 ∧ c (Call.af 0) ≤ c Call.act ∧
    (∀ j, j < 8 → c (Call.pf j) ≤ 1 ∧ c (Call.pf j) ≤ c (Call.af j)) ∧
    (∀ j, j + 1 < 8 → c (Call.pf (j + 1)) ≤ c (Call.pf j)) ∧
    (∀ j, j < 64 → c (Call.af j) ≤ 1 ∧ c (Call.tg j) ≤ 1) ∧
    (∀ j, j + 1 < 64 → c (Call.af (j + 1)) ≤ c (Call.af j)) ∧
    c Call.shape = cellSum c Call.pf (List.range 8) + 128 * cellSum c Call.af (List.range 64) ∧
    (∀ q, q < 4 → c (Call.m q) = wSum c (fun i => 2 ^ i) (fun i => Call.tg (16 * q + i)) (List.range 16)) ∧
    (Call.np.eval (natRow c rw) = ((cellSum c Call.pf (List.range 8) : Nat) : F)) ∧
    (Call.nl.eval (natRow c rw) = ((cellSum c Call.af (List.range 64) : Nat) : F)) ∧
    (v Call.n0 + B16 * v Call.n1 + v Call.charge - v Call.r0 - B16 * v Call.r1).eval (natRow c rw) = 0 ∧
    (Call.sbNew - v Call.sbn0 - B16 * v Call.sbn1).eval (natRow c rw) = 0 ∧
    (v cTs - v Call.ts0 - B16 * v Call.ts1).eval (natRow c rw) = 0 := by
  have hP' := P_val
  have mAct : Chips.bool (v Call.act) ∈ Call.constraints := by
    simp only [Call.constraints, List.mem_append, List.mem_cons]; simp
  have mAf0 : v (Call.af 0) * (1 - v Call.act) ∈ Call.constraints := by
    simp only [Call.constraints, List.mem_append, List.mem_cons]; simp
  have mPf : ∀ j, j < 8 → Chips.bool (v (Call.pf j)) ∈ Call.constraints ∧
      v (Call.pf j) * (1 - v (Call.af j)) ∈ Call.constraints := by
    intro j hj
    constructor <;>
    simp only [Call.constraints, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_cons,
      List.mem_nil_iff, or_false]
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨j, hj, Or.inl rfl⟩)))))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨j, hj, Or.inr rfl⟩)))))))
  have mPp : ∀ j, j < 7 → v (Call.pf (j + 1)) * (1 - v (Call.pf j)) ∈ Call.constraints := by
    intro j hj
    simp only [Call.constraints, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_cons,
      List.mem_nil_iff, or_false]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨j, hj, rfl⟩))))))
  have mAf : ∀ j, j < 64 → Chips.bool (v (Call.af j)) ∈ Call.constraints := by
    intro j hj
    simp only [Call.constraints, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_cons,
      List.mem_nil_iff, or_false]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨j, hj, rfl⟩)))))
  have mAp : ∀ j, j < 63 → v (Call.af (j + 1)) * (1 - v (Call.af j)) ∈ Call.constraints := by
    intro j hj
    simp only [Call.constraints, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_cons,
      List.mem_nil_iff, or_false]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨j, hj, rfl⟩))))
  have mTg : ∀ j, j < 64 → Chips.bool (v (Call.tg j)) ∈ Call.constraints := by
    intro j hj
    simp only [Call.constraints, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_cons,
      List.mem_nil_iff, or_false]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨j, hj, rfl⟩)))
  have mSh : v Call.shape - Call.np - 128 * Call.nl ∈ Call.constraints := by
    simp only [Call.constraints, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_cons,
      List.mem_nil_iff, or_false]
    exact Or.inl (Or.inl (Or.inr trivial))
  have mM : ∀ q, q < 4 → v (Call.m q) - Call.maskOf q ∈ Call.constraints := by
    intro q hq
    simp only [Call.constraints, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_cons,
      List.mem_nil_iff, or_false]
    exact Or.inl (Or.inr ⟨q, hq, rfl⟩)
  have mB : v Call.n0 + B16 * v Call.n1 + v Call.charge - v Call.r0 - B16 * v Call.r1 ∈ Call.constraints := by
    simp only [Call.constraints, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_cons,
      List.mem_nil_iff, or_false]
    exact Or.inr (Or.inl trivial)
  have mS : Call.sbNew - v Call.sbn0 - B16 * v Call.sbn1 ∈ Call.constraints := by
    simp only [Call.constraints, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_cons,
      List.mem_nil_iff, or_false]
    exact Or.inr (Or.inr (Or.inl trivial))
  have mT : v cTs - v Call.ts0 - B16 * v Call.ts1 ∈ Call.constraints := by
    simp only [Call.constraints, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_cons,
      List.mem_nil_iff, or_false]
    exact Or.inr (Or.inr (Or.inr trivial))
  have hact := bit_of hP (hc _ mAct)
  have hpf : ∀ j, j < 8 → c (Call.pf j) ≤ 1 := fun j hj => bit_of hP (hc _ (mPf j hj).1)
  have haf : ∀ j, j < 64 → c (Call.af j) ≤ 1 := fun j hj => bit_of hP (hc _ (mAf j hj))
  have htg : ∀ j, j < 64 → c (Call.tg j) ≤ 1 := fun j hj => bit_of hP (hc _ (mTg j hj))
  have enp : Call.np.eval (natRow c rw) = ((cellSum c Call.pf (List.range 8) : Nat) : F) := by
    unfold Call.np; rw [eval_sumE]; show ((0 : Nat) : F) + _ = _; grind
  have enl : Call.nl.eval (natRow c rw) = ((cellSum c Call.af (List.range 64) : Nat) : F) := by
    unfold Call.nl; rw [eval_sumE]; show ((0 : Nat) : F) + _ = _; grind
  have snp : cellSum c Call.pf (List.range 8) ≤ 8 := by
    have := cellSum_le c Call.pf 1 (List.range 8) (fun j hj => hpf j (List.mem_range.mp hj)); simpa using this
  have snl : cellSum c Call.af (List.range 64) ≤ 64 := by
    have := cellSum_le c Call.af 1 (List.range 64) (fun j hj => haf j (List.mem_range.mp hj)); simpa using this
  refine ⟨hact, ?_, fun j hj => ⟨hpf j hj, ?_⟩, fun j hj => ?_, fun j hj => ⟨haf j hj, htg j hj⟩, fun j hj => ?_,
    ?_, fun q hq => ?_, enp, enl, hc _ mB, hc _ mS, hc _ mT⟩
  · exact le_of_mulsub hP (haf 0 (by decide)) hact (hc _ mAf0)
  · exact le_of_mulsub hP (hpf j hj) (haf j (by omega)) (hc _ (mPf j hj).2)
  · exact le_of_mulsub hP (hpf (j + 1) hj) (hpf j (by omega)) (hc _ (mPp j (by omega)))
  · exact le_of_mulsub hP (haf (j + 1) hj) (haf j (by omega)) (hc _ (mAp j (by omega)))
  · have h := hc _ mSh
    simp only [Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, enp, enl] at h
    have e : ((c Call.shape : Nat) : F) = ((cellSum c Call.pf (List.range 8) + 128 * cellSum c Call.af (List.range 64) : Nat) : F) := by
      rw [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]; grind
    exact natEq e (hP _) (by omega)
  · have h := hc _ (mM q hq)
    unfold Call.maskOf at h
    rw [Expr.eval_sub', eval_wSum c rw (fun i => 2 ^ i) (fun i => Call.tg (16 * q + i))] at h
    simp only [v, Expr.eval_col, natRow_cur] at h
    have hw := wSum_le c (fun i => 2 ^ i) (fun i => Call.tg (16 * q + i)) (List.range 16)
      (fun i hi => htg _ (by rw [List.mem_range] at hi; omega))
    have h65 : ((List.range 16).map fun i => 2 ^ i).foldl (· + ·) 0 = 65535 := by decide
    rw [h65] at hw
    have e : ((c (Call.m q) : Nat) : F) = ((wSum c (fun i => 2 ^ i) (fun i => Call.tg (16 * q + i)) (List.range 16) : Nat) : F) := by
      have h0 : Expr.eval (natRow c rw) (0 : Expr) = ((0 : Nat) : F) := rfl
      rw [h0] at h; grind
    exact natEq e (hP _) (by omega)

/-! ## Binary digits -/

theorem geom_sum : ∀ n : Nat, ((List.range n).map fun i => 2 ^ i).foldl (· + ·) 0 = 2 ^ n - 1
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [geom_sum n]
    have := Nat.one_le_two_pow (n := n); rw [Nat.pow_succ]; omega

/-- `Σ_{i<n} 2^i b_i` with bits `b_i` determines the bits. -/
theorem bits_unique (b : Nat → Nat) : ∀ (n x : Nat), (∀ i, i < n → b i ≤ 1) →
    ((List.range n).map fun i => 2 ^ i * b i).foldl (· + ·) 0 = x → ∀ i, i < n → b i = x / 2 ^ i % 2
  | 0, _, _, _, i, hi => absurd hi (by omega)
  | n + 1, x, hb, hx, i, hi => by
    rw [List.range_succ, List.map_append, List.foldl_append] at hx
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at hx
    obtain ⟨y, hy⟩ : ∃ y, y = ((List.range n).map fun i => 2 ^ i * b i).foldl (· + ·) 0 := ⟨_, rfl⟩
    rw [← hy] at hx
    have hyl : y < 2 ^ n := by
      have := wSum_le b (fun i => 2 ^ i) id (List.range n) (fun i hi => hb i (by rw [List.mem_range] at hi; omega))
      have e := geom_sum n
      simp only [wSum, id] at this
      rw [e] at this
      have := Nat.one_le_two_pow (n := n)
      omega
    have hbn := hb n (by omega)
    by_cases hin : i < n
    · have ih := bits_unique b n y (fun i hi => hb i (by omega)) hy.symm i hin
      rw [ih, ← hx]
      have hd : 2 ^ n = 2 ^ i * 2 ^ (n - i) := by rw [← Nat.pow_add]; congr 1; omega
      rw [hd, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos i)]
      have he : 2 ^ (n - i) = 2 * 2 ^ (n - i - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      rw [he, Nat.mul_assoc, Nat.add_mul_mod_self_left]
    · have hin' : i = n := by omega
      subst hin'
      rw [← hx, Nat.add_mul_div_left _ _ (Nat.two_pow_pos i), Nat.div_eq_of_lt hyl, Nat.zero_add]
      omega

theorem div_mod_two_of_mod (y i : Nat) (hi : i < 16) : (y % 65536) / 2 ^ i % 2 = y / 2 ^ i % 2 := by
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self]
  congr 1
  have hd : 2 ^ i * 2 ∣ 65536 := by
    have : 65536 = 2 ^ i * 2 * 2 ^ (15 - i) := by
      rw [← Nat.pow_succ, ← Nat.pow_add]; rw [show i + 1 + (15 - i) = 16 by omega]
    rw [this]; exact Nat.dvd_mul_right _ _
  exact Nat.mod_mod_of_dvd y hd

/-- The type bits of the CALL row are the locals' tags (the mask limbs of the function table). -/
theorem mask_bits (tags : List Nat) (hb : ∀ i, tags.getD i 0 ≤ 1) (tg : Nat → Nat) (htg : ∀ j, j < 64 → tg j ≤ 1)
    (hm : ∀ q, q < 4 → ((List.range 16).map fun i => 2 ^ i * tg (16 * q + i)).foldl (· + ·) 0 =
      (limbs4 (maskOf tags)).getD q 0) :
    ∀ j, j < 64 → tg j = tags.getD j 0 := by
  intro j hj
  have hq : j / 16 < 4 := by omega
  have e := bits_unique (fun i => tg (16 * (j / 16) + i)) 16 _ (fun i hi => htg _ (by omega)) (hm (j / 16) hq)
    (j % 16) (Nat.mod_lt _ (by decide))
  rw [show 16 * (j / 16) + j % 16 = j by omega] at e
  rw [e]
  have hmask := bits_unique (fun i => tags.getD i 0) 64 (maskOf tags) (fun i _ => hb i) rfl j hj
  rw [hmask]
  have hl : (limbs4 (maskOf tags)).getD (j / 16) 0 = maskOf tags / 2 ^ (16 * (j / 16)) % 65536 := by
    rcases (show j / 16 = 0 ∨ j / 16 = 1 ∨ j / 16 = 2 ∨ j / 16 = 3 by omega) with h | h | h | h <;>
      rw [h] <;> simp [limbs4]
  rw [hl, div_mod_two_of_mod _ _ (Nat.mod_lt _ (by decide)), Nat.div_div_eq_div_mul, ← Nat.pow_add,
    show 16 * (j / 16) + j % 16 = j by omega]

end WasmBase
