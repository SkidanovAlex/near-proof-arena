import ZkFormal.NearV3.D1.Extract.Tx.ChainC

/-!
# `ZkFormal.NearV3.D1.Extract.Tx.ChainQ` — the storage chains `Q` (`10¹⁹·storage`), `D` (stake
comparison), `S` (`storage ≤ 770`)

* delay line `dl x` on lane `k` = `st_{k−1−x}` (`0` before the op);
* `Q`: `q + 256·cq = Σⱼ Sⱼ·st_{k−j} + cin` = `convS st k + cin`, so
  `q + 2¹²⁸·cq₁₅ = 10¹⁹·storage − 2¹²⁸·convR`;
* `D`: `tT + 2¹²⁸·boQ₁₅ = dQ + q`;
* `S`: `770 + 2¹²⁸·boS₁₅ = dS + storage`.
-/

namespace ZkFormal.NearV3.D1.TxProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.TxV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem qb_bool : ∀ b, b < 8 → qb b ∈ boolCols := by
  intro b hb; simp [boolCols, qb, hb]
theorem cqb_bool : ∀ b, b < 12 → cqb b ∈ boolCols := by
  intro b hb; simp [boolCols, cqb, hb]
theorem dQb_bool : ∀ b, b < 8 → dQb b ∈ boolCols := by
  intro b hb; simp [boolCols, dQb, hb]
theorem dSb_bool : ∀ b, b < 8 → dSb b ∈ boolCols := by
  intro b hb; simp [boolCols, dSb, hb]

theorem convC_eq : convC = sum [smul 0 (c st), smul 0 (c (dl 0)), smul 232 (c (dl 1)),
    smul 137 (c (dl 2)), smul 4 (c (dl 3)), smul 35 (c (dl 4)), smul 199 (c (dl 5)),
    smul 138 (c (dl 6))] := rfl
theorem convN_eq : convN = sum [smul 0 (n st), smul 0 (n (dl 0)), smul 232 (n (dl 1)),
    smul 137 (n (dl 2)), smul 4 (n (dl 3)), smul 35 (n (dl 4)), smul 199 (n (dl 5)),
    smul 138 (n (dl 6))] := rfl

section
variable (hL : TableLocal TxV3.table tr tt pub)
include hL

/-- **Delay line.** -/
theorem dl_val {s : Nat} (hop : OpAt tr tt s) :
    ∀ k, k < 16 → ∀ x, x < 7 →
      tr.cell tt (s + k) (dl x) = if x + 1 ≤ k then tr.cell tt (s + (k - (x + 1))) st else 0 := by
  have hH := hop.h
  intro k
  induction k with
  | zero =>
    intro _ x hx
    have e := con hL (r := s) (by omega)
      (mem_chains (e := first (c (dl x))) (by
        simp [cChains, chain, show ∃ a, a < 7 ∧ first (c (dl a)) = first (c (dl x)) from ⟨x, hx, rfl⟩]))
    have hlf := hop.lf 0 (by omega)
    simp only [Nat.add_zero, ite_true] at hlf
    simp only [first, eval_mul, eval_c, hlf] at e
    simp only [Nat.add_zero, show ¬ x + 1 ≤ 0 by omega, ite_false]
    grind
  | succ k ih =>
    intro hk x hx
    have hac := hop.act k (by omega)
    have hl := hop.ll k (by omega)
    rw [if_neg (by omega)] at hl
    have hn : s + k + 1 < tr.height tt := by omega
    rcases Nat.eq_zero_or_pos x with h0 | hpos
    · subst h0
      have e := con hL (r := s + k) (by omega)
        (mem_chains (e := inOpE (sub (n (dl 0)) (c st))) (by simp [cChains, chain]))
      simp only [inOpE, inOp, eval_mul, eval_sub, eval_c, eval_n, eval_not, hac, hl, nxt hn] at e
      simp only [show 0 + 1 ≤ k + 1 by omega, ite_true, show k + 1 - (0 + 1) = k by omega,
        ← Nat.add_assoc]
      grind
    · have e := con hL (r := s + k) (by omega)
        (mem_chains (e := inOpE (sub (n (dl (x - 1 + 1))) (c (dl (x - 1)))))
          (by simp [cChains, chain, show ∃ a, a < 6 ∧ inOpE (sub (n (dl (a + 1))) (c (dl a))) =
                inOpE (sub (n (dl (x - 1 + 1))) (c (dl (x - 1)))) from ⟨x - 1, by omega, rfl⟩]))
      simp only [inOpE, inOp, eval_mul, eval_sub, eval_c, eval_n, eval_not, hac, hl, nxt hn,
        show x - 1 + 1 = x by omega] at e
      have i := ih (by omega) (x - 1) (by omega)
      rw [← Nat.add_assoc]
      by_cases hc : x + 1 ≤ k + 1
      · rw [if_pos hc]
        rw [if_pos (show x - 1 + 1 ≤ k by omega), show k - (x - 1 + 1) = k + 1 - (x + 1) by omega] at i
        grind
      · rw [if_neg hc]
        rw [if_neg (show ¬ x - 1 + 1 ≤ k by omega)] at i
        grind

theorem dl_cv {s : Nat} (hop : OpAt tr tt s) (k : Nat) (hk : k < 16) (x : Nat) (hx : x < 7) :
    cv tr tt (s + k) (dl x) = if x + 1 ≤ k then cv tr tt (s + (k - (x + 1))) st else 0 := by
  unfold cv; rw [dl_val hL hop k hk x hx]; split <;> simp [Fp.toNat_zero]

/-- The convolution of lane `k` over the delay line, as naturals. -/
def convDl (tr : Trace Fp) (tt r : Nat) : Nat :=
  232 * cv tr tt r (dl 1) + 137 * cv tr tt r (dl 2) + 4 * cv tr tt r (dl 3) + 35 * cv tr tt r (dl 4) +
    199 * cv tr tt r (dl 5) + 138 * cv tr tt r (dl 6)

theorem convDl_eq {s : Nat} (hop : OpAt tr tt s) (k : Nat) (hk : k < 16) :
    convDl tr tt (s + k) = RcptProof.convS (fun j => cv tr tt (s + j) st) k := by
  unfold convDl RcptProof.convS
  rw [dl_cv hL hop k hk 1 (by omega), dl_cv hL hop k hk 2 (by omega), dl_cv hL hop k hk 3 (by omega),
    dl_cv hL hop k hk 4 (by omega), dl_cv hL hop k hk 5 (by omega), dl_cv hL hop k hk 6 (by omega)]

theorem convDl_le {s : Nat} (hop : OpAt tr tt s) (k : Nat) (hk : k < 16)
    (hst : ∀ j, j < 16 → cv tr tt (s + j) st < 256) : convDl tr tt (s + k) ≤ 745 * 255 := by
  rw [convDl_eq hL hop k hk]; unfold RcptProof.convS; dsimp only
  have h : ∀ i, (if i ≤ k then cv tr tt (s + (k - i)) st else 0) ≤ 255 := fun i => by
    split
    · have := hst (k - i) (by omega); omega
    · omega
  have := h 2; have := h 3; have := h 4; have := h 5; have := h 6; have := h 7
  omega

/-- Lane `k` of chain `Q`. -/
theorem laneQ {s : Nat} (hop : OpAt tr tt s) (k : Nat) (hk : k < 16)
    (hst : ∀ j, j < 16 → cv tr tt (s + j) st < 256) :
    bv tr tt (s + k) qb + 256 * bv tr tt (s + k) cqb 12 =
      convDl tr tt (s + k) + (if k = 0 then 0 else bv tr tt (s + k - 1) cqb 12) := by
  have hH := hop.h
  have hq := bv_lt hL (r := s + k) (by omega) qb_bool
  have hc := bv_lt hL (r := s + k) (by omega) cqb_bool
  have hcv := convDl_le hL hop k hk hst
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    have e := con hL (r := s) (by omega)
      (mem_chains (e := first (sub (.add q (smul 256 cq)) convC)) (by simp [cChains, chain]))
    have hlf := hop.lf 0 (by omega)
    simp only [Nat.add_zero, ite_true] at hlf hq hc hcv ⊢
    simp only [first, q, cq, byteC, convC_eq, eval_mul, eval_sub, eval_add, eval_c, eval_k, eval_smul,
      eval_sum_cons, eval_sum_nil, hlf, eval_byte hL (r := s) (by omega) qb_bool,
      eval_byte hL (r := s) (by omega) cqb_bool] at e
    apply natEq (by unfold P; omega) (by unfold P; omega)
    simp only [convDl, natCast_add, natCast_mul, ← cell_eq_cast]
    grind
  · have hc' := bv_lt hL (r := s + k - 1) (by omega) cqb_bool
    have e := con hL (r := s + k - 1) (by omega)
      (mem_chains (e := inOpE (sub (.add (byteN qb) (smul 256 cqN)) (.add convN cq)))
        (by simp [cChains, chain]))
    have hac := hop.act (k - 1) (by omega)
    have hl := hop.ll (k - 1) (by omega)
    rw [if_neg (by omega)] at hl
    rw [show s + (k - 1) = s + k - 1 by omega] at hac hl
    have hn : s + k - 1 + 1 < tr.height tt := by omega
    simp only [inOpE, inOp, byteN, cqN, cq, convN_eq, eval_mul, eval_sub, eval_add, eval_c, eval_n,
      eval_k, eval_smul, eval_not, eval_sum_cons, eval_sum_nil, hac, hl, eval_bitsN hn, nxt hn,
      show s + k - 1 + 1 = s + k by omega, Nat.mod_eq_of_lt (show s + k < tr.height tt by omega),
      eval_byte hL (r := s + k) (by omega) qb_bool, eval_byte hL (r := s + k) (by omega) cqb_bool,
      eval_byte hL (r := s + k - 1) (by omega) cqb_bool] at e
    rw [if_neg (by omega)]
    apply natEq (by unfold P; omega) (by unfold P; omega)
    simp only [convDl, natCast_add, natCast_mul, ← cell_eq_cast]
    grind

/-- **Chain `Q`**: `q = 10¹⁹·storage mod 2¹²⁸`. -/
theorem chainQ {s : Nat} (hop : OpAt tr tt s) (hst : ∀ j, j < 16 → cv tr tt (s + j) st < 256) :
    RcptProof.sumL (fun j => bv tr tt (s + j) qb) 16 =
      (NearSpec.Params.storageAmountPerByte * RcptProof.sumL (fun j => cv tr tt (s + j) st) 16) %
        NearSpec.Params.two128 := by
  have hc := RcptProof.chainC 16 (by omega) (fun j => bv tr tt (s + j) qb)
    (fun j => RcptProof.convS (fun j => cv tr tt (s + j) st) j)
    (fun j => if j = 0 then 0 else bv tr tt (s + j - 1) cqb 12) (fun j => bv tr tt (s + j) cqb 12)
    (fun j hj => by rw [← convDl_eq hL hop j hj]; exact laneQ hL hop j hj hst)
    (fun j hj => by simp [show s + (j + 1) - 1 = s + j by omega])
  have hid := RcptProof.convS_id (fun j => cv tr tt (s + j) st)
  have hlt := RcptProof.sumL_lt (fun j => bv tr tt (s + j) qb) 16 (fun j hj =>
    bv_lt hL (r := s + j) (by have := hop.h; omega) qb_bool)
  rw [← RcptProof.two128] at hlt
  simp only [ite_true, Nat.add_zero] at hc
  rw [RcptProof.two128] at hid ⊢
  rw [RcptProof.two128] at hlt
  rw [hid, ← hc, Nat.add_assoc, ← Nat.mul_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

end

end ZkFormal.NearV3.D1.TxProof
