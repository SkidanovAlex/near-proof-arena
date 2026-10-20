import NearSpecV3.TxD1
import ZkFormal.Algebra.Fp

/-!
# `ZkFormal.NearV3.D1.Extract.Akm.Utf8Abs` — the `akmV3` UTF-8 automaton accepts only `NearSpecV3.utf8Ok`

Pure lemma (no trace).  A string body of `R` bytes `x 0 … x (R−1)` with, per byte, a class
(`0` ASCII, `1` continuation, `2`/`3`/`4` lead of a 2/3/4-byte sequence), a pending count `u`
(a field element: `u 0 = 0`, `u (j+1) = [2] + 2·[3] + 3·[4] + [1]·(u j − 1)`, the last byte's
successor value `0`, a non-continuation needs `u = 0`), and the second-byte flags after
`E0`/`ED`/`F0`/`F4`: then `NearSpecV3.utf8Ok` holds.
-/

namespace ZkFormal.NearV3.D1.AkmProof

open ZkFormal.Algebra

/-- The class facts of one byte. -/
def ClassOk (k x : Nat) : Prop :=
  (k = 0 ∧ x < 0x80) ∨ (k = 1 ∧ 0x80 ≤ x ∧ x ≤ 0xBF) ∨ (k = 2 ∧ 0xC2 ≤ x ∧ x ≤ 0xDF) ∨
    (k = 3 ∧ 0xE0 ≤ x ∧ x ≤ 0xEF) ∨ (k = 4 ∧ 0xF0 ≤ x ∧ x ≤ 0xF4)

/-- The successor pending count. -/
def ucnF (k : Nat) (u : Fp) : Fp :=
  if k = 2 then 1 else if k = 3 then 2 else if k = 4 then 3 else if k = 1 then u - 1 else 0

structure U8Rows (R : Nat) (x k : Nat → Nat) (u : Nat → Fp) (e0 ed f0 f4 : Nat → Bool) : Prop where
  cls : ∀ j, j < R → ClassOk (k j) (x j)
  lead : ∀ j, j < R → k j ≠ 1 → u j = 0
  step : ∀ j, j + 1 < R → u (j + 1) = ucnF (k j) (u j)
  stop : 0 < R → ucnF (k (R - 1)) (u (R - 1)) = 0
  start : 0 < R → u 0 = 0
  /-- second-byte flags (set on the byte after the lead) -/
  fE0 : ∀ j, j + 1 < R → k j = 3 → x j = 0xE0 → k (j + 1) = 1 → 0xA0 ≤ x (j + 1)
  fED : ∀ j, j + 1 < R → k j = 3 → x j = 0xED → k (j + 1) = 1 → x (j + 1) ≤ 0x9F
  fF0 : ∀ j, j + 1 < R → k j = 4 → x j = 0xF0 → k (j + 1) = 1 → 0x90 ≤ x (j + 1)
  fF4 : ∀ j, j + 1 < R → k j = 4 → x j = 0xF4 → k (j + 1) = 1 → x (j + 1) ≤ 0x8F

theorem fp_one_ne_zero' : (1 : Fp) ≠ 0 := by decide

theorem fp_ofNat_ne_zero {n : Nat} (h0 : 0 < n) (hP : n < P) : ((n : Nat) : Fp) ≠ 0 := by
  intro h
  have := congrArg Fp.toNat h
  rw [show ((n : Nat) : Fp) = Fp.ofNat n from rfl, Fp.toNat_ofNat, Nat.mod_eq_of_lt hP] at this
  rw [Fp.toNat_zero] at this; omega

theorem utf8_a (a : UInt8) (l : List UInt8) (h : a.toNat < 128) : NearSpecV3.utf8Ok (a :: l) = NearSpecV3.utf8Ok l := by
  conv => lhs; unfold NearSpecV3.utf8Ok
  simp only [h, ite_true]
theorem utf8_2 (a b : UInt8) (l : List UInt8) (h1 : 194 ≤ a.toNat) (h2 : a.toNat ≤ 223)
    (hb1 : 128 ≤ b.toNat) (hb2 : b.toNat ≤ 191) : NearSpecV3.utf8Ok (a :: b :: l) = NearSpecV3.utf8Ok l := by
  conv => lhs; unfold NearSpecV3.utf8Ok
  simp only [show ¬ a.toNat < 128 by omega, ite_false, h1, h2, decide_true, Bool.and_self, ite_true, hb1, hb2,
    Bool.true_and]
theorem utf8_3 (a b c : UInt8) (l : List UInt8) (h1 : 224 ≤ a.toNat) (h2 : a.toNat ≤ 239)
    (hb1 : (if a.toNat = 224 then 160 else 128) ≤ b.toNat) (hb2 : b.toNat ≤ (if a.toNat = 237 then 159 else 191))
    (hc1 : 128 ≤ c.toNat) (hc2 : c.toNat ≤ 191) : NearSpecV3.utf8Ok (a :: b :: c :: l) = NearSpecV3.utf8Ok l := by
  conv => lhs; unfold NearSpecV3.utf8Ok
  simp only [show ¬ a.toNat < 128 by omega, ite_false, show ¬ (a.toNat ≤ 223) by omega, decide_false,
    Bool.and_false, Bool.false_eq_true, h1, h2, decide_true, Bool.and_self, ite_true, hc1, hc2,
    Bool.true_and, beq_iff_eq]
  simp only [hb1, hb2, decide_true, Bool.true_and]
theorem utf8_4 (a b c d : UInt8) (l : List UInt8) (h1 : 240 ≤ a.toNat) (h2 : a.toNat ≤ 244)
    (hb1 : (if a.toNat = 240 then 144 else 128) ≤ b.toNat) (hb2 : b.toNat ≤ (if a.toNat = 244 then 143 else 191))
    (hc1 : 128 ≤ c.toNat) (hc2 : c.toNat ≤ 191) (hd1 : 128 ≤ d.toNat) (hd2 : d.toNat ≤ 191) :
    NearSpecV3.utf8Ok (a :: b :: c :: d :: l) = NearSpecV3.utf8Ok l := by
  conv => lhs; unfold NearSpecV3.utf8Ok
  simp only [show ¬ a.toNat < 128 by omega, ite_false, show ¬ (a.toNat ≤ 223) by omega,
    show ¬ (a.toNat ≤ 239) by omega, decide_false,
    Bool.and_false, Bool.false_eq_true, h1, h2, decide_true, Bool.and_self, ite_true, hc1, hc2, hd1, hd2,
    Bool.true_and, beq_iff_eq]
  simp only [hb1, hb2, decide_true, Bool.true_and]

theorem u8 {y : Nat} (h : y < 256) : (UInt8.ofNat y).toNat = y := by simp; omega

theorem ucn_k1 (v : Fp) : ucnF 1 v = v - 1 := by simp [ucnF]

section
variable {R : Nat} {x k : Nat → Nat} {u : Nat → Fp} {e0 ed f0 f4 : Nat → Bool}
  (H : U8Rows R x k u e0 ed f0 f4)
include H

theorem cls_le (j : Nat) (hj : j < R) : k j ≤ 4 := by
  rcases H.cls j hj with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega

/-- A row with a "negative" pending count cannot reach the end. -/
theorem neg_dead (hR : R < P) : ∀ m j, j + m = R - 1 → j < R → ∀ c, 0 < c → c + m + 1 < P →
    u j = -((c : Nat) : Fp) → False := by
  intro m
  induction m with
  | zero =>
    intro j hj hjR c hc hcP hu
    have hj' : j = R - 1 := by omega
    have hs := H.stop (by omega); rw [← hj'] at hs
    have hk1 : k j = 1 := Classical.byContradiction fun hne => by
      have := H.lead j hjR hne; rw [hu] at this
      exact fp_ofNat_ne_zero hc (by omega) (by grind)
    simp only [ucnF, hk1, show ¬ (1 = 2) by omega, show ¬ (1 = 3) by omega, show ¬ (1 = 4) by omega,
      ite_false, ite_true, hu] at hs
    have : (((c + 1 : Nat)) : Fp) = 0 := by
      rw [show ((c + 1 : Nat) : Fp) = ((c : Nat) : Fp) + 1 by
        rw [show ((c + 1 : Nat) : Fp) = Fp.ofNat (c + 1) from rfl, show ((c : Nat) : Fp) = Fp.ofNat c from rfl,
          show (1 : Fp) = Fp.ofNat 1 from rfl]
        apply Fp.ext; simp [Fp.add_def]]
      grind
    exact fp_ofNat_ne_zero (by omega) (by omega) this
  | succ m ih =>
    intro j hj hjR c hc hcP hu
    have hk1 : k j = 1 := Classical.byContradiction fun hne => by
      have := H.lead j hjR hne; rw [hu] at this
      exact fp_ofNat_ne_zero hc (by omega) (by grind)
    have hs := H.step j (by omega)
    simp only [ucnF, hk1, show ¬ (1 = 2) by omega, show ¬ (1 = 3) by omega, show ¬ (1 = 4) by omega,
      ite_false, ite_true, hu] at hs
    refine ih (j + 1) (by omega) (by omega) (c + 1) (by omega) (by omega) ?_
    rw [hs, show ((c + 1 : Nat) : Fp) = Fp.ofNat (c + 1) from rfl,
      show ((c : Nat) : Fp) = Fp.ofNat c from rfl]
    have : Fp.ofNat (c + 1) = Fp.ofNat c + 1 := by
      rw [show (1 : Fp) = Fp.ofNat 1 from rfl]; apply Fp.ext; simp [Fp.add_def]
    rw [this]; grind

/-- **The automaton accepts only well-formed UTF-8.** -/
theorem utf8_rows (hR : R < P) : ∀ m j, j + m = R → (m = 0 ∨ u j = 0) →
    NearSpecV3.utf8Ok ((List.range' j m).map fun i => UInt8.ofNat (x i)) = true := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro j hjm h0
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp [NearSpecV3.utf8Ok]
  have hu0 : u j = 0 := h0.resolve_left (by omega)
  have hjR : j < R := by omega
  have hb : x j < 256 := by rcases H.cls j hjR with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> omega
  -- the next pending counts
  have nxt1 : ∀ i, i < R → i + 1 < R ∨ i + 1 = R := fun i hi => by omega
  have notC : ∀ i, i < R → u i ≠ 0 → k i = 1 := fun i hi hne =>
    Classical.byContradiction fun h => hne (H.lead i hi h)
  have contB : ∀ i, i < R → k i = 1 → 0x80 ≤ x i ∧ x i ≤ 0xBF := fun i hi hk => by
    rcases H.cls i hi with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> first | omega | exact h
  have one_ne : (1 : Fp) ≠ 0 := fp_one_ne_zero'
  rw [show m = (m - 1) + 1 by omega, List.range'_succ, List.map_cons]
  rcases H.cls j hjR with ⟨hk, hx⟩ | ⟨hk, hx1, hx2⟩ | ⟨hk, hx1, hx2⟩ | ⟨hk, hx1, hx2⟩ | ⟨hk, hx1, hx2⟩
  · -- ASCII
    rw [utf8_a _ _ (by rw [u8 hb]; omega)]
    refine ih (m - 1) (by omega) (j + 1) (by omega) ?_
    rcases Nat.eq_zero_or_pos (m - 1) with h | h
    · exact Or.inl h
    · right; rw [H.step j (by omega), hk]; simp [ucnF]
  · -- a stray continuation byte: impossible
    exfalso
    rcases nxt1 j hjR with h | h
    · have hs := H.step j h; rw [hk, ucn_k1, hu0] at hs
      exact neg_dead H hR (R - 1 - (j + 1)) (j + 1) (by omega) h 1 (by omega) (by omega)
        (by rw [hs]; rfl)
    · have hs := H.stop (by omega); rw [show R - 1 = j by omega, hk, ucn_k1, hu0] at hs
      exact one_ne (by grind)
  · -- 2-byte sequence
    have hj1 : j + 1 < R := by
      rcases nxt1 j hjR with h | h
      · exact h
      · exfalso; have hs := H.stop (by omega); rw [show R - 1 = j by omega, hk] at hs
        simp [ucnF] at hs; exact one_ne hs
    have hu1 : u (j + 1) = 1 := by rw [H.step j hj1, hk]; simp [ucnF]
    have hk1 := notC (j + 1) hj1 (by rw [hu1]; exact one_ne)
    have hc1 := contB (j + 1) hj1 hk1
    rw [show m - 1 = (m - 2) + 1 by omega, List.range'_succ, List.map_cons,
      utf8_2 _ _ _ (by rw [u8 hb]; omega) (by rw [u8 hb]; omega) (by rw [u8 (by omega)]; omega)
        (by rw [u8 (by omega)]; omega)]
    refine ih (m - 2) (by omega) (j + 1 + 1) (by omega) ?_
    rcases Nat.eq_zero_or_pos (m - 2) with h | h
    · exact Or.inl h
    · right; rw [H.step (j + 1) (by omega), hk1, ucn_k1, hu1]; grind
  · -- 3-byte sequence
    have two_ne : (2 : Fp) ≠ 0 := by decide
    have hj1 : j + 1 < R := by
      rcases nxt1 j hjR with h | h
      · exact h
      · exfalso; have hs := H.stop (by omega); rw [show R - 1 = j by omega, hk] at hs
        simp [ucnF] at hs; exact two_ne hs
    have hu1 : u (j + 1) = 2 := by rw [H.step j hj1, hk]; simp [ucnF]
    have hk1 := notC (j + 1) hj1 (by rw [hu1]; exact two_ne)
    have hj2 : j + 2 < R := by
      rcases nxt1 (j + 1) hj1 with h | h
      · exact h
      · exfalso; have hs := H.stop (by omega); rw [show R - 1 = j + 1 by omega, hk1, ucn_k1, hu1] at hs
        exact one_ne (by grind)
    have hu2 : u (j + 2) = 1 := by rw [H.step (j + 1) hj2, hk1, ucn_k1, hu1]; grind
    have hk2 := notC (j + 2) hj2 (by rw [hu2]; exact one_ne)
    have hc1 := contB (j + 1) hj1 hk1
    have hc2 := contB (j + 2) hj2 hk2
    have hc2' : 128 ≤ x (j + 1 + 1) ∧ x (j + 1 + 1) ≤ 191 := hc2
    have lo : (if x j = 224 then 160 else 128) ≤ x (j + 1) := by
      split
      · exact H.fE0 j hj1 hk (by omega) hk1
      · omega
    have hi : x (j + 1) ≤ (if x j = 237 then 159 else 191) := by
      split
      · exact H.fED j hj1 hk (by omega) hk1
      · omega
    rw [show m - 1 = ((m - 3) + 1) + 1 by omega, List.range'_succ, List.range'_succ, List.map_cons,
      List.map_cons,
      utf8_3 _ _ _ _ (by rw [u8 hb]; omega) (by rw [u8 hb]; omega) (by rw [u8 hb, u8 (by omega)]; exact lo)
        (by rw [u8 hb, u8 (by omega)]; exact hi) (by rw [u8 (by omega)]; omega) (by rw [u8 (by omega)]; omega)]
    refine ih (m - 3) (by omega) (j + 1 + 1 + 1) (by omega) ?_
    rcases Nat.eq_zero_or_pos (m - 3) with h | h
    · exact Or.inl h
    · right; rw [H.step (j + 2) (by omega), hk2, ucn_k1, hu2]; grind
  · -- 4-byte sequence
    have three_ne : (3 : Fp) ≠ 0 := by decide
    have two_ne : (2 : Fp) ≠ 0 := by decide
    have hj1 : j + 1 < R := by
      rcases nxt1 j hjR with h | h
      · exact h
      · exfalso; have hs := H.stop (by omega); rw [show R - 1 = j by omega, hk] at hs
        simp [ucnF] at hs; exact three_ne hs
    have hu1 : u (j + 1) = 3 := by rw [H.step j hj1, hk]; simp [ucnF]
    have hk1 := notC (j + 1) hj1 (by rw [hu1]; exact three_ne)
    have hj2 : j + 2 < R := by
      rcases nxt1 (j + 1) hj1 with h | h
      · exact h
      · exfalso; have hs := H.stop (by omega); rw [show R - 1 = j + 1 by omega, hk1, ucn_k1, hu1] at hs
        exact two_ne (by grind)
    have hu2 : u (j + 2) = 2 := by rw [H.step (j + 1) hj2, hk1, ucn_k1, hu1]; grind
    have hk2 := notC (j + 2) hj2 (by rw [hu2]; exact two_ne)
    have hj3 : j + 3 < R := by
      rcases nxt1 (j + 2) hj2 with h | h
      · exact h
      · exfalso; have hs := H.stop (by omega); rw [show R - 1 = j + 2 by omega, hk2, ucn_k1, hu2] at hs
        exact one_ne (by grind)
    have hu3 : u (j + 3) = 1 := by rw [H.step (j + 2) hj3, hk2, ucn_k1, hu2]; grind
    have hk3 := notC (j + 3) hj3 (by rw [hu3]; exact one_ne)
    have hc1 := contB (j + 1) hj1 hk1
    have hc2 := contB (j + 2) hj2 hk2
    have hc3 := contB (j + 3) hj3 hk3
    have hc2' : 128 ≤ x (j + 1 + 1) ∧ x (j + 1 + 1) ≤ 191 := hc2
    have hc3' : 128 ≤ x (j + 1 + 1 + 1) ∧ x (j + 1 + 1 + 1) ≤ 191 := hc3
    have lo : (if x j = 240 then 144 else 128) ≤ x (j + 1) := by
      split
      · exact H.fF0 j hj1 hk (by omega) hk1
      · omega
    have hi : x (j + 1) ≤ (if x j = 244 then 143 else 191) := by
      split
      · exact H.fF4 j hj1 hk (by omega) hk1
      · omega
    rw [show m - 1 = (((m - 4) + 1) + 1) + 1 by omega, List.range'_succ, List.range'_succ,
      List.range'_succ, List.map_cons, List.map_cons, List.map_cons,
      utf8_4 _ _ _ _ _ (by rw [u8 hb]; omega) (by rw [u8 hb]; omega) (by rw [u8 hb, u8 (by omega)]; exact lo)
        (by rw [u8 hb, u8 (by omega)]; exact hi) (by rw [u8 (by omega)]; omega) (by rw [u8 (by omega)]; omega)
        (by rw [u8 (by omega)]; omega) (by rw [u8 (by omega)]; omega)]
    refine ih (m - 4) (by omega) (j + 1 + 1 + 1 + 1) (by omega) ?_
    rcases Nat.eq_zero_or_pos (m - 4) with h | h
    · exact Or.inl h
    · right; rw [H.step (j + 3) (by omega), hk3, ucn_k1, hu3]; grind

end

end ZkFormal.NearV3.D1.AkmProof
