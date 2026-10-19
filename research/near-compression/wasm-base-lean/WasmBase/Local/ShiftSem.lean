import NearSpecV3.Wasm.Numerics
/-!
# Shift/rotate semantics from the product `P = A · 2^e mod 2^(2w)`

The SHIFT chip computes `lo + 2^w · hi = (A · 2^e) mod 2^(2w)` (byte limbs with carries).  These
lemmas show that the selected halves are exactly the spec's `shl`, `shr_u`, `shr_s`, `rotl`, `rotr`.
-/
namespace WasmBase.Local
open NearSpecV3.Wasm

theorem two_pow_pos' (n : Nat) : 0 < 2 ^ n := Nat.two_pow_pos n

theorem pow_split {w k : Nat} (hk : k ≤ w) : 2 ^ w = 2 ^ k * 2 ^ (w - k) := by
  rw [← Nat.pow_add]; congr 1; omega

theorem pow_two_w (w : Nat) : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by
  rw [← Nat.pow_add]; congr 1; omega

theorem lo_of (w x lo hi : Nat) (hlo : lo < 2 ^ w) (h : lo + 2 ^ w * hi = x % 2 ^ (2 * w)) :
    lo = x % 2 ^ w := by
  have hd : 2 ^ w ∣ 2 ^ (2 * w) := Nat.pow_dvd_pow 2 (by omega)
  have := congrArg (· % 2 ^ w) h
  rw [Nat.mod_mod_of_dvd _ hd, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo] at this
  exact this

theorem hi_of (w x lo hi : Nat) (hlo : lo < 2 ^ w) (hx : x < 2 ^ (2 * w))
    (h : lo + 2 ^ w * hi = x % 2 ^ (2 * w)) : hi = x / 2 ^ w := by
  rw [Nat.mod_eq_of_lt hx] at h
  rw [← h, Nat.add_mul_div_left _ _ (two_pow_pos' w), Nat.div_eq_of_lt hlo, Nat.zero_add]

theorem mul_pow_lt {w a k : Nat} (hk : k ≤ w) (ha : a < 2 ^ w) : a * 2 ^ k < 2 ^ (2 * w) := by
  rw [pow_two_w]
  exact Nat.mul_lt_mul_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hk) (two_pow_pos' w)

/-- `a · 2^k / 2^w = a / 2^(w-k)`. -/
theorem mul_pow_div {w a k : Nat} (hk : k ≤ w) : a * 2 ^ k / 2 ^ w = a / 2 ^ (w - k) := by
  rw [pow_split hk, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (two_pow_pos' k)]

theorem sem_shl (w a k lo hi : Nat) (hk : k < w) (hlo : lo < 2 ^ w)
    (h : lo + 2 ^ w * hi = (a * 2 ^ k) % 2 ^ (2 * w)) : lo = Num.shl w a k := by
  rw [lo_of w _ lo hi hlo h]; unfold Num.shl; rw [Nat.mod_eq_of_lt hk]

theorem sem_shru (w a k lo hi : Nat) (hk : k < w) (ha : a < 2 ^ w) (hlo : lo < 2 ^ w)
    (h : lo + 2 ^ w * hi = (a * 2 ^ (w - k)) % 2 ^ (2 * w)) : hi = Num.shrU w a k := by
  rw [hi_of w _ lo hi hlo (mul_pow_lt (by omega) ha) h, mul_pow_div (by omega)]
  unfold Num.shrU; rw [Nat.mod_eq_of_lt hk, show w - (w - k) = k by omega]

theorem sem_rotl (w a k lo hi : Nat) (hk : k < w) (ha : a < 2 ^ w) (hlo : lo < 2 ^ w)
    (h : lo + 2 ^ w * hi = (a * 2 ^ k) % 2 ^ (2 * w)) : lo + hi = Num.rotl w a k := by
  rw [lo_of w _ lo hi hlo h, hi_of w _ lo hi hlo (mul_pow_lt (by omega) ha) h, mul_pow_div (by omega)]
  unfold Num.rotl; rw [Nat.mod_eq_of_lt hk]

theorem sem_rotr (w a k lo hi : Nat) (hw : 0 < w) (hk : k < w) (ha : a < 2 ^ w) (hlo : lo < 2 ^ w)
    (h : lo + 2 ^ w * hi = (a * 2 ^ (w - k)) % 2 ^ (2 * w)) : lo + hi = Num.rotr w a k := by
  rw [lo_of w _ lo hi hlo h, hi_of w _ lo hi hlo (mul_pow_lt (by omega) ha) h, mul_pow_div (by omega)]
  unfold Num.rotr Num.rotl
  rw [Nat.mod_eq_of_lt hk]
  by_cases hk0 : k = 0
  · subst hk0
    simp only [Nat.sub_zero, Nat.mod_self, Nat.zero_mod, Nat.pow_zero, Nat.mul_one, Nat.sub_self, Nat.div_one]
    rw [pow_split (Nat.le_refl w), Nat.sub_self, Nat.pow_zero, Nat.mul_one, Nat.mul_mod_left, Nat.zero_add,
      Nat.div_eq_of_lt ha, Nat.add_zero, Nat.mod_eq_of_lt ha]
  · simp only [Nat.mod_eq_of_lt (show w - k < w by omega), show w - (w - k) = k by omega]

/-- shr_s: high half of the sign-extended `A · 2^(w-k)`. -/
theorem sem_shrs (w a k lo hi sgn rest : Nat) (hk : k < w) (ha : a = 2 ^ (w - 1) * sgn + rest)
    (hs : sgn ≤ 1) (hr : rest < 2 ^ (w - 1)) (hlo : lo < 2 ^ w)
    (h : lo + 2 ^ w * hi = ((a + sgn * (2 ^ (2 * w) - 2 ^ w)) * 2 ^ (w - k)) % 2 ^ (2 * w)) :
    hi = Num.shrS w a k := by
  have hw1 : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have haw : a < 2 ^ w := by rcases (show sgn = 0 ∨ sgn = 1 by omega) with h0 | h0 <;> subst h0 <;> omega
  unfold Num.shrS Num.wrap Num.signed
  rw [Nat.mod_eq_of_lt hk]
  rcases (show sgn = 0 ∨ sgn = 1 by omega) with h0 | h0
  · subst h0
    simp only [Nat.zero_mul, Nat.add_zero] at h
    have e := sem_shru w a k lo hi hk haw hlo h
    unfold Num.shrU at e; rw [Nat.mod_eq_of_lt hk] at e
    rw [if_neg (by omega), e]
    have hlt : a / 2 ^ k < 2 ^ w := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) haw
    have h1 : (a : Int) / (2 : Int) ^ k = ((a / 2 ^ k : Nat) : Int) := by
      rw [Int.natCast_ediv]; push_cast; rfl
    have h2 : ((a / 2 ^ k : Nat) : Int) % (2 : Int) ^ w = ((a / 2 ^ k : Nat) : Int) := by
      rw [show ((2 : Int) ^ w) = ((2 ^ w : Nat) : Int) by push_cast; rfl, ← Int.natCast_emod,
        Nat.mod_eq_of_lt hlt]
    rw [h1, h2, Int.toNat_natCast]
  · subst h0
    rw [if_pos (by omega)]
    -- d = 2^w - a, A' = 2^(2w) - d, m = 2^(w-k), 2^w = 2^k m
    obtain ⟨d, hd⟩ : ∃ d, d = 2 ^ w - a := ⟨_, rfl⟩
    have hd1 : 1 ≤ d := by omega
    have hd2 : d ≤ 2 ^ (w - 1) := by omega
    have hW : 2 ^ w = 2 ^ k * 2 ^ (w - k) := pow_split (by omega)
    have h2W : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := pow_two_w w
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = 2 ^ k := ⟨_, rfl⟩
    obtain ⟨M, hM⟩ : ∃ M, M = 2 ^ (w - k) := ⟨_, rfl⟩
    obtain ⟨W, hWd⟩ : ∃ W, W = 2 ^ w := ⟨_, rfl⟩
    have hQ1 : 1 ≤ Q := by rw [hQ]; exact Nat.one_le_two_pow
    have hM1 : 1 ≤ M := by rw [hM]; exact Nat.one_le_two_pow
    rw [← hQ, ← hM, ← hWd] at hW
    -- the product modulo 2^(2w)
    have hA : (a + 1 * (2 ^ (2 * w) - 2 ^ w)) * 2 ^ (w - k) = W * W * (M - 1) + (W * W - d * M) := by
      rw [← hM, h2W, ← hWd]
      have hdM : d * M ≤ W * M := Nat.mul_le_mul_right _ (by omega)
      have hWM : W * W * M = W * W * (M - 1) + W * W := by
        rw [Nat.mul_sub, Nat.mul_one]; have := Nat.mul_le_mul_left (W * W) hM1; omega
      have e1 : (a + 1 * (W * W - W)) * M = W * W * M - d * M := by
        have : a + 1 * (W * W - W) = W * W - d := by
          have : W ≤ W * W := Nat.le_mul_of_pos_left _ (by omega)
          omega
        rw [this, Nat.sub_mul]
      rw [e1, hWM]
      have : d * M ≤ W * W := by
        have := Nat.mul_le_mul_right M hd2
        have h' : 2 ^ (w - 1) * M ≤ W * W := by
          have : M ≤ W := by rw [hM, hWd]; exact Nat.pow_le_pow_right (by decide) (by omega)
          have := Nat.mul_le_mul (show 2 ^ (w - 1) ≤ W by omega) this
          omega
        omega
      omega
    have hdMpos : 1 ≤ d * M := Nat.mul_le_mul hd1 hM1
    have hP : lo + W * hi = W * W - d * M := by
      have h' := h
      rw [hA, h2W, ← hWd, Nat.mul_add_mod] at h'
      have hWW : 0 < W * W := Nat.mul_pos (by omega) (by omega)
      rw [h', Nat.mod_eq_of_lt (Nat.sub_lt hWW (by omega))]
    -- ceil(d / 2^k)
    obtain ⟨c, hc⟩ : ∃ c, c = (d + Q - 1) / Q := ⟨_, rfl⟩
    have hc1 : d ≤ c * Q := by
      have := Nat.lt_div_mul_add (a := d + Q - 1) (b := Q) (by omega); rw [← hc] at this; omega
    have hc2 : c * Q ≤ d + Q - 1 := by rw [hc]; exact Nat.div_mul_le_self _ _
    have hcpos : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · rw [h0] at hc1; omega
      · exact h0
    have hcW : c ≤ W := by
      refine Classical.byContradiction fun hcon => ?_
      have h1 : (W + 1) * Q ≤ c * Q := Nat.mul_le_mul_right Q (by omega)
      have h2 : W ≤ W * Q := Nat.le_mul_of_pos_right W (by omega)
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
    have hcWQ : c * W = c * Q * M := by rw [hW, Nat.mul_assoc]
    have hdM : d * M ≤ c * Q * M := Nat.mul_le_mul_right _ hc1
    have hdM2 : (c - 1) * Q * M < d * M := by
      apply Nat.mul_lt_mul_of_pos_right _ (by omega)
      rw [Nat.sub_mul, Nat.one_mul]; omega
    have hhi : hi = W - c := by
      have hP' : (W * W - d * M) / W = W - c := by
        apply Nat.div_eq_of_lt_le
        · rw [Nat.sub_mul, hcWQ]; omega
        · rw [show W - c + 1 = W - (c - 1) by omega, Nat.sub_mul, show (c - 1) * W = (c - 1) * Q * M by
            rw [hW, Nat.mul_assoc]]
          have : (c - 1) * Q * M ≤ c * Q * M := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
          have : c * Q * M ≤ W * W := by rw [← hcWQ]; exact Nat.mul_le_mul_right _ hcW
          omega
      rw [← hP', ← hP, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]
    rw [hhi]
    -- spec side: (-d) / 2^k = -c, (-c) % 2^w = 2^w - c
    have hsa : (a : Int) - 2 ^ w = -(d : Int) := by
      have h1 : ((2 : Int) ^ w) = ((2 ^ w : Nat) : Int) := by simp
      have h2 : a ≤ 2 ^ w := by omega
      rw [h1, hd]
      generalize 2 ^ w = X at h2 ⊢
      omega
    rw [hsa]
    have hQi : ((2 : Int) ^ k) = (Q : Int) := by rw [hQ]; simp
    have hWi : ((2 : Int) ^ w) = (W : Int) := by rw [hWd]; simp
    rw [hQi, hWi]
    have hc1' : (d : Int) ≤ (c : Int) * Q := by exact_mod_cast hc1
    have hc2' : (c : Int) * Q ≤ (d : Int) + Q - 1 := by
      have : c * Q + 1 ≤ d + Q := by omega
      have : ((c * Q + 1 : Nat) : Int) ≤ ((d + Q : Nat) : Int) := by exact_mod_cast this
      push_cast at this; omega
    have e1 : -(d : Int) / (Q : Int) = -(c : Int) :=
      ((Int.ediv_emod_unique (r := (c : Int) * Q - d) (by omega)).mpr
        ⟨by rw [Int.mul_neg, Int.mul_comm]; omega, by omega, by omega⟩).1
    have hcW' : (c : Int) ≤ (W : Int) := by exact_mod_cast hcW
    have hc1'' : (1 : Int) ≤ (c : Int) := by exact_mod_cast hcpos
    have e2 : -(c : Int) % (W : Int) = (W : Int) - c :=
      ((Int.ediv_emod_unique (q := -1) (r := (W : Int) - c) (by omega)).mpr
        ⟨by omega, by omega, by omega⟩).2
    rw [e1, e2]
    omega

end WasmBase.Local
