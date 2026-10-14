import ZkFormal.NearV3.D1.Extract.Akm.Row

/-!
# `ZkFormal.NearV3.D1.Extract.Akm.Field` — a field of a value segment

A fixed field of state `x` and length `L + 1` starting at offset `p` (`ix = 0`) occupies offsets
`p … p+L` (state `x`, `ix = j`, same `mth`), ends there (`fe`), and does not end the segment
before.  A string body (`sS`, `rem = R`) occupies `R` offsets likewise.
-/

namespace ZkFormal.NearV3.D1.AkmProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.AkmV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- The fixed-field table: state and `len − 1`. -/
def FixedLen (x L : Nat) : Prop :=
  (x = sN ∧ L = 7) ∨ (x = sT ∧ L = 0) ∨ (x = sG ∧ L = 17) ∨ (x = sO ∧ L = 0) ∨
    (x = sA ∧ L = 15) ∨ (x = sL ∧ L = 3) ∨ (x = sC ∧ L = 3)

theorem FixedLen.mem {x L : Nat} (h : FixedLen x L) : x ∈ states ∧ x ≠ sS ∧ L ≤ 17 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨by simp [states], by decide, by omega⟩

section
variable (hL : TableLocal AkmV3.table tr tt pub)
include hL

theorem eval_bitsNA {r : Nat} (hr : r + 1 < tr.height tt) :
    (bits (fun x => n (bb x)) 0 8).eval tr tt r pub = (bits (fun x => c (bb x)) 0 8).eval tr tt (r + 1) pub := by
  have gen : ∀ len, (bits (fun x => n (bb x)) 0 len).eval tr tt r pub =
      (bits (fun x => c (bb x)) 0 len).eval tr tt (r + 1) pub := by
    intro len
    induction len with
    | zero => rfl
    | succ len ih =>
      rw [bits_succ, bits_succ, eval_sum_append, eval_sum_append,
        show sum ((List.range len).map fun b => smul (2 ^ b) ((fun x => n (bb x)) (0 + b))) =
          bits (fun x => n (bb x)) 0 len from rfl,
        show sum ((List.range len).map fun b => smul (2 ^ b) ((fun x => c (bb x)) (0 + b))) =
          bits (fun x => c (bb x)) 0 len from rfl, ih]
      simp only [eval_sum_cons, eval_sum_nil, eval_smul, eval_n, eval_c, nxt hr]
  exact gen 8

theorem seg_next {s ℓ : Nat} (seg : SegAt tr tt s ℓ) {p : Nat} (hp : p < ℓ)
    (hal : tr.cell tt (s + p) al = 0) : p + 1 < ℓ := by
  have := seg.al p hp
  rw [hal] at this
  by_cases h : p + 1 = ℓ
  · rw [if_pos h] at this; exact absurd this.symm fp_one_ne_zero
  · omega

/-- **A fixed field.** -/
theorem field {s ℓ : Nat} (seg : SegAt tr tt s ℓ) {x L : Nat} (hxL : FixedLen x L) {p : Nat}
    (hp : p < ℓ) (hX : tr.cell tt (s + p) x = 1) (hix : tr.cell tt (s + p) ix = 0) :
    ∀ j, j ≤ L → p + j < ℓ ∧ tr.cell tt (s + p + j) x = 1 ∧
      tr.cell tt (s + p + j) ix = ((j : Nat) : Fp) ∧
      tr.cell tt (s + p + j) mth = tr.cell tt (s + p) mth ∧
      (j < L → tr.cell tt (s + p + j) fe = 0 ∧ tr.cell tt (s + p + j) al = 0) ∧
      (j = L → tr.cell tt (s + p + j) fe = 1) := by
  obtain ⟨hmem, hS, hL17⟩ := hxL.mem
  have hH := seg.h
  have key : ∀ j, j ≤ L → p + j < ℓ → tr.cell tt (s + p + j) x = 1 →
      tr.cell tt (s + p + j) ix = ((j : Nat) : Fp) →
      (j < L → tr.cell tt (s + p + j) fe = 0 ∧ tr.cell tt (s + p + j) al = 0) ∧
      (j = L → tr.cell tt (s + p + j) fe = 1) := by
    intro j hj hpj hx hi
    have ha := seg.act (p + j) hpj; rw [← Nat.add_assoc] at ha
    have hr : s + p + j < tr.height tt := by omega
    have hle := lastE_fixed hL hr ha hmem hx hS hxL
    rw [hi] at hle
    obtain ⟨hb, hiff⟩ := fe_iff hL hr ha
    refine ⟨fun hlt => ?_, fun he => hiff.mpr (by rw [hle, he]; grind)⟩
    have hf0 : tr.cell tt (s + p + j) fe = 0 := by
      rcases hb with hb | hb
      · exact hb
      · exfalso
        have h0 := hiff.mp hb; rw [hle] at h0
        have : ((j : Nat) : Fp) = ((L : Nat) : Fp) := by grind
        have := ofNat_inj (by unfold P; omega) (by unfold P; omega) this
        omega
    have hal := (Row_al_zero hL hr ha hf0)
    exact ⟨hf0, hal⟩
  intro j
  induction j with
  | zero =>
    intro _
    have hix0 : tr.cell tt (s + p + 0) ix = ((0 : Nat) : Fp) := by rw [Nat.add_zero, hix]; rfl
    have h0 := key 0 (by omega) (by omega) (by simpa using hX) hix0
    exact ⟨by omega, by simpa using hX, hix0, by simp, h0.1, h0.2⟩
  | succ j ih =>
    intro hj
    obtain ⟨hpj, hx, hi, hm, hf, -⟩ := ih (by omega)
    obtain ⟨hfe, hal⟩ := hf (by omega)
    have hpj1 := seg_next hL seg hpj (by rw [← Nat.add_assoc]; exact hal)
    have hr : s + p + j + 1 < tr.height tt := by omega
    have ha := seg.act (p + j) hpj; rw [← Nat.add_assoc] at ha
    obtain ⟨-, hix1, hm1, hst, -⟩ := inside hL hr ha hfe
    have hx1 : tr.cell tt (s + p + (j + 1)) x = 1 := by rw [← Nat.add_assoc, hst x hmem, hx]
    have hi1 : tr.cell tt (s + p + (j + 1)) ix = (((j + 1 : Nat)) : Fp) := by
      rw [← Nat.add_assoc, hix1, hi, natCast_add]; rfl
    have hk := key (j + 1) hj (by omega) hx1 hi1
    exact ⟨by omega, hx1, hi1, by rw [← Nat.add_assoc, hm1, hm], hk.1, hk.2⟩

/-- **A string body** of `R ≥ 1` bytes. -/
theorem body {s ℓ : Nat} (seg : SegAt tr tt s ℓ) {p R : Nat} (hp : p < ℓ)
    (hX : tr.cell tt (s + p) sS = 1) (hrem : tr.cell tt (s + p) rem = ((R : Nat) : Fp))
    (hR : 1 ≤ R) (hRP : R < P) :
    ∀ j, j < R → p + j < ℓ ∧ tr.cell tt (s + p + j) sS = 1 ∧
      tr.cell tt (s + p + j) rem = (((R - j : Nat)) : Fp) ∧
      tr.cell tt (s + p + j) mth = tr.cell tt (s + p) mth ∧
      (j + 1 < R → tr.cell tt (s + p + j) fe = 0 ∧ tr.cell tt (s + p + j) al = 0) ∧
      (j + 1 = R → tr.cell tt (s + p + j) fe = 1) := by
  have hH := seg.h
  have key : ∀ j, j < R → p + j < ℓ → tr.cell tt (s + p + j) sS = 1 →
      tr.cell tt (s + p + j) rem = (((R - j : Nat)) : Fp) →
      (j + 1 < R → tr.cell tt (s + p + j) fe = 0 ∧ tr.cell tt (s + p + j) al = 0) ∧
      (j + 1 = R → tr.cell tt (s + p + j) fe = 1) := by
    intro j hj hpj hx hi
    have ha := seg.act (p + j) hpj; rw [← Nat.add_assoc] at ha
    have hr : s + p + j < tr.height tt := by omega
    have hle := lastE_S hL hr ha hx
    rw [hi] at hle
    obtain ⟨hb, hiff⟩ := fe_iff hL hr ha
    refine ⟨fun hlt => ?_, fun he => hiff.mpr (by rw [hle, show R - j = 1 by omega]; grind)⟩
    have hf0 : tr.cell tt (s + p + j) fe = 0 := by
      rcases hb with hb | hb
      · exact hb
      · exfalso
        have h0 := hiff.mp hb; rw [hle] at h0
        have : (((R - j : Nat)) : Fp) = ((1 : Nat) : Fp) := by grind
        have := ofNat_inj (by omega) (by unfold P; omega) this
        omega
    exact ⟨hf0, Row_al_zero hL hr ha hf0⟩
  intro j
  induction j with
  | zero =>
    intro hj
    have hi0 : tr.cell tt (s + p + 0) rem = (((R - 0 : Nat)) : Fp) := by rw [Nat.add_zero, hrem, Nat.sub_zero]
    have h0 := key 0 hj (by omega) (by simpa using hX) hi0
    exact ⟨by omega, by simpa using hX, hi0, by simp, h0.1, h0.2⟩
  | succ j ih =>
    intro hj
    obtain ⟨hpj, hx, hi, hm, hf, -⟩ := ih (by omega)
    obtain ⟨hfe, hal⟩ := hf (by omega)
    have hpj1 := seg_next hL seg hpj (by rw [← Nat.add_assoc]; exact hal)
    have hr : s + p + j + 1 < tr.height tt := by omega
    have ha := seg.act (p + j) hpj; rw [← Nat.add_assoc] at ha
    obtain ⟨-, -, hm1, hst, hrm⟩ := inside hL hr ha hfe
    have hx1 : tr.cell tt (s + p + (j + 1)) sS = 1 := by
      rw [← Nat.add_assoc, hst sS (by simp [states]), hx]
    have hi1 : tr.cell tt (s + p + (j + 1)) rem = (((R - (j + 1) : Nat)) : Fp) := by
      rw [← Nat.add_assoc, hrm hx, hi, show R - j = (R - (j + 1)) + 1 by omega, natCast_add]
      grind
    have hk := key (j + 1) hj (by omega) hx1 hi1
    exact ⟨by omega, hx1, hi1, by rw [← Nat.add_assoc, hm1, hm], hk.1, hk.2⟩

theorem u32S_one {r : Nat} (hr : r < tr.height tt) (ha : tr.cell tt r act = 1) {x : Nat}
    (hx : x = sL ∨ x = sC) (h1 : tr.cell tt r x = 1) : u32S.eval tr tt r pub = 1 := by
  have z := oneHot hL hr ha (by rcases hx with rfl | rfl <;> simp [states]) h1
  simp only [u32S, eval_add, eval_c]
  rcases hx with rfl | rfl
  · rw [h1, z sC (by simp [states]) (by decide)]; grind
  · rw [h1, z sL (by simp [states]) (by decide)]; grind

/-- **A `u32` field** (`sL` length or `sC` count) after a field end: its value has high byte `0`,
`acc` on the last byte holds it, and `zA` tests it for `0`. -/
theorem u32field {s ℓ : Nat} (seg : SegAt tr tt s ℓ) {x : Nat} (hx : x = sL ∨ x = sC) {p : Nat}
    (hp : p < ℓ) (hp1 : 1 ≤ p) (hX : tr.cell tt (s + p) x = 1) (hix : tr.cell tt (s + p) ix = 0)
    (hgo : tr.cell tt (s + p - 1) fgo = 1) :
    p + 3 < ℓ ∧ tr.cell tt (s + p + 3) fe = 1 ∧ bvA tr tt (s + p + 3) = 0 ∧
    tr.cell tt (s + p + 3) acc =
      (((bvA tr tt (s + p) + 256 * bvA tr tt (s + p + 1) + 65536 * bvA tr tt (s + p + 2) : Nat)) : Fp) ∧
    (tr.cell tt (s + p + 3) zA = 0 ∨ tr.cell tt (s + p + 3) zA = 1) ∧
    (tr.cell tt (s + p + 3) zA = 1 ↔
      bvA tr tt (s + p) + 256 * bvA tr tt (s + p + 1) + 65536 * bvA tr tt (s + p + 2) = 0) := by
  have hH := seg.h
  have hxL : FixedLen x 3 := by rcases hx with rfl | rfl <;> simp [FixedLen]
  have F := field hL seg hxL hp hX hix
  obtain ⟨hp3, hx3, -, -, -, hfe3⟩ := F 3 (by omega)
  have hfe3 := hfe3 rfl
  have u := fun j (hj : j ≤ 3) => u32S_one hL (r := s + p + j) (by have := (F j hj).1; omega)
    (by have := seg.act (p + j) (F j hj).1; rwa [← Nat.add_assoc] at this) hx (F j hj).2.1
  have bl := fun j (hj : j ≤ 3) => bvA_lt hL (r := s + p + j) (by have := (F j hj).1; omega)
  -- the start: `pw = 1`, `acc = b₀`
  have hr0 : s + p - 1 + 1 < tr.height tt := by omega
  have e1 := con hL (r := s + p - 1) (by omega) (mem_fields (e := mul3 (c fgo) u32SN (sub (n pw) (k 1)))
    (by simp [cFields]))
  have e2 := con hL (r := s + p - 1) (by omega) (mem_fields (e := mul3 (c fgo) u32SN (sub (n acc) bN))
    (by simp [cFields]))
  have hu0 := u 0 (by omega); simp only [Nat.add_zero] at hu0
  have hn : u32SN.eval tr tt (s + p - 1) pub = u32S.eval tr tt (s + p) pub := by
    simp only [u32SN, u32S, eval_add, eval_n, eval_c, nxt hr0, show s + p - 1 + 1 = s + p by omega,
      Nat.mod_eq_of_lt (show s + p < tr.height tt by omega)]
  have hbN : bN.eval tr tt (s + p - 1) pub = ((bvA tr tt (s + p) : Nat) : Fp) := by
    rw [← eval_bE hL (r := s + p) (by omega)]
    simp only [bN, bE]; rw [show s + p = s + p - 1 + 1 by omega]
    exact eval_bitsNA hL hr0
  simp only [eval_mul3, eval_sub, eval_c, eval_n, eval_k, hgo, hn, hu0, hbN, nxt hr0,
    show s + p - 1 + 1 = s + p by omega, Nat.mod_eq_of_lt (show s + p < tr.height tt by omega)] at e1 e2
  have pw0 : tr.cell tt (s + p) pw = 1 := by grind
  have ac0 : tr.cell tt (s + p) acc = ((bvA tr tt (s + p) : Nat) : Fp) := by grind
  -- the steps
  have step : ∀ j, j < 3 → tr.cell tt (s + p + (j + 1)) pw = ((256 : Nat) : Fp) * tr.cell tt (s + p + j) pw ∧
      tr.cell tt (s + p + (j + 1)) acc = tr.cell tt (s + p + j) acc +
        tr.cell tt (s + p + (j + 1)) pw * ((bvA tr tt (s + p + (j + 1)) : Nat) : Fp) := by
    intro j hj
    have hpj := (F j (by omega)).1
    have hr : s + p + j + 1 < tr.height tt := by omega
    have hfe := ((F j (by omega)).2.2.2.2.1 hj).1
    have f1 := con hL (r := s + p + j) (by omega) (mem_fields (e := mul3 u32S (not (c fe)) (sub (n pw) (smul 256 (c pw))))
      (by simp [cFields]))
    have f2 := con hL (r := s + p + j) (by omega) (mem_fields (e := mul3 u32S (not (c fe))
      (sub (n acc) (.add (c acc) (.mul (n pw) bN)))) (by simp [cFields]))
    have hbN' : bN.eval tr tt (s + p + j) pub = ((bvA tr tt (s + p + (j + 1)) : Nat) : Fp) := by
      rw [← eval_bE hL (r := s + p + (j + 1)) (by omega)]
      simp only [bN, bE]; rw [← Nat.add_assoc]; exact eval_bitsNA hL hr
    simp only [eval_mul3, eval_sub, eval_add, eval_mul, eval_c, eval_n, eval_smul, eval_not, hfe,
      u j (by omega), hbN', nxt hr] at f1 f2
    rw [← Nat.add_assoc]
    exact ⟨by grind, by grind⟩
  obtain ⟨p1, a1⟩ := step 0 (by omega); obtain ⟨p2, a2⟩ := step 1 (by omega)
  obtain ⟨p3, a3⟩ := step 2 (by omega)
  simp only [Nat.zero_add, Nat.add_zero] at p1 a1 p2 a2 p3 a3
  rw [pw0] at p1; rw [p1] at p2 a1; rw [p2] at p3 a2; rw [p3] at a3
  rw [ac0] at a1; rw [a1] at a2; rw [a2] at a3
  -- the end: high byte `0`, `zA`
  have hr3 : s + p + 3 < tr.height tt := by omega
  have ha3 := seg.act (p + 3) hp3; rw [← Nat.add_assoc] at ha3
  have g1 := con hL hr3 (mem_fields (e := mul3 u32S (c fe) bE) (by simp [cFields]))
  have g2 := con hL hr3 (mem_fields (e := mul3 u32S (c fe) (.mul (c acc) (c zA))) (by simp [cFields]))
  have g3 := con hL hr3 (mem_fields (e := mul3 u32S (c fe) (sub (.mul (c acc) (c invA)) (not (c zA))))
    (by simp [cFields]))
  simp only [eval_mul3, eval_mul, eval_sub, eval_c, eval_not, u 3 (by omega), hfe3, eval_bE hL hr3] at g1 g2 g3
  have hb3 : bvA tr tt (s + p + 3) = 0 :=
    ofNat_inj (by have := bl 3 (by omega); unfold P; omega) (by unfold P; omega) (by grind)
  have b0 := bl 0 (by omega); have b1 := bl 1 (by omega); have b2 := bl 2 (by omega)
  simp only [Nat.add_zero] at b0
  have hacc : tr.cell tt (s + p + 3) acc =
      (((bvA tr tt (s + p) + 256 * bvA tr tt (s + p + 1) + 65536 * bvA tr tt (s + p + 2) : Nat)) : Fp) := by
    rw [a3, hb3]; simp only [natCast_add, natCast_mul]; grind
  have hzb := isBool hL hr3 (x := zA) (by simp [boolCols])
  refine ⟨hp3, hfe3, hb3, hacc, hzb, fun h => ?_, fun h => ?_⟩
  · rw [h, hacc] at g2
    exact ofNat_inj (by unfold P; omega) (by unfold P; omega) (by grind)
  · rw [hacc, h] at g3
    rcases hzb with hz | hz
    · rw [hz] at g3; exact absurd (by grind) fp_zero_ne_one
    · exact hz

end

end ZkFormal.NearV3.D1.AkmProof
