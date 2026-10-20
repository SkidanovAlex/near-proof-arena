import ZkFormal.NearV3.D1.Extract.Akm.Events
import ZkFormal.NearV3.D1.Extract.Akm.Parse

/-!
# `ZkFormal.NearV3.D1.Extract.Akm.Str` — a borsh `String` of an access-key segment

From a length field (`sL`, `ix = 0`, after a field end) the rows hold `u32 n ‖ utf8[n]`:
`pString` reads it, and the last row is the "string done" row (`sd = 1`, `fe = 1`, same `mth`),
with the method counter unchanged until there.
-/

namespace ZkFormal.NearV3.D1.AkmProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.AkmV3 NearSpecV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- The segment bytes as a function of the offset. -/
def segF (tr : Trace Fp) (tt s : Nat) (j : Nat) : UInt8 := UInt8.ofNat (bvA tr tt (s + j))

/-- A field start at offset `q`: state `x`, `ix = 0`, the previous row ended a field. -/
structure FStart (tr : Trace Fp) (tt s ℓ q x : Nat) : Prop where
  lt : q < ℓ
  pos : 1 ≤ q
  st : tr.cell tt (s + q) x = 1
  ix0 : tr.cell tt (s + q) ix = 0
  go : tr.cell tt (s + q - 1) fgo = 1

/-- What a string leaves at its last row `e − 1`. -/
structure StrEnd (tr : Trace Fp) (tt s ℓ q e : Nat) : Prop where
  bound : q + 4 ≤ e ∧ e ≤ ℓ
  sd1 : tr.cell tt (s + (e - 1)) sd = 1
  fe1 : tr.cell tt (s + (e - 1)) fe = 1
  mth : tr.cell tt (s + (e - 1)) mth = tr.cell tt (s + q) mth
  state : tr.cell tt (s + (e - 1)) sL + tr.cell tt (s + (e - 1)) sS = 1 ∧
    tr.cell tt (s + (e - 1)) sT = 0 ∧ tr.cell tt (s + (e - 1)) sG = 0 ∧ tr.cell tt (s + (e - 1)) sC = 0
  vc : tr.cell tt (s + (e - 1)) vc = tr.cell tt (s + q) vc
  noN : ∀ j, q ≤ j → j < e → tr.cell tt (s + j) sN = 0

section
variable (hL : TableLocal AkmV3.table tr tt pub)
include hL

theorem u8b {r : Nat} (hr : r < tr.height tt) : (UInt8.ofNat (bvA tr tt r)).toNat = bvA tr tt r := by
  have := bvA_lt hL hr; simp; omega

/-- On a row in state `sL` or `sS`, the other states are `0`. -/
theorem other0 {r : Nat} (hr : r < tr.height tt) (ha : tr.cell tt r act = 1) {x : Nat} (hx : x = sL ∨ x = sS)
    (h1 : tr.cell tt r x = 1) :
    tr.cell tt r sL + tr.cell tt r sS = 1 ∧ tr.cell tt r sT = 0 ∧ tr.cell tt r sG = 0 ∧ tr.cell tt r sC = 0 := by
  have z := oneHot hL hr ha (by rcases hx with rfl | rfl <;> simp [states]) h1
  rcases hx with rfl | rfl
  · rw [h1, z sS (by simp [states]) (by decide)]
    exact ⟨by grind, z sT (by simp [states]) (by decide), z sG (by simp [states]) (by decide),
      z sC (by simp [states]) (by decide)⟩
  · rw [h1, z sL (by simp [states]) (by decide)]
    exact ⟨by grind, z sT (by simp [states]) (by decide), z sG (by simp [states]) (by decide),
      z sC (by simp [states]) (by decide)⟩

theorem notN {r : Nat} (hr : r < tr.height tt) (ha : tr.cell tt r act = 1) {x : Nat} (hx : x ∈ states)
    (hne : x ≠ sN) (h1 : tr.cell tt r x = 1) : tr.cell tt r sN = 0 :=
  oneHot hL hr ha hx h1 sN (by simp [states]) (Ne.symm hne)

/-- `vc` is unchanged over a row that is neither a method end nor a count start. -/
theorem vc_keep {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 1) (hl : tr.cell tt r al = 0)
    (hsd : tr.cell tt r sd = 0) (hC : tr.cell tt r sC = 0) : tr.cell tt (r + 1) vc = tr.cell tt r vc := by
  rw [vc_step hL hr ha hl, md_eq hL (by omega), eC_eq hL (by omega), hsd, hC]; grind

/-- The `eS` row's settings of the next row. -/
theorem eS_next {r : Nat} (hr : r + 1 < tr.height tt) (he : tr.cell tt r eS = 1) :
    tr.cell tt (r + 1) sS = 1 ∧ tr.cell tt (r + 1) rem = tr.cell tt r acc ∧
    tr.cell tt (r + 1) mth = tr.cell tt r mth ∧ tr.cell tt (r + 1) uc = 0 := by
  have e1 := ev hL (by omega : r < _) (e := .mul (c eS) (not (n sS))) (by simp [cEvents])
  have e2 := ev hL (by omega : r < _) (e := .mul (c eS) (sub (n rem) (c acc))) (by simp [cEvents])
  have e3 := ev hL (by omega : r < _) (e := .mul (c eS) (sub (n mth) (c mth))) (by simp [cEvents])
  have e4 := ev hL (by omega : r < _) (e := .mul (c eS) (n uc)) (by simp [cEvents])
  simp only [eval_mul, eval_not, eval_sub, eval_c, eval_n, he, nxt hr] at e1 e2 e3 e4
  exact ⟨by grind, by grind, by grind, by grind⟩

/-- **A string.** -/
theorem str {s ℓ q : Nat} (seg : SegAt tr tt s ℓ) (hq : FStart tr tt s ℓ q sL) (w : String) :
    ∃ e, StrEnd tr tt s ℓ q e ∧
      pString w (win (segF tr tt s) q (ℓ - q)) = .ok (win (segF tr tt s) (q + 4) (e - q - 4),
        win (segF tr tt s) e (ℓ - e)) := by
  have hH := seg.h
  obtain ⟨hql, hq1, hst, hix, hgo⟩ := hq
  have U := u32field hL seg (Or.inl rfl) hql hq1 hst hix hgo
  obtain ⟨hp3, hfe3, hb3, hacc, hzb, hziff⟩ := U
  have F := field hL seg (x := sL) (L := 3) (by simp [FixedLen]) hql hst hix
  obtain ⟨n, hn⟩ : ∃ n, n = bvA tr tt (s + q) + 256 * bvA tr tt (s + q + 1) + 65536 * bvA tr tt (s + q + 2) :=
    ⟨_, rfl⟩
  rw [← hn] at hacc hziff
  have bl := fun j (hj : j ≤ 3) => bvA_lt hL (r := s + q + j) (by have := (F j hj).1; omega)
  have hnP : n < 16777216 := by
    have := bl 0 (by omega); have := bl 1 (by omega); have := bl 2 (by omega); simp only [Nat.add_zero] at *
    omega
  have hwv : winVal (segF tr tt s) q 4 = n := by
    rw [winVal_four]; simp only [segF]
    rw [u8b hL (by omega), u8b hL (by omega), u8b hL (by omega), u8b hL (by omega)]
    simp only [← Nat.add_assoc, hb3]; omega
  have ha : ∀ j, j ≤ 3 → tr.cell tt (s + q + j) act = 1 := by
    intro j hj; have := seg.act (q + j) (F j hj).1; rwa [← Nat.add_assoc] at this
  have hr3 : s + q + 3 < tr.height tt := by omega
  have st3 := (F 3 (by omega)).2.1
  have o3 := other0 hL hr3 (ha 3 (by omega)) (Or.inl rfl) st3
  have hS3 : tr.cell tt (s + q + 3) sS = 0 := by rw [st3] at o3; grind
  -- `vc` over the length field
  have vcL : tr.cell tt (s + q + 3) vc = tr.cell tt (s + q) vc := by
    have k : ∀ j, j < 3 → tr.cell tt (s + q + (j + 1)) vc = tr.cell tt (s + q + j) vc := by
      intro j hj
      obtain ⟨hpj, hxj, -, -, hfj, -⟩ := F j (by omega)
      obtain ⟨hf0, hal0⟩ := hfj hj
      have hrj : s + q + j < tr.height tt := by omega
      have oj := other0 hL hrj (ha j (by omega)) (Or.inl rfl) hxj
      have hsd : tr.cell tt (s + q + j) sd = 0 := by rw [sd_eq hL hrj, hf0]; grind
      rw [← Nat.add_assoc]
      exact vc_keep hL (by have := (F (j + 1) (by omega)).1; omega) (ha j (by omega)) hal0 hsd oj.2.2.2
    rw [show s + q + 3 = s + q + (2 + 1) from rfl, k 2 (by omega), k 1 (by omega),
      show s + q + 1 = s + q + (0 + 1) from rfl, k 0 (by omega), Nat.add_zero]
  have hm3 := (F 3 (by omega)).2.2.2.1
  rcases hzb with hz | hz
  · -- a non-empty string: `eS`, then the body
    have hn0 : n ≠ 0 := fun h => by rw [hziff.mpr h] at hz; exact fp_zero_ne_one hz.symm
    have hsd3 : tr.cell tt (s + q + 3) sd = 0 := by rw [sd_eq hL hr3, hz, hS3]; grind
    have hmd3 : tr.cell tt (s + q + 3) md = 0 := by rw [md_eq hL hr3, hsd3]; grind
    have hal3 : tr.cell tt (s + q + 3) al = 0 := by
      rw [al_endOK hL hr3 (ha 3 (by omega)), endOK_eq hL hr3, o3.2.1, o3.2.2.1, o3.2.2.2, hmd3]; grind
    have hq4 : q + 4 < ℓ := by
      have := seg_next hL seg (p := q + 3) hp3 (by rw [← Nat.add_assoc]; exact hal3); omega
    have hr4 : s + q + 3 + 1 < tr.height tt := by omega
    obtain ⟨hgo3, -⟩ := fgo_next hL hr4 hfe3 hal3
    have heS : tr.cell tt (s + q + 3) eS = 1 := by rw [eS_eq hL hr3, st3, hgo3, hz]; grind
    obtain ⟨hS4, hrem4, hm4, huc4⟩ := eS_next hL hr4 heS
    have hvc4 : tr.cell tt (s + q + 3 + 1) vc = tr.cell tt (s + q + 3) vc :=
      vc_keep hL hr4 (ha 3 (by omega)) hal3 hsd3 o3.2.2.2
    rw [show s + q + 3 + 1 = s + (q + 4) by omega] at hS4 hrem4 hm4 huc4 hvc4
    rw [hacc] at hrem4
    have Bd := body hL seg (p := q + 4) hq4 hS4 hrem4 (by omega) (by unfold ZkFormal.Algebra.P; omega)
    have hlast := Bd (n - 1) (by omega)
    obtain ⟨hpl, hSl, -, hml, -, hfl⟩ := hlast
    have hfl := hfl (by omega)
    have hrl : s + (q + 4) + (n - 1) < tr.height tt := by omega
    have hal : ∀ j, j ≤ n - 1 → tr.cell tt (s + (q + 4) + j) act = 1 := by
      intro j hj; have := seg.act (q + 4 + j) (Bd j (by omega)).1; rwa [← Nat.add_assoc] at this
    have ol := other0 hL hrl (hal (n - 1) (Nat.le_refl _)) (Or.inr rfl) hSl
    have hLl : tr.cell tt (s + (q + 4) + (n - 1)) sL = 0 := by rw [hSl] at ol; grind
    -- `vc` over the body
    have vcB : ∀ j, j ≤ n - 1 → tr.cell tt (s + (q + 4) + j) vc = tr.cell tt (s + (q + 4)) vc := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        obtain ⟨hpj, hSj, -, -, hfj, -⟩ := Bd j (by omega)
        obtain ⟨hf0, hal0⟩ := hfj (by omega)
        have hrj : s + (q + 4) + j < tr.height tt := by omega
        have oj := other0 hL hrj (hal j (by omega)) (Or.inr rfl) hSj
        have hsd : tr.cell tt (s + (q + 4) + j) sd = 0 := by rw [sd_eq hL hrj, hf0]; grind
        rw [← Nat.add_assoc, vc_keep hL (by omega) (hal j (by omega)) hal0 hsd oj.2.2.2, ih (by omega)]
    refine ⟨q + 4 + n, ⟨⟨by omega, by omega⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [show s + (q + 4 + n - 1) = s + (q + 4) + (n - 1) by omega, sd_eq hL hrl, hfl, hSl, hLl]; grind
    · rw [show s + (q + 4 + n - 1) = s + (q + 4) + (n - 1) by omega]; exact hfl
    · rw [show s + (q + 4 + n - 1) = s + (q + 4) + (n - 1) by omega, hml, hm4, hm3]
    · rw [show s + (q + 4 + n - 1) = s + (q + 4) + (n - 1) by omega]; exact ol
    · rw [show s + (q + 4 + n - 1) = s + (q + 4) + (n - 1) by omega, vcB (n - 1) (Nat.le_refl _), hvc4, vcL]
    · intro j h1 h2
      by_cases hj : j < q + 4
      · have := (F (j - q) (by omega)).2.1
        rw [show s + q + (j - q) = s + j by omega] at this
        exact notN hL (by omega) (by have := ha (j - q) (by omega); rwa [show s + q + (j - q) = s + j by omega] at this)
          (by simp [states]) (by decide) this
      · have := (Bd (j - (q + 4)) (by omega)).2.1
        rw [show s + (q + 4) + (j - (q + 4)) = s + j by omega] at this
        have hact := hal (j - (q + 4)) (by omega)
        rw [show s + (q + 4) + (j - (q + 4)) = s + j by omega] at hact
        exact notN hL (by omega) hact (by simp [states]) (by decide) this
    · have hu := body_utf8 hL seg (p := q + 4) hq4 hS4 hrem4 (by omega) (by unfold ZkFormal.Algebra.P; omega) huc4
      rw [pString_win (segF tr tt s) q (ℓ - q) n w (by omega) hwv hu]
      rw [show q + 4 + n - q - 4 = n by omega, show ℓ - q - 4 - n = ℓ - (q + 4 + n) by omega]
  · -- the empty string
    have hn0 : n = 0 := hziff.mp hz
    have hsd3 : tr.cell tt (s + q + 3) sd = 1 := by rw [sd_eq hL hr3, hz, hS3, st3, hfe3]; grind
    refine ⟨q + 4, ⟨⟨by omega, by omega⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [show s + (q + 4 - 1) = s + q + 3 by omega]; exact hsd3
    · rw [show s + (q + 4 - 1) = s + q + 3 by omega]; exact hfe3
    · rw [show s + (q + 4 - 1) = s + q + 3 by omega, hm3]
    · rw [show s + (q + 4 - 1) = s + q + 3 by omega]; exact o3
    · rw [show s + (q + 4 - 1) = s + q + 3 by omega]; exact vcL
    · intro j h1 h2
      have := (F (j - q) (by omega)).2.1
      rw [show s + q + (j - q) = s + j by omega] at this
      exact notN hL (by omega) (by have := ha (j - q) (by omega); rwa [show s + q + (j - q) = s + j by omega] at this)
        (by simp [states]) (by decide) this
    · rw [pString_win (segF tr tt s) q (ℓ - q) 0 w (by omega) (by rw [hwv, hn0]) (by simp [win_zero, utf8Ok])]
      rw [show q + 4 - q - 4 = 0 by omega, show ℓ - q - 4 - 0 = ℓ - (q + 4) by omega, Nat.add_zero]

end

end ZkFormal.NearV3.D1.AkmProof
