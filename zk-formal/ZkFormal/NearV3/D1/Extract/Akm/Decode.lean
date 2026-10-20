import ZkFormal.NearV3.D1.Extract.Akm.Methods

/-!
# `ZkFormal.NearV3.D1.Extract.Akm.Decode` — an `akmV3` segment decodes as an `AccessKey`

`akm_decode`: the bytes of a value segment satisfy `decodeAccessKey b = some k`, with
`k.nonce` the first 8 bytes, `k.perm = FullAccess ⇔ t₁` (and then the value is the 9 bytes
`nonce ‖ 1`), the nonce rows exactly the offsets `0 … 7` (`ix = pos`).
-/

namespace ZkFormal.NearV3.D1.AkmProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.AkmV3 NearSpecV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

section
variable (hL : TableLocal AkmV3.table tr tt pub)
include hL

/-- In state `sN`, `sO` or `sA` no accepting event: the segment goes on. -/
theorem al0_state {s ℓ : Nat} (seg : SegAt tr tt s ℓ) {p x : Nat} (hp : p < ℓ) (hx : x = sN ∨ x = sO ∨ x = sA)
    (h1 : tr.cell tt (s + p) x = 1) : tr.cell tt (s + p) al = 0 := by
  have hr : s + p < tr.height tt := by have := seg.h; omega
  have ha := seg.act p hp
  have z := oneHot hL hr ha (by rcases hx with rfl | rfl | rfl <;> simp [states]) h1
  have ne : ∀ y, y = sT ∨ y = sG ∨ y = sC ∨ y = sL ∨ y = sS → y ≠ x := by
    intro y hy; rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl | rfl <;> decide
  have hT := z sT (by simp [states]) (ne _ (by simp)); have hG := z sG (by simp [states]) (ne _ (by simp))
  have hC := z sC (by simp [states]) (ne _ (by simp)); have hLz := z sL (by simp [states]) (ne _ (by simp))
  have hSz := z sS (by simp [states]) (ne _ (by simp))
  have hsd : tr.cell tt (s + p) sd = 0 := by rw [sd_eq hL hr, hLz, hSz]; grind
  have hmd : tr.cell tt (s + p) md = 0 := by rw [md_eq hL hr, hsd]; grind
  exact al0 hL seg hp hT hG hC hmd

theorem notN' {s ℓ : Nat} (seg : SegAt tr tt s ℓ) {j x : Nat} (hj : j < ℓ) (hx : x ∈ states) (hne : x ≠ sN)
    (h1 : tr.cell tt (s + j) x = 1) : tr.cell tt (s + j) sN = 0 :=
  notN hL (by have := seg.h; omega) (seg.act j hj) hx hne h1

/-- **A function-call permission** (from the option tag). -/
theorem fcPerm {s ℓ o : Nat} (seg : SegAt tr tt s ℓ) (ho : FStart tr tt s ℓ o sO) :
    ∃ al, pFcPerm (win (segF tr tt s) o (ℓ - o)) = .ok (al, win (segF tr tt s) ℓ (ℓ - ℓ)) ∧
      ∀ j, o ≤ j → j < ℓ → tr.cell tt (s + j) sN = 0 := by
  have hH := seg.h
  obtain ⟨hol, ho1, hst, hix, hgo⟩ := ho
  have F := field hL seg (x := sO) (L := 0) (by simp [FixedLen]) hol hst hix
  have hfe := (F 0 (by omega)).2.2.2.2.2 rfl; simp only [Nat.add_zero] at hfe
  have hal := al0_state hL seg hol (Or.inr (Or.inl rfl)) hst
  have hn := seg_next hL seg hol hal
  have hr : s + o < tr.height tt := by omega
  have hr1 : s + o + 1 < tr.height tt := by omega
  obtain ⟨hgo1, hix1⟩ := fgo_next hL hr1 hfe hal
  -- the option byte is 0 or 1
  have eb := con hL hr (mem_fields (e := .mul (c sO) (.mul bE (sub bE (k 1)))) (by simp [cFields]))
  simp only [eval_mul, eval_sub, eval_k, eval_c, hst, eval_bE hL hr] at eb
  have hb01 : bvA tr tt (s + o) = 0 ∨ bvA tr tt (s + o) = 1 := by
    have hlt := bvA_lt hL hr
    rcases mul_eq_zero'.mp (by grind : ((bvA tr tt (s + o) : Nat) : Fp) * (((bvA tr tt (s + o) : Nat) : Fp) - 1) = 0)
      with h | h
    · exact Or.inl (ofNat_inj (by unfold ZkFormal.Algebra.P; omega) (by unfold ZkFormal.Algebra.P; omega) h)
    · exact Or.inr (ofNat_inj (by unfold ZkFormal.Algebra.P; omega) (by unfold ZkFormal.Algebra.P; omega)
        (sub_eq_zero'.mp h))
  have hw1 : winVal (segF tr tt s) o 1 = bvA tr tt (s + o) := by rw [winVal_one]; exact u8b hL hr
  have hbE : bE.eval tr tt (s + o) pub = ((bvA tr tt (s + o) : Nat) : Fp) := eval_bE hL hr
  -- the receiver and the method names, from a length field at `q` with `mth = 0`
  have tail : ∀ q, FStart tr tt s ℓ q sL → tr.cell tt (s + q) mth = 0 →
      ∃ x bs', pString "receiver_id" (win (segF tr tt s) q (ℓ - q)) = .ok (x, bs') ∧
        (∃ ms, pVec "method_names" (pString "method_name") bs' = .ok (ms, win (segF tr tt s) ℓ (ℓ - ℓ))) ∧
        ∀ j, q ≤ j → j < ℓ → tr.cell tt (s + j) sN = 0 := by
    intro q hq hm
    obtain ⟨e, E, hp⟩ := str hL seg hq "receiver_id"
    have hC := rcv_to_count hL seg E hm
    obtain ⟨ms, hms, hnoN⟩ := vecMethods hL seg hC
    refine ⟨_, _, hp, ⟨ms, hms⟩, fun j h1 h2 => ?_⟩
    by_cases hj : j < e
    · exact E.noN j h1 hj
    · exact hnoN j (by omega) h2
  have noO : tr.cell tt (s + o) sN = 0 := notN' hL seg hol (by simp [states]) (by decide) hst
  simp only [pFcPerm, pOption, bind, Except.bind]
  rw [pU8_win (segF tr tt s) o (ℓ - o) (by omega), hw1]
  rcases hb01 with hb | hb
  · -- no allowance
    have hb1 : (Dsl.not bE).eval tr tt (s + o) pub = 1 := by rw [eval_not, hbE, hb]; grind
    have hL1 := transGo hL hr1 hal (a := c sO) (b := Dsl.not bE) (x := sL) (by simp [cEvents])
      (by simp only [eval_c]; exact hst) hb1
    have hm1 := transGoz hL hr1 hal (a := c sO) (b := Dsl.not bE) (x := mth) (by simp [cEvents])
      (by simp only [eval_c]; exact hst) hb1
    rw [show s + o + 1 = s + (o + 1) by omega] at hL1 hm1 hix1
    obtain ⟨x, bs', hp, ⟨ms, hms⟩, hnoN⟩ := tail (o + 1)
      ⟨by omega, by omega, hL1, hix1, by rw [show s + (o + 1) - 1 = s + o by omega]; exact hgo1⟩ hm1
    rw [hb]; simp only [pure, Except.pure]
    rw [show ℓ - o - 1 = ℓ - (o + 1) by omega, hp]; simp only [hms]
    refine ⟨_, rfl, fun j h1 h2 => ?_⟩
    by_cases hj : j = o
    · subst hj; exact noO
    · exact hnoN j (by omega) h2
  · -- an allowance (`u128`)
    have hb1 : bE.eval tr tt (s + o) pub = 1 := by rw [hbE, hb]; rfl
    have hA1 := transGo hL hr1 hal (a := c sO) (b := bE) (x := sA) (by simp [cEvents])
      (by simp only [eval_c]; exact hst) hb1
    rw [show s + o + 1 = s + (o + 1) by omega] at hA1 hix1
    have FA := field hL seg (x := sA) (L := 15) (by simp [FixedLen]) (p := o + 1) (by omega) hA1 hix1
    obtain ⟨hp16, hA16, -, -, -, hfe16⟩ := FA 15 (by omega)
    have hfe16 := hfe16 rfl
    have hal16 := al0_state hL seg (p := o + 1 + 15) hp16 (Or.inr (Or.inr rfl)) (by rw [← Nat.add_assoc]; exact hA16)
    have hn16 := seg_next hL seg hp16 hal16
    have hr17 : s + (o + 1 + 15) + 1 < tr.height tt := by omega
    obtain ⟨hgo16, hix17⟩ := fgo_next hL hr17 (by rw [← Nat.add_assoc] at hfe16; exact hfe16) hal16
    have hL17 := trans3 hL hr17 (a := c sA) (b := c fgo) (x := sL) (by simp [cEvents])
      (by simp only [eval_c]; rw [← Nat.add_assoc] at hA16; exact hA16) (by simp only [eval_c]; exact hgo16)
    have hm17 := trans3z hL hr17 (a := c sA) (b := c fgo) (x := mth) (by simp [cEvents])
      (by simp only [eval_c]; rw [← Nat.add_assoc] at hA16; exact hA16) (by simp only [eval_c]; exact hgo16)
    rw [show s + (o + 1 + 15) + 1 = s + (o + 17) by omega] at hL17 hm17 hix17
    obtain ⟨x, bs', hp, ⟨ms, hms⟩, hnoN⟩ := tail (o + 17)
      ⟨by omega, by omega, hL17, hix17, by rw [show s + (o + 17) - 1 = s + (o + 1 + 15) by omega]; exact hgo16⟩ hm17
    rw [hb]
    dsimp only
    rw [pU128_win (segF tr tt s) (o + 1) (ℓ - o - 1) (by omega)]
    simp only [pure, Except.pure]
    rw [show ℓ - o - 1 - 16 = ℓ - (o + 17) by omega, show o + 1 + 16 = o + 17 by omega, hp]; simp only [hms]
    refine ⟨_, rfl, fun j h1 h2 => ?_⟩
    by_cases hj : j = o
    · subst hj; exact noO
    · by_cases hj2 : j < o + 17
      · have := (FA (j - (o + 1)) (by omega)).2.1
        rw [show s + (o + 1) + (j - (o + 1)) = s + j by omega] at this
        exact notN' hL seg (by omega) (by simp [states]) (by decide) this
      · exact hnoN j (by omega) h2

/-- **Gas-key info** (`u128 ‖ u16`). -/
theorem gki {s ℓ g : Nat} (seg : SegAt tr tt s ℓ) (hg : FStart tr tt s ℓ g sG) :
    g + 17 < ℓ ∧ tr.cell tt (s + (g + 17)) fe = 1 ∧ tr.cell tt (s + (g + 17)) sG = 1 ∧
    pGasKeyInfo (win (segF tr tt s) g (ℓ - g)) = .ok ((), win (segF tr tt s) (g + 18) (ℓ - (g + 18))) ∧
    ∀ j, g ≤ j → j < g + 18 → tr.cell tt (s + j) sN = 0 := by
  obtain ⟨hgl, hg1, hst, hix, hgo⟩ := hg
  have F := field hL seg (x := sG) (L := 17) (by simp [FixedLen]) hgl hst hix
  obtain ⟨hp, hG, -, -, -, hfe⟩ := F 17 (by omega)
  rw [Nat.add_assoc] at hG
  refine ⟨hp, by rw [← Nat.add_assoc]; exact hfe rfl, hG, ?_, fun j h1 h2 => ?_⟩
  · simp only [pGasKeyInfo, bind, Except.bind]
    rw [pU128_win (segF tr tt s) g (ℓ - g) (by omega)]
    simp only
    rw [pU16_win (segF tr tt s) (g + 16) (ℓ - g - 16) (by omega)]
    simp only [pure, Except.pure]
    rw [show g + 16 + 2 = g + 18 by omega, show ℓ - g - 16 - 2 = ℓ - (g + 18) by omega]
  · have := (F (j - g) (by omega)).2.1
    rw [show s + g + (j - g) = s + j by omega] at this
    exact notN' hL seg (by omega) (by simp [states]) (by decide) this

theorem t_bool (x : Nat) (hx : x < 4) : t x ∈ boolCols := by
  rcases (show x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

theorem t_const (x : Nat) (hx : x < 4) : t x ∈ segConst := by
  rcases (show x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 by omega) with rfl | rfl | rfl | rfl <;> simp [segConst]

/-- **The access-key value of a segment decodes.** -/
theorem akm_decode {s ℓ : Nat} (seg : SegAt tr tt s ℓ) :
    ∃ k, decodeAccessKey (win (segF tr tt s) 0 ℓ) = some k ∧ k.nonce = winVal (segF tr tt s) 0 8 ∧
      (k.perm = .fullAccess ↔ tr.cell tt s (t 1) = 1) ∧
      (tr.cell tt s (t 1) = 1 → ℓ = 9 ∧ bvA tr tt (s + 8) = 1) ∧ 9 ≤ ℓ ∧
      (∀ j, j < 8 → tr.cell tt (s + j) sN = 1 ∧ tr.cell tt (s + j) ix = ((j : Nat) : Fp)) ∧
      (∀ j, 8 ≤ j → j < ℓ → tr.cell tt (s + j) sN = 0) ∧ tr.cell tt (s + 8) sT = 1 := by
  have hH := seg.h
  have h0 : 0 < ℓ := seg.pos
  have hr0 : s < tr.height tt := by omega
  have haf : tr.cell tt s af = 1 := by simpa using seg.af 0 h0
  have e1 := con hL hr0 (mem_shape (e := .mul (c af) (not (c sN))) (by simp [cShape]))
  have e2 := con hL hr0 (mem_shape (e := .mul (c af) (c ix)) (by simp [cShape]))
  simp only [eval_mul, eval_not, eval_c, haf] at e1 e2
  have hN0 : tr.cell tt (s + 0) sN = 1 := by simp only [Nat.add_zero]; grind
  have hix0 : tr.cell tt (s + 0) ix = 0 := by simp only [Nat.add_zero]; grind
  have FN := field hL seg (x := sN) (L := 7) (by simp [FixedLen]) h0 hN0 hix0
  obtain ⟨hp7, hN7, -, -, -, hfe7⟩ := FN 7 (by omega)
  have hfe7 := hfe7 rfl
  simp only [Nat.add_zero] at hN7 hfe7
  have hal7 := al0_state hL seg hp7 (Or.inl rfl) hN7
  have hn7 := seg_next hL seg hp7 hal7
  have hr8 : s + 7 + 1 < tr.height tt := by omega
  obtain ⟨hgo7, hix8⟩ := fgo_next hL hr8 hfe7 hal7
  have hT8 := trans3 hL hr8 (a := c sN) (b := c fgo) (x := sT) (by simp [cEvents])
    (by simp only [eval_c]; exact hN7) (by simp only [eval_c]; exact hgo7)
  rw [show s + 7 + 1 = s + 8 by omega] at hT8 hix8
  have FT := field hL seg (x := sT) (L := 0) (by simp [FixedLen]) (p := 8) (by omega) hT8 hix8
  have hfe8 := (FT 0 (by omega)).2.2.2.2.2 rfl; simp only [Nat.add_zero] at hfe8
  have hr8' : s + 8 < tr.height tt := by omega
  have ha8 : tr.cell tt (s + 8) act = 1 := seg.act 8 (by omega)
  -- the tag
  have ct := fun x (hx : x < 4) => seg.const 8 (by omega) (t x) (t_const hL x hx)
  have et := con hL hr8' (mem_shape (e := .mul (c sT) (sub bE tagE)) (by simp [cShape]))
  have eh := con hL hr0 (mem_shape (e := .mul (c act) (sub (sum ((List.range 4).map fun x => c (t x))) (k 1)))
    (by simp [cShape]))
  simp only [tagE, eval_mul, eval_sub, eval_add, eval_smul, eval_c, eval_sum_cons, eval_sum_nil, eval_k,
    hT8, eval_bE hL hr8', ct 1 (by omega), ct 2 (by omega), ct 3 (by omega)] at et
  simp only [List.range, List.range.loop, List.map_cons, List.map_nil, eval_mul, eval_sub, eval_sum_cons,
    eval_sum_nil, eval_c, eval_k] at eh
  have ha0 : tr.cell tt s act = 1 := by simpa using seg.act 0 h0
  rw [ha0] at eh
  have tb := fun x (hx : x < 4) => isBool hL hr0 (t_bool hL x hx)
  -- row 8: only `sT`
  have z8 := oneHot hL hr8' ha8 (by simp [states]) hT8
  have hG8 := z8 sG (by simp [states]) (by decide); have hC8 := z8 sC (by simp [states]) (by decide)
  have hL8 := z8 sL (by simp [states]) (by decide); have hS8 := z8 sS (by simp [states]) (by decide)
  have hmd8 : tr.cell tt (s + 8) md = 0 := by
    rw [md_eq hL hr8', sd_eq hL hr8', hL8, hS8]; grind
  have hal8 : tr.cell tt (s + 8) al = tr.cell tt s (t 1) := by
    rw [al_endOK hL hr8' ha8, endOK_eq hL hr8', hT8, hG8, hC8, hmd8, ct 1 (by omega)]; grind
  have noN8 : tr.cell tt (s + 8) sN = 0 := notN' hL seg (by omega) (by simp [states]) (by decide) hT8
  have nonce : ∀ j, j < 8 → tr.cell tt (s + j) sN = 1 ∧ tr.cell tt (s + j) ix = ((j : Nat) : Fp) :=
    fun j hj => ⟨(FN j (by omega)).2.1, (FN j (by omega)).2.2.1⟩
  have hb8l := bvA_lt hL hr8'
  have hw8 : winVal (segF tr tt s) 8 1 = bvA tr tt (s + 8) := by rw [winVal_one]; exact u8b hL hr8'
  have tag : ∀ v : Nat, ((v : Nat) : Fp) = ((bvA tr tt (s + 8) : Nat) : Fp) → v < 4 → bvA tr tt (s + 8) = v :=
    fun v h hv => (ofNat_inj (by unfold ZkFormal.Algebra.P; omega) (by unfold ZkFormal.Algebra.P; omega) h).symm
  have hr9 : s + 8 + 1 < tr.height tt → True := fun _ => trivial
  rcases tb 1 (by omega) with t1z | t1o
  · -- not FullAccess: the segment goes on after the tag
    have notFA : ¬ (tr.cell tt s (t 1) = 1) := by rw [t1z]; exact fp_zero_ne_one
    have hal8' : tr.cell tt (s + 8) al = 0 := by rw [hal8, t1z]
    have hn8 := seg_next hL seg (p := 8) (by omega) hal8'
    have hr9 : s + 8 + 1 < tr.height tt := by omega
    obtain ⟨hgo8, hix9⟩ := fgo_next hL hr9 hfe8 hal8'
    rcases tb 0 (by omega) with t0z | t0o
    · -- a gas key (tag 2 or 3)
      have h23 : tr.cell tt s (t 2) + tr.cell tt s (t 3) = 1 := by rw [t0z, t1z] at eh; grind
      have hG9 := transGo hL hr9 hal8' (a := c sT) (b := .add (c (t 2)) (c (t 3))) (x := sG) (by simp [cEvents])
        (by simp only [eval_c]; exact hT8) (by simp only [eval_add, eval_c, ct 2 (by omega), ct 3 (by omega)]; exact h23)
      rw [show s + 8 + 1 = s + 9 by omega] at hG9 hix9
      obtain ⟨hp26, hfe26, hG26, hgk, hnoG⟩ := gki hL seg (g := 9)
        ⟨by omega, by omega, hG9, hix9, by rw [show s + 9 - 1 = s + 8 by omega]; exact hgo8⟩
      have hr26 : s + (9 + 17) < tr.height tt := by omega
      have ha26 := seg.act (9 + 17) hp26
      have z26 := oneHot hL hr26 ha26 (by simp [states]) hG26
      have hT26 := z26 sT (by simp [states]) (by decide); have hC26 := z26 sC (by simp [states]) (by decide)
      have hmd26 : tr.cell tt (s + (9 + 17)) md = 0 := by
        rw [md_eq hL hr26, sd_eq hL hr26, z26 sL (by simp [states]) (by decide), z26 sS (by simp [states]) (by decide)]
        grind
      have c26 := seg.const (9 + 17) hp26 (t 3) (t_const hL 3 (by omega))
      have hal26 : tr.cell tt (s + (9 + 17)) al = tr.cell tt s (t 3) := by
        rw [al_endOK hL hr26 ha26, endOK_eq hL hr26, hT26, hC26, hmd26, hG26, hfe26, c26]; grind
      rcases tb 3 (by omega) with t3z | t3o
      · -- tag 2: gas key info, then a function-call permission
        have t2o : tr.cell tt s (t 2) = 1 := by rw [t3z] at h23; grind
        have hb : bvA tr tt (s + 8) = 2 := tag 2 (by rw [t1z, t2o, t3z] at et; grind) (by omega)
        have hal26' : tr.cell tt (s + (9 + 17)) al = 0 := by rw [hal26, t3z]
        have hn26 := seg_next hL seg hp26 hal26'
        have hr27 : s + (9 + 17) + 1 < tr.height tt := by omega
        obtain ⟨hgo26, hix27⟩ := fgo_next hL hr27 hfe26 hal26'
        have e4 := ev hL hr26 (e := mul3 (c sG) (c fgo) (.mul (c (t 2)) (not (n sO)))) (by simp [cEvents])
        have c262 := seg.const (9 + 17) hp26 (t 2) (t_const hL 2 (by omega))
        simp only [eval_mul3, eval_mul, eval_not, eval_c, eval_n, hG26, hgo26, c262, t2o, nxt hr27] at e4
        have hO27 : tr.cell tt (s + 27) sO = 1 := by rw [show s + 27 = s + (9 + 17) + 1 by omega]; grind
        rw [show s + (9 + 17) + 1 = s + 27 by omega] at hix27
        obtain ⟨al', hfc, hnoO⟩ := fcPerm hL seg (o := 27)
          ⟨by omega, by omega, hO27, hix27, by rw [show s + 27 - 1 = s + (9 + 17) by omega]; exact hgo26⟩
        refine ⟨⟨winVal (segF tr tt s) 0 8, .gasKey⟩, ?_, rfl, ⟨fun h => (nomatch h), fun h => absurd h notFA⟩, fun h => absurd h notFA, by omega,
          nonce, fun j h1 h2 => ?_, hT8⟩
        · unfold decodeAccessKey
          simp only [bind, Except.bind]
          rw [pU64_win (segF tr tt s) 0 ℓ (by omega)]
          dsimp only
          rw [pU8_win (segF tr tt s) 8 (ℓ - 8) (by omega), hw8, hb]
          dsimp only
          rw [show ℓ - 8 - 1 = ℓ - 9 by omega, hgk]
          dsimp only
          rw [show ℓ - (9 + 18) = ℓ - 27 by omega, show 9 + 18 = 27 by omega, hfc]
          simp [pure, Except.pure, win]
        · by_cases hj : j = 8
          · subst hj; exact noN8
          · by_cases hj2 : j < 27
            · exact hnoG j (by omega) (by omega)
            · exact hnoO j (by omega) h2
      · -- tag 3: gas key info only
        have t2z : tr.cell tt s (t 2) = 0 := by rw [t3o] at h23; grind
        have hb : bvA tr tt (s + 8) = 3 := tag 3 (by rw [t1z, t2z, t3o] at et; grind) (by omega)
        have hee := seg_end hL seg hp26 (by rw [hal26, t3o])
        refine ⟨⟨winVal (segF tr tt s) 0 8, .gasKey⟩, ?_, rfl, ⟨fun h => (nomatch h), fun h => absurd h notFA⟩, fun h => absurd h notFA, by omega,
          nonce, fun j h1 h2 => ?_, hT8⟩
        · unfold decodeAccessKey
          simp only [bind, Except.bind]
          rw [pU64_win (segF tr tt s) 0 ℓ (by omega)]
          dsimp only
          rw [pU8_win (segF tr tt s) 8 (ℓ - 8) (by omega), hw8, hb]
          dsimp only
          rw [show ℓ - 8 - 1 = ℓ - 9 by omega, hgk]
          simp [pure, Except.pure, win, show ℓ - (9 + 18) = 0 by omega]
        · by_cases hj : j = 8
          · subst hj; exact noN8
          · exact hnoG j (by omega) (by omega)
    · -- tag 0: a function-call permission
      have hb : bvA tr tt (s + 8) = 0 := by
        have h2z : tr.cell tt s (t 2) = 0 := by
          rcases tb 2 (by omega) with h | h
          · exact h
          · rw [t0o, t1z, h] at eh; exfalso; revert eh; rcases tb 3 (by omega) with h3 | h3 <;> rw [h3] <;> decide
        have h3z : tr.cell tt s (t 3) = 0 := by
          rcases tb 3 (by omega) with h | h
          · exact h
          · rw [t0o, t1z, h2z, h] at eh; exfalso; revert eh; decide
        exact tag 0 (by rw [t1z, h2z, h3z] at et; grind) (by omega)
      have hO9 := transGo hL hr9 hal8' (a := c sT) (b := c (t 0)) (x := sO) (by simp [cEvents])
        (by simp only [eval_c]; exact hT8) (by simp only [eval_c, ct 0 (by omega)]; exact t0o)
      rw [show s + 8 + 1 = s + 9 by omega] at hO9 hix9
      obtain ⟨al', hfc, hnoO⟩ := fcPerm hL seg (o := 9)
        ⟨by omega, by omega, hO9, hix9, by rw [show s + 9 - 1 = s + 8 by omega]; exact hgo8⟩
      refine ⟨⟨winVal (segF tr tt s) 0 8, .functionCall al'⟩, ?_, rfl, ⟨fun h => (nomatch h), fun h => absurd h notFA⟩, fun h => absurd h notFA,
        by omega, nonce, fun j h1 h2 => ?_, hT8⟩
      · unfold decodeAccessKey
        simp only [bind, Except.bind]
        rw [pU64_win (segF tr tt s) 0 ℓ (by omega)]
        dsimp only
        rw [pU8_win (segF tr tt s) 8 (ℓ - 8) (by omega), hw8, hb]
        dsimp only
        rw [show ℓ - 8 - 1 = ℓ - 9 by omega, show 8 + 1 = 9 by omega, hfc]
        simp [pure, Except.pure, win]
      · by_cases hj : j = 8
        · subst hj; exact noN8
        · exact hnoO j (by omega) h2
  · -- FullAccess: the segment ends at the tag
    have hee := seg_end hL seg (p := 8) (by omega) (by rw [hal8, t1o])
    have h023 : tr.cell tt s (t 0) = 0 ∧ tr.cell tt s (t 2) = 0 ∧ tr.cell tt s (t 3) = 0 := by
      rcases tb 0 (by omega) with h0 | h0 <;> rcases tb 2 (by omega) with h2 | h2 <;>
        rcases tb 3 (by omega) with h3 | h3 <;> rw [h0, t1o, h2, h3] at eh <;>
        first | exact ⟨h0, h2, h3⟩ | (exfalso; revert eh; decide)
    have hb : bvA tr tt (s + 8) = 1 := tag 1 (by rw [t1o, h023.2.1, h023.2.2] at et; grind) (by omega)
    refine ⟨⟨winVal (segF tr tt s) 0 8, .fullAccess⟩, ?_, rfl, ⟨fun _ => t1o, fun _ => rfl⟩,
      fun _ => ⟨by omega, hb⟩, by omega, nonce, fun j h1 h2 => (show j = 8 by omega) ▸ noN8, hT8⟩
    unfold decodeAccessKey
    simp only [bind, Except.bind]
    rw [pU64_win (segF tr tt s) 0 ℓ (by omega)]
    dsimp only
    rw [pU8_win (segF tr tt s) 8 (ℓ - 8) (by omega), hw8, hb]
    simp [pure, Except.pure, win, show ℓ - 8 - 1 = 0 by omega]


end

end ZkFormal.NearV3.D1.AkmProof
