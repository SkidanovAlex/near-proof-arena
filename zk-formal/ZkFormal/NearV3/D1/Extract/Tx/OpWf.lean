import ZkFormal.NearV3.D1.Extract.Tx.RowT
import ZkFormal.NearV3.D1.Extract.TxView

/-!
# `ZkFormal.NearV3.D1.Extract.Tx.OpWf` — the entry of an op and its facts (`opWf`)
-/

namespace ZkFormal.NearV3.D1.TxProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.TxV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

def laneOf (tr : Trace Fp) (tt r : Nat) : TxLaneE :=
  ⟨cv tr tt r g, cv tr tt r xN, cv tr tt r xB, cv tr tt r xC, cv tr tt r amt, cv tr tt r lk,
   cv tr tt r st, cv tr tt r mo, cv tr tt r kn, cv tr tt r nk⟩

def txOf (tr : Trace Fp) (tt s : Nat) : TxE :=
  { op := cv tr tt s op, kind := cv tr tt s kind, strict := cv tr tt s strict, okP := cv tr tt s okP,
    tov := cv tr tt s tov, stage := cv tr tt s stage, cok := cv tr tt s cok, valid := cv tr tt s valid,
    s1 := cv tr tt s s1, s2 := cv tr tt s s2, cand := cv tr tt s cand, wr := cv tr tt s wr,
    fa := cv tr tt s fa, vidA := cv tr tt s vidA, vidK := cv tr tt s vidK, tpA := cv tr tt s tpA,
    tpK := cv tr tt s tpK, fW := cv tr tt s fW, fK := cv tr tt s fK,
    ln := (List.range 16).map fun j => laneOf tr tt (s + j) }

theorem lane_txOf (s j : Nat) (hj : j < 16) : (txOf tr tt s).lane j = laneOf tr tt (s + j) := by
  simp [TxE.lane, txOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]

theorem val_txOf (s : Nat) (f : TxLaneE → Nat) :
    (txOf tr tt s).val f = RcptProof.sumL (fun j => f (laneOf tr tt (s + j))) 16 :=
  RcptProof.sumL_congr _ _ 16 (fun j hj => by rw [lane_txOf s j hj])

/-- Boolean cell ↦ `cv ≤ 1` and the `= 1` / `= 0` correspondences. -/
theorem cv_b {r x : Nat} (h : tr.cell tt r x = 0 ∨ tr.cell tt r x = 1) :
    (cv tr tt r x = 0 ∧ tr.cell tt r x = 0) ∨ (cv tr tt r x = 1 ∧ tr.cell tt r x = 1) := by
  rcases h with h | h
  · exact Or.inl ⟨cv_zero_iff.mpr h, h⟩
  · exact Or.inr ⟨cv_one_iff.mpr h, h⟩

theorem sumL_zero_iff (f : Nat → Nat) : ∀ L, RcptProof.sumL f L = 0 ↔ ∀ i, i < L → f i = 0
  | 0 => by simp [RcptProof.sumL]
  | L + 1 => by
    have ih := sumL_zero_iff f L
    have hp : 0 < 256 ^ L := Nat.pow_pos (by omega)
    simp only [RcptProof.sumL]
    constructor
    · intro h i hi
      have h1 : RcptProof.sumL f L = 0 := by omega
      have h2 : 256 ^ L * f L = 0 := by omega
      rcases Nat.lt_or_ge i L with hl | hl
      · exact ih.mp h1 i hl
      · have : i = L := by omega
        subst this
        rcases Nat.mul_eq_zero.mp h2 with h | h
        · omega
        · exact h
    · intro h
      rw [ih.mpr (fun i hi => h i (by omega)), h L (by omega)]; simp

theorem msV_zero_of {s : Nat} : ∀ k, (∀ i, i ≤ k → bv tr tt (s + i) rCb = 255) → msV tr tt s k = 0
  | 0, h => by have := h 0 (by omega); simp only [Nat.add_zero] at this; simp [msV, this]
  | k + 1, h => by
    rw [msV_succ, msV_zero_of k (fun i hi => h i (by omega)), h (k + 1) (by omega)]

theorem two128_eq : NearSpec.Params.two128 = 256 ^ 16 := RcptProof.two128

/-- Cells as naturals: a field equation between small values is a `Nat` equation. -/
theorem cv_of_eq {r x : Nat} {n : Nat} (hn : n < P) (h : tr.cell tt r x = ((n : Nat) : Fp)) :
    cv tr tt r x = n := by
  unfold cv; rw [h, natCast_eq, Fp.toNat_ofNat, Nat.mod_eq_of_lt hn]

section
variable (hL : TableLocal TxV3.table tr tt pub)
include hL

/-- Written amount lanes: with `wr = 1`, `mo` is the chain result `rC`. -/
theorem mo_rC {s : Nat} (hop : OpAt tr tt s) (hw : tr.cell tt s wr = 1) (j : Nat) (hj : j < 16) :
    cv tr tt (s + j) mo = bv tr tt (s + j) rCb := by
  have hH := hop.h
  have hl := (laneFlags hL hop j hj).2.2.2.1
  rw [hw] at hl
  have hd := bv_lt hL (r := s + j) (by omega) rCb_bool
  have : tr.cell tt (s + j) mo = ((bv tr tt (s + j) rCb : Nat) : Fp) := by grind
  unfold cv; rw [this, natCast_eq, Fp.toNat_ofNat, Nat.mod_eq_of_lt (by unfold P; omega)]

/-- Byte inputs of the op at `s`. -/
structure InBytes (tr : Trace Fp) (tt s : Nat) : Prop where
  xN : ∀ j, j < 16 → cv tr tt (s + j) xN < 256
  xB : ∀ j, j < 16 → cv tr tt (s + j) xB < 256
  xC : ∀ j, j < 16 → cv tr tt (s + j) xC < 256
  amt : ∀ j, j < 16 → cv tr tt (s + j) amt < 256
  lk : ∀ j, j < 16 → cv tr tt (s + j) lk < 256
  st : ∀ j, j < 16 → cv tr tt (s + j) st < 256
  kn : ∀ j, j < 16 → cv tr tt (s + j) kn < 256

local notation "SL" f => RcptProof.sumL f 16

theorem bvSum_lt {s : Nat} (hop : OpAt tr tt s) {f : Nat → Nat} (hf : ∀ b, b < 8 → f b ∈ boolCols) :
    (SL (fun j => bv tr tt (s + j) f)) < 256 ^ 16 :=
  RcptProof.sumL_lt _ 16 (fun j hj => bv_lt hL (r := s + j) (by have := hop.h; omega) hf)

theorem cvb {r x : Nat} (hr : r < tr.height tt) (hx : x ∈ boolCols) : cv tr tt r x ≤ 1 := cv_bool' hL hr hx

/-- **Debit verdict** in naturals. -/
theorem arith_debit {s : Nat} (hop : OpAt tr tt s) (hb : InBytes tr tt s) (hk : tr.cell tt s kind = 0) :
    (cv tr tt s okP = 1 ↔ (cv tr tt s s2 = 1 ∧ cv tr tt s fa = 1 ∧
      (SL (fun j => cv tr tt (s + j) kn)) < (SL (fun j => cv tr tt (s + j) xN)) ∧
      (cv tr tt s strict ≠ 0 → (SL (fun j => cv tr tt (s + j) xN)) = (SL (fun j => cv tr tt (s + j) kn)) + 1) ∧
      (SL (fun j => cv tr tt (s + j) xN)) < (SL (fun j => cv tr tt (s + j) xB)) ∧
      (SL (fun j => cv tr tt (s + j) xC)) ≤ (SL (fun j => cv tr tt (s + j) amt)) ∧
      (SL (fun j => cv tr tt (s + j) amt)) - (SL (fun j => cv tr tt (s + j) xC)) +
        (SL (fun j => cv tr tt (s + j) lk)) < 256 ^ 16 ∧
      ((NearSpec.Params.storageAmountPerByte * (SL (fun j => cv tr tt (s + j) st))) % NearSpec.Params.two128 ≤
          (SL (fun j => cv tr tt (s + j) amt)) - (SL (fun j => cv tr tt (s + j) xC)) +
            (SL (fun j => cv tr tt (s + j) lk)) ∨
        (SL (fun j => cv tr tt (s + j) st)) ≤ NearSpec.Params.zeroBalanceStorageLimit))) ∧
    (cv tr tt s okP = 1 → tr.cell tt (s + 15) coC = 0) := by
  have hH := hop.h
  have h15 : s + 15 < tr.height tt := by omega
  have cN := chainN hL hop hb.xN hb.kn
  have cB := chainB hL hop hb.xB hb.xN
  have cC := chainC_debit hL hop hk hb.amt hb.xC
  have cT := chainT hL hop hb.lk
  have cD := chainD hL hop
  have cS := chainS hL hop hb.st
  have cQ := chainQ hL hop hb.st
  have zz := (zN_iff hL hop 15 (by omega))
  have hz : cv tr tt (s + 15) zN = 1 ↔ (SL (fun j => bv tr tt (s + j) dNb)) = 0 := by
    rw [cv_one_iff, zz.2, sumL_zero_iff]
    exact ⟨fun h i hi => h i (by omega), fun h i hi => h i (by omega)⟩
  have hv := verdict_debit hL hop hk
  have ad := debit_arith (strict := cv tr tt s strict)
    (cvb hL h15 (by simp [boolCols])) (cvb hL h15 (by simp [boolCols])) (cvb hL h15 (by simp [boolCols]))
    (cvb hL h15 (by simp [boolCols])) (cvb hL h15 (by simp [boolCols])) (cvb hL h15 (by simp [boolCols]))
    cN (bvSum_lt hL hop dNb_bool) hz cB (bvSum_lt hL hop dBb_bool) cC (bvSum_lt hL hop rCb_bool)
    cT (bvSum_lt hL hop tTb_bool) cD (bvSum_lt hL hop dQb_bool) cS (bvSum_lt hL hop dSb_bool)
  rw [← cQ]
  simp only [cv_one_iff, cv_zero_iff, ne_eq] at ad hz ⊢
  rw [hv]
  refine ⟨?_, fun h => h.2.2.2.2.2.1⟩
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, ad.mp h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, ad.mpr h3⟩

/-- The debit write: `rC = A − C` once `coC₁₅ = 0`. -/
theorem write_debit {s : Nat} (hop : OpAt tr tt s) (hb : InBytes tr tt s) (hk : tr.cell tt s kind = 0)
    (hc : tr.cell tt (s + 15) coC = 0) :
    (SL (fun j => bv tr tt (s + j) rCb)) =
      (SL (fun j => cv tr tt (s + j) amt)) - (SL (fun j => cv tr tt (s + j) xC)) := by
  have cC := chainC_debit hL hop hk hb.amt hb.xC
  rw [cv_zero_iff.mpr hc] at cC
  exact (debit_write cC).1

/-- **Credit facts** in naturals. -/
theorem arith_credit {s : Nat} (hop : OpAt tr tt s) (hb : InBytes tr tt s) (hk : tr.cell tt s kind = 1) :
    (SL (fun j => bv tr tt (s + j) rCb)) =
        (SL (fun j => cv tr tt (s + j) amt)) + (SL (fun j => cv tr tt (s + j) xC)) ∧
    (SL (fun j => bv tr tt (s + j) rCb)) < NearSpec.Params.u128Max ∧
    (SL (fun j => bv tr tt (s + j) rCb)) + (SL (fun j => cv tr tt (s + j) lk)) < 256 ^ 16 ∧
    ((NearSpec.Params.storageAmountPerByte * (SL (fun j => cv tr tt (s + j) st))) % NearSpec.Params.two128 ≤
        (SL (fun j => bv tr tt (s + j) rCb)) + (SL (fun j => cv tr tt (s + j) lk)) ∨
      (SL (fun j => cv tr tt (s + j) st)) ≤ NearSpec.Params.zeroBalanceStorageLimit) := by
  have hH := hop.h
  have h15 : s + 15 < tr.height tt := by omega
  obtain ⟨vc, vt, vm, vqs⟩ := verdict_credit hL hop hk
  have cC := chainC_credit hL hop hk hb.amt hb.xC
  have cT := chainT hL hop hb.lk
  have cD := chainD hL hop
  have cS := chainS hL hop hb.st
  have cQ := chainQ hL hop hb.st
  rw [cv_zero_iff.mpr vc] at cC
  rw [cv_zero_iff.mpr vt] at cT
  have ac := credit_arith (cvb hL h15 (by simp [boolCols])) (cvb hL h15 (by simp [boolCols])) cC cT cD
    (bvSum_lt hL hop dQb_bool) cS (bvSum_lt hL hop dSb_bool) (bvSum_lt hL hop tTb_bool)
    (by rw [cv_one_iff, cv_one_iff]; exact vqs)
  rw [← cQ]
  refine ⟨ac.1, ?_, ac.2.1, ac.2.2⟩
  -- `msum ≠ 0`: some lane of `rC` is not `255`
  have hm := msum_val hL hop 15 (by omega)
  have hne : msV tr tt s 15 ≠ 0 := by
    intro h0; rw [h0] at hm; exact vm hm
  have : ∃ i, i ≤ 15 ∧ bv tr tt (s + i) rCb ≠ 255 := by
    refine Classical.byContradiction fun hn => hne (msV_zero_of 15 fun i hi => ?_)
    exact Classical.byContradiction fun h => hn ⟨i, hi, h⟩
  obtain ⟨i, hi, hne'⟩ := this
  exact RcptProof.sumL16_notmax _ (fun k hk => bv_lt hL (r := s + k) (by omega) rCb_bool) i (by omega) hne'

/-- **The facts of one op.** -/
theorem opWf {s : Nat} (hop : OpAt tr tt s) : TxOpWf (txOf tr tt s) := by
  have hH := hop.h
  have hr : s < tr.height tt := by omega
  have bk := cv_b (isBool hL hr (x := kind) (by simp [boolCols]))
  have bs1 := cv_b (isBool hL hr (x := s1) (by simp [boolCols]))
  have bs2 := cv_b (isBool hL hr (x := s2) (by simp [boolCols]))
  have bva := cv_b (isBool hL hr (x := valid) (by simp [boolCols]))
  have bco := cv_b (isBool hL hr (x := cok) (by simp [boolCols]))
  have bok := cv_b (isBool hL hr (x := okP) (by simp [boolCols]))
  have btv := cv_b (isBool hL hr (x := tov) (by simp [boolCols]))
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := opFlags hL hop
  have hP : (2 : Nat) < P := by unfold P; omega
  refine ⟨by simp [txOf], ⟨cvb hL hr (by simp [boolCols]), cvb hL hr (by simp [boolCols]),
    cvb hL hr (by simp [boolCols]), cvb hL hr (by simp [boolCols]), cvb hL hr (by simp [boolCols]),
    cvb hL hr (by simp [boolCols]), cvb hL hr (by simp [boolCols]), cvb hL hr (by simp [boolCols]),
    cvb hL hr (by simp [boolCols])⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- stage
    show cv tr tt s stage = cv tr tt s s1 + cv tr tt s s2
    rcases bs1 with ⟨a1, c1⟩ | ⟨a1, c1⟩ <;> rcases bs2 with ⟨a2, c2⟩ | ⟨a2, c2⟩ <;> rw [a1, a2] <;>
      exact cv_of_eq (by unfold P; omega) (by rw [f1, c1, c2]; first | rfl | grind)
  · show cv tr tt s s2 = 1 → cv tr tt s s1 = 1
    intro h; exact cv_one_iff.mpr (f2 (cv_one_iff.mp h))
  · show cv tr tt s cand = cv tr tt s valid * cv tr tt s cok
    rcases bva with ⟨a1, c1⟩ | ⟨a1, c1⟩ <;> rcases bco with ⟨a2, c2⟩ | ⟨a2, c2⟩ <;> rw [a1, a2] <;>
      exact cv_of_eq (by unfold P; omega) (by rw [f3, c1, c2]; first | rfl | grind)
  · show cv tr tt s kind = 0 → cv tr tt s s1 = 1 → cv tr tt s cand = 1
    intro h1 h2; exact cv_one_iff.mpr (f4 (cv_zero_iff.mp h1) (cv_one_iff.mp h2))
  · show cv tr tt s kind = 1 → cv tr tt s s1 = 1 ∧ cv tr tt s s2 = 0
    intro h; have := f5 (cv_one_iff.mp h); exact ⟨cv_one_iff.mpr this.1, cv_zero_iff.mpr this.2⟩
  · show cv tr tt s fW = if cv tr tt s kind = 1 then 1 else cv tr tt s cand
    rcases bk with ⟨a, c⟩ | ⟨a, c⟩ <;> rw [c] at f6 <;> simp only [a, c, fp_zero_ne_one, ite_true, ite_false,
      show ¬ (0 = 1) by omega] at f6 ⊢
    · unfold cv; rw [f6]
    · exact cv_of_eq (by unfold P; omega) f6
  · show cv tr tt s fK = if cv tr tt s kind = 1 then 0 else cv tr tt s s1
    rcases bk with ⟨a, c⟩ | ⟨a, c⟩ <;> rw [c] at f7 <;> simp only [a, c, fp_zero_ne_one, ite_true, ite_false,
      show ¬ (0 = 1) by omega] at f7 ⊢
    · unfold cv; rw [f7]; try grind
    · exact cv_of_eq (by unfold P; omega) (by rw [f7]; rfl)
  · show cv tr tt s wr = if cv tr tt s kind = 1 then 1 else cv tr tt s okP * (1 - cv tr tt s tov)
    rcases bk with ⟨a, c⟩ | ⟨a, c⟩ <;> rw [c] at f8 <;> simp only [a, c, fp_zero_ne_one, ite_true, ite_false,
      show ¬ (0 = 1) by omega] at f8 ⊢
    · rcases bok with ⟨a1, c1⟩ | ⟨a1, c1⟩ <;> rcases btv with ⟨a2, c2⟩ | ⟨a2, c2⟩ <;> rw [a1, a2] <;>
        exact cv_of_eq (by unfold P; omega) (by rw [f8, c1, c2]; first | rfl | grind)
    · exact cv_of_eq (by unfold P; omega) (by rw [f8]; rfl)
  · intro j hj
    obtain ⟨l1, l2, l3, l4, l5⟩ := laneFlags hL hop j hj
    rw [lane_txOf s j hj]
    have hrj : s + j < tr.height tt := by omega
    refine ⟨?_, fun h8 => cv_zero_iff.mpr (l3 h8), fun hw => ?_, fun hw => ?_⟩
    · show Fp.ofNat (cv tr tt (s + j) g) = Fp.ofNat (16 * cv tr tt s op + j)
      rw [ofNat_cv, l1]; rfl
    · have hw' := cv_zero_iff.mp hw
      rw [hw'] at l4 l5
      refine ⟨?_, ?_⟩
      · show cv tr tt (s + j) mo = cv tr tt (s + j) amt
        unfold cv; rw [l4]; grind
      · show cv tr tt (s + j) nk = cv tr tt (s + j) kn
        unfold cv; rw [l5]; grind
    · have hw' := cv_one_iff.mp hw
      refine ⟨?_, ?_⟩
      · show cv tr tt (s + j) nk = cv tr tt (s + j) xN
        rw [hw'] at l5; unfold cv; rw [l5]; grind
      · show cv tr tt (s + j) mo < 256
        rw [mo_rC hL hop hw' j hj]; exact bv_lt hL hrj rCb_bool
  · intro h
    obtain ⟨d, hd, e⟩ := (opTimes hL hop).1 (cv_one_iff.mp h)
    refine ⟨d, hd, ?_⟩
    show Fp.ofNat (cv tr tt s tpA + d) = Fp.ofNat (cv tr tt s op)
    rw [← ofNat_add', ofNat_cv, ofNat_cv]; exact e
  · intro h
    obtain ⟨d, hd, e⟩ := (opTimes hL hop).2 (cv_one_iff.mp h)
    refine ⟨d, hd, ?_⟩
    show Fp.ofNat (cv tr tt s tpK + d) = Fp.ofNat (cv tr tt s op)
    rw [← ofNat_add', ofNat_cv, ofNat_cv]; exact e
  · intro hbytes
    have hb : InBytes tr tt s := by
      refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
        fun j hj => ?_, fun j hj => ?_⟩ <;>
      · have := hbytes j hj; rw [lane_txOf s j hj] at this
        simp only [laneOf] at this; omega
    refine ⟨fun hk => ?_, fun hk => ?_⟩ <;> simp only [val_txOf, laneOf]
    · have hk' := cv_zero_iff.mp hk
      obtain ⟨ad, ac⟩ := arith_debit hL hop hb hk'
      refine ⟨by rw [two128_eq]; exact ad, fun hw => ?_⟩
      have hwc := cv_one_iff.mp hw
      rw [f8, hk'] at hwc
      simp only [fp_zero_ne_one, ite_false] at hwc
      have hok : cv tr tt s okP = 1 := by
        rcases bok with ⟨a1, c1⟩ | ⟨a1, c1⟩
        · rw [c1] at hwc; exact absurd (by grind : (0 : Fp) = 1) fp_zero_ne_one
        · exact a1
      rw [RcptProof.sumL_congr _ (fun j => bv tr tt (s + j) rCb) 16
        (fun j hj => mo_rC hL hop (cv_one_iff.mp hw) j hj)]
      exact write_debit hL hop hb hk' (ac hok)
    · have hk' := cv_one_iff.mp hk
      have hw : tr.cell tt s wr = 1 := by rw [f8, hk']; simp
      rw [RcptProof.sumL_congr _ (fun j => bv tr tt (s + j) rCb) 16 (fun j hj => mo_rC hL hop hw j hj)]
      obtain ⟨c1, c2, c3, c4⟩ := arith_credit hL hop hb hk'
      exact ⟨c1, c2, by rw [two128_eq]; exact c3, c4⟩
  · refine ⟨cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _, fun j hj => ?_⟩
    rw [lane_txOf s j hj]
    exact ⟨cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _,
      cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _⟩

end

end ZkFormal.NearV3.D1.TxProof
