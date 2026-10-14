import ZkFormal.NearV3.D1.Extract.Tx.Verdict

/-!
# `ZkFormal.NearV3.D1.Extract.Tx.Flags` — the op flags, gates, written values and memory times
-/

namespace ZkFormal.NearV3.D1.TxProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.TxV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem fmem {e : Expr} (h : e ∈ cFlags) : e ∈ TxV3.table.constraints := mem_flags h

theorem lb_bool : ∀ b, b < 4 → lb b ∈ boolCols := by
  intro b hb; simp [boolCols, lb, hb]
theorem tb_bool : ∀ b, b < 14 → tb b ∈ boolCols := by
  intro b hb; simp [boolCols, tb, hb]

section
variable (hL : TableLocal TxV3.table tr tt pub)
include hL

/-- The op-level flags, on the op's first row. -/
theorem opFlags {s : Nat} (hop : OpAt tr tt s) :
    tr.cell tt s stage = tr.cell tt s s1 + tr.cell tt s s2 ∧
    (tr.cell tt s s2 = 1 → tr.cell tt s s1 = 1) ∧
    tr.cell tt s cand = tr.cell tt s valid * tr.cell tt s cok ∧
    (tr.cell tt s kind = 0 → tr.cell tt s s1 = 1 → tr.cell tt s cand = 1) ∧
    (tr.cell tt s kind = 1 → tr.cell tt s s1 = 1 ∧ tr.cell tt s s2 = 0) ∧
    tr.cell tt s fW = (if tr.cell tt s kind = 1 then 1 else tr.cell tt s cand) ∧
    tr.cell tt s fK = (if tr.cell tt s kind = 1 then 0 else tr.cell tt s s1) ∧
    tr.cell tt s wr = (if tr.cell tt s kind = 1 then 1 else tr.cell tt s okP * (1 - tr.cell tt s tov)) := by
  have hH := hop.h
  have hr : s < tr.height tt := by omega
  have ha := hop.act 0 (by omega); have hlf := hop.lf 0 (by omega)
  simp only [Nat.add_zero, ite_true] at ha hlf
  have f1 := con hL hr (fmem (e := .mul (c act) (sub (c stage) (.add (c s1) (c s2)))) (by simp [cFlags]))
  have f2 := con hL hr (fmem (e := .mul (c s2) (not (c s1))) (by simp [cFlags]))
  have f4 := con hL hr (fmem (e := .mul (c act) (sub (c cand) (.mul (c valid) (c cok)))) (by simp [cFlags]))
  have f5 := con hL hr (fmem (e := mul3 (not (c kind)) (c s1) (not (c cand))) (by simp [cFlags]))
  have f6 := con hL hr (fmem (e := .mul (c kind) (not (c s1))) (by simp [cFlags]))
  have f7 := con hL hr (fmem (e := .mul (c kind) (c s2)) (by simp [cFlags]))
  have f9 := con hL hr (fmem (e := .mul (c act) (sub (c gW) (.add (c kind) (.mul (not (c kind)) (c cand)))))
    (by simp [cFlags]))
  have f10 := con hL hr (fmem (e := sub (c gK) (.mul (not (c kind)) (c s1))) (by simp [cFlags]))
  have f12 := con hL hr (fmem (e := sub (c fW) (.mul (c lf) (c gW))) (by simp [cFlags]))
  have f13 := con hL hr (fmem (e := sub (c fK) (.mul (c lf) (c gK))) (by simp [cFlags]))
  have f14 := con hL hr (fmem (e := .mul (c act) (sub (c wr) (.add (c kind)
    (mul3 (not (c kind)) (c okP) (not (c tov)))))) (by simp [cFlags]))
  simp only [eval_mul, eval_mul3, eval_sub, eval_add, eval_c, eval_not, ha, hlf] at f1 f2 f4 f5 f6 f7 f9 f10 f12 f13 f14
  have bk := isBool hL hr (x := kind) (by simp [boolCols])
  refine ⟨by grind, fun h => by rw [h] at f2; grind, by grind, fun h1 h2 => by rw [h1, h2] at f5; grind,
    fun h => ?_, ?_, ?_, ?_⟩
  · rw [h] at f6 f7; exact ⟨by grind, by grind⟩
  · rcases bk with h | h <;> simp only [h, fp_zero_ne_one, ite_true, ite_false] <;> grind
  · rcases bk with h | h <;> simp only [h, fp_zero_ne_one, ite_true, ite_false] <;> grind
  · rcases bk with h | h <;> simp only [h, fp_zero_ne_one, ite_true, ite_false] <;> grind

/-- Lane facts: `g`, the `AKMEM` gate, the written values. -/
theorem laneFlags {s : Nat} (hop : OpAt tr tt s) (j : Nat) (hj : j < 16) :
    tr.cell tt (s + j) g = ((16 * cv tr tt s op + j : Nat) : Fp) ∧
    tr.cell tt (s + j) gA = (if j < 8 then tr.cell tt s s2 else 0) ∧
    (8 ≤ j → tr.cell tt (s + j) kn = 0) ∧
    tr.cell tt (s + j) mo = tr.cell tt (s + j) amt + tr.cell tt s wr *
      (((bv tr tt (s + j) rCb : Nat) : Fp) - tr.cell tt (s + j) amt) ∧
    tr.cell tt (s + j) nk = tr.cell tt (s + j) kn + tr.cell tt s wr *
      (tr.cell tt (s + j) xN - tr.cell tt (s + j) kn) := by
  have hH := hop.h
  have hr : s + j < tr.height tt := by omega
  have ha := hop.act j hj
  have hla := hop.lane j hj
  have hc := fun x (hx : x ∈ opConst) => hop.const j hj x hx
  have eop := hc op (by simp [opConst]); have e2 := hc s2 (by simp [opConst])
  have ew := hc wr (by simp [opConst])
  have f0 := con hL hr (mem_shapeL (e := .mul (c act) (sub (c g) (.add (smul LANES (c op)) (c lane))))
    (by simp))
  have fl := con hL hr (mem_shapeL (e := sub (c lane) laneE) (by simp))
  have f11 := con hL hr (fmem (e := sub (c gA) (.mul (c s2) lo8)) (by simp [cFlags]))
  have f15 := con hL hr (fmem (e := .mul (c act) (sub (c mo) (.add (c amt) (.mul (c wr) (sub rC (c amt))))))
    (by simp [cFlags]))
  have f16 := con hL hr (fmem (e := .mul (c act) (sub (c nk) (.add (c kn) (.mul (c wr) (sub (c xN) (c kn))))))
    (by simp [cFlags]))
  have f17 := con hL hr (fmem (e := .mul (c (lb 3)) (c kn)) (by simp [cFlags]))
  simp only [eval_mul, eval_sub, eval_add, eval_c, eval_smul, eval_not, ha, eop, e2, ew, hla, rC, byteC,
    eval_byte hL hr rCb_bool, lo8, LANES] at f0 f11 f15 f16 f17
  simp only [laneE, eval_sub, eval_c, hla, eval_byte hL hr lb_bool] at fl
  -- the lane bits: `lb₃ = [j ≥ 8]`
  have hlv : bv tr tt (s + j) lb 4 = j := by
    have hlt := bv_lt hL hr lb_bool (len := 4)
    exact (natEq (by unfold P; omega) (by unfold P; omega) (by grind)).symm
  have hb3 : tr.cell tt (s + j) (lb 3) = if 8 ≤ j then 1 else 0 := by
    have b0 := cv_bool' hL hr (lb_bool 0 (by omega)); have b1 := cv_bool' hL hr (lb_bool 1 (by omega))
    have b2 := cv_bool' hL hr (lb_bool 2 (by omega)); have b3 := cv_bool' hL hr (lb_bool 3 (by omega))
    simp only [bv, bitsVal, Nat.zero_add] at hlv
    rcases isBool hL hr (lb_bool 3 (by omega)) with h | h
    · have : cv tr tt (s + j) (lb 3) = 0 := cv_zero_iff.mpr h
      rw [if_neg (by omega)]; exact h
    · have : cv tr tt (s + j) (lb 3) = 1 := cv_one_iff.mpr h
      rw [if_pos (by omega)]; exact h
  refine ⟨?_, ?_, fun h8 => ?_, by grind, by grind⟩
  · rw [natCast_add, natCast_mul, ← cell_eq_cast]; grind
  · rw [hb3] at f11
    by_cases h8 : j < 8
    · rw [if_pos h8]; rw [if_neg (by omega)] at f11; grind
    · rw [if_neg h8]; rw [if_pos (by omega)] at f11; grind
  · rw [hb3, if_pos h8] at f17; grind

/-- Memory times: `tp + d = op` with `d < 2¹⁴`. -/
theorem opTimes {s : Nat} (hop : OpAt tr tt s) :
    (tr.cell tt s s1 = 1 → ∃ d, d < 2 ^ 14 ∧ tr.cell tt s tpA + ((d : Nat) : Fp) = tr.cell tt s op) ∧
    (tr.cell tt s s2 = 1 → ∃ d, d < 2 ^ 14 ∧ tr.cell tt s tpK + ((d : Nat) : Fp) = tr.cell tt s op) := by
  have hH := hop.h
  have hr0 : s < tr.height tt := by omega
  have hr1 : s + 1 < tr.height tt := by omega
  have hlf := hop.lf 0 (by omega); have hl1 := hop.l1 1 (by omega)
  simp only [Nat.add_zero, ite_true] at hlf hl1
  have hc := fun x (hx : x ∈ opConst) => hop.const 1 (by omega) x hx
  have eop := hc op (by simp [opConst]); have e2 := hc s2 (by simp [opConst])
  have etk := hc tpK (by simp [opConst])
  have f18 := con hL hr0 (fmem (e := mul3 (c lf) (c s1) (sub (sub (c op) (c tpA)) tbE)) (by simp [cFlags]))
  have f19 := con hL hr1 (fmem (e := mul3 (c l1) (c s2) (sub (sub (c op) (c tpK)) tbE)) (by simp [cFlags]))
  simp only [tbE, eval_mul3, eval_sub, eval_c, hlf, hl1, eop, e2, etk,
    eval_byte hL hr0 tb_bool, eval_byte hL hr1 tb_bool] at f18 f19
  refine ⟨fun h => ⟨bv tr tt s tb 14, bv_lt hL hr0 tb_bool, ?_⟩,
    fun h => ⟨bv tr tt (s + 1) tb 14, bv_lt hL hr1 tb_bool, ?_⟩⟩
  · rw [h] at f18; grind
  · rw [h] at f19; grind

end

end ZkFormal.NearV3.D1.TxProof
