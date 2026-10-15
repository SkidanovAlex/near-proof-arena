import ZkFormal.NearV3.D1.Extract.Tx.ChainZ
import ZkFormal.NearV3.D1.Extract.Tx.Arith

/-!
# `ZkFormal.NearV3.D1.Extract.Tx.Verdict` — the verdict constraints of `txV3` (lane 15)

The products `hN`, `hS`, `h1 … h3`, `okC` of boolean cells, and the debit / credit conditions on
the last lane, as statements about which cells are `0` / `1`.
-/

namespace ZkFormal.NearV3.D1.TxProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.TxV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-! ## Boolean field algebra -/

def IsB (a : Fp) : Prop := a = 0 ∨ a = 1

theorem isB_mul {a b : Fp} (ha : IsB a) (hb : IsB b) : IsB (a * b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> unfold IsB <;> grind

theorem mul_eq_one {a b : Fp} (ha : IsB a) (hb : IsB b) : a * b = 1 ↔ a = 1 ∧ b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [fp_zero_ne_one, fp_one_ne_zero] <;> grind

theorem isB_not {a : Fp} (ha : IsB a) : IsB (1 - a) := by
  rcases ha with rfl | rfl <;> unfold IsB <;> grind

theorem not_eq_one {a : Fp} (ha : IsB a) : 1 - a = 1 ↔ a = 0 := by
  rcases ha with rfl | rfl <;> simp [fp_zero_ne_one, fp_one_ne_zero] <;> grind

theorem cv_one_iff {r x : Nat} : cv tr tt r x = 1 ↔ tr.cell tt r x = 1 := by
  constructor
  · intro h; rw [cell_eq_cast, h]; rfl
  · intro h; unfold cv; rw [h]; rfl

theorem cv_zero_iff {r x : Nat} : cv tr tt r x = 0 ↔ tr.cell tt r x = 0 := by
  constructor
  · intro h; rw [cell_eq_cast, h]; rfl
  · intro h; unfold cv; rw [h]; rfl

theorem vmem {e : Expr} (h : e ∈ cVerdict) : e ∈ TxV3.table.constraints := mem_verdict h

section
variable (hL : TableLocal TxV3.table tr tt pub)
include hL

theorem cellB {r : Nat} (hr : r < tr.height tt) {x : Nat} (hx : x ∈ boolCols) : IsB (tr.cell tt r x) :=
  isBool hL hr hx

/-- **Debit verdict** (`kind = 0`): the public `okP` is `1` exactly when every factor is. -/
theorem verdict_debit {s : Nat} (hop : OpAt tr tt s) (hk : tr.cell tt s kind = 0) :
    tr.cell tt s okP = 1 ↔
      (tr.cell tt s s2 = 1 ∧ tr.cell tt s fa = 1 ∧ tr.cell tt (s + 15) boN = 0 ∧
        (tr.cell tt s strict = 0 ∨ tr.cell tt (s + 15) zN = 1) ∧ tr.cell tt (s + 15) boB = 0 ∧
        tr.cell tt (s + 15) coC = 0 ∧ tr.cell tt (s + 15) coT = 0 ∧
        ¬ (tr.cell tt (s + 15) boQ = 1 ∧ tr.cell tt (s + 15) boS = 1)) := by
  have hH := hop.h
  have hr : s + 15 < tr.height tt := by omega
  have hll := hop.ll 15 (by omega); simp only [ite_true] at hll
  have hc := fun x (hx : x ∈ opConst) => hop.const 15 (by omega) x hx
  have ek := hc kind (by simp [opConst]); have es := hc strict (by simp [opConst])
  have eo := hc okP (by simp [opConst]); have e2 := hc s2 (by simp [opConst])
  have ef := hc fa (by simp [opConst])
  have v1 := con hL hr (vmem (e := lastE (sub (c hN) (.mul (not (c boN))
    (.add (not (c strict)) (.mul (c strict) (c zN)))))) (by simp [cVerdict]))
  have v2 := con hL hr (vmem (e := lastE (sub (c hS) (.mul (not (c coT)) (not (.mul (c boQ) (c boS))))))
    (by simp [cVerdict]))
  have v3 := con hL hr (vmem (e := lastE (sub (c h1) (.mul (c s2) (c fa)))) (by simp [cVerdict]))
  have v4 := con hL hr (vmem (e := lastE (sub (c h2) (.mul (c h1) (c hN)))) (by simp [cVerdict]))
  have v5 := con hL hr (vmem (e := lastE (sub (c h3) (mul3 (c h2) (not (c boB)) (not (c coC)))))
    (by simp [cVerdict]))
  have v6 := con hL hr (vmem (e := lastE (sub (c okC) (.mul (c h3) (c hS)))) (by simp [cVerdict]))
  have v7 := con hL hr (vmem (e := .mul (lastE (not (c kind))) (sub (c okP) (c okC))) (by simp [cVerdict]))
  simp only [lastE, eval_mul, eval_mul3, eval_sub, eval_add, eval_c, eval_not, hll, ek, es, eo, e2, ef,
    hk] at v1 v2 v3 v4 v5 v6 v7
  have bB := fun x (hx : x ∈ boolCols) => cellB hL hr hx
  have b2 := cellB hL (r := s) (by omega) (x := s2) (by simp [boolCols])
  have bfa := cellB hL (r := s) (by omega) (x := fa) (by simp [boolCols])
  have bst := cellB hL (r := s) (by omega) (x := strict) (by simp [boolCols])
  have bN := bB boN (by simp [boolCols]); have bz := bB zN (by simp [boolCols])
  have bBo := bB boB (by simp [boolCols]); have bC := bB coC (by simp [boolCols])
  have bT := bB coT (by simp [boolCols]); have bQ := bB boQ (by simp [boolCols])
  have bS := bB boS (by simp [boolCols])
  have hhN : tr.cell tt (s + 15) hN = (1 - tr.cell tt (s + 15) boN) *
      ((1 - tr.cell tt s strict) + tr.cell tt s strict * tr.cell tt (s + 15) zN) := by grind
  have hhS : tr.cell tt (s + 15) hS = (1 - tr.cell tt (s + 15) coT) *
      (1 - tr.cell tt (s + 15) boQ * tr.cell tt (s + 15) boS) := by grind
  have hok : tr.cell tt s okP = tr.cell tt s s2 * tr.cell tt s fa * tr.cell tt (s + 15) hN *
      (1 - tr.cell tt (s + 15) boB) * (1 - tr.cell tt (s + 15) coC) * tr.cell tt (s + 15) hS := by grind
  have bsz : IsB ((1 - tr.cell tt s strict) + tr.cell tt s strict * tr.cell tt (s + 15) zN) := by
    rcases bst with h | h <;> rw [h] <;> rcases bz with h' | h' <;> rw [h'] <;> unfold IsB <;> grind
  have sz : (1 - tr.cell tt s strict) + tr.cell tt s strict * tr.cell tt (s + 15) zN = 1 ↔
      (tr.cell tt s strict = 0 ∨ tr.cell tt (s + 15) zN = 1) := by
    rcases bst with h | h <;> rw [h] <;> rcases bz with h' | h' <;> rw [h'] <;>
      simp [fp_one_ne_zero, fp_zero_ne_one] <;> grind
  have bqs := isB_mul bQ bS
  have bhN : IsB (tr.cell tt (s + 15) hN) := by rw [hhN]; exact isB_mul (isB_not bN) bsz
  have bhS : IsB (tr.cell tt (s + 15) hS) := by rw [hhS]; exact isB_mul (isB_not bT) (isB_not bqs)
  rw [hok, mul_eq_one (isB_mul (isB_mul (isB_mul (isB_mul b2 bfa) bhN) (isB_not bBo)) (isB_not bC)) bhS,
    mul_eq_one (isB_mul (isB_mul (isB_mul b2 bfa) bhN) (isB_not bBo)) (isB_not bC),
    mul_eq_one (isB_mul (isB_mul b2 bfa) bhN) (isB_not bBo), mul_eq_one (isB_mul b2 bfa) bhN,
    mul_eq_one b2 bfa, hhN, mul_eq_one (isB_not bN) bsz, hhS, mul_eq_one (isB_not bT) (isB_not bqs),
    not_eq_one bN, sz, not_eq_one bBo, not_eq_one bC, not_eq_one bT, not_eq_one bqs,
    show (tr.cell tt (s + 15) boQ * tr.cell tt (s + 15) boS = 0 ↔
      ¬ (tr.cell tt (s + 15) boQ = 1 ∧ tr.cell tt (s + 15) boS = 1)) from by
        rw [← mul_eq_one bQ bS]; rcases bqs with h | h <;> rw [h] <;> simp [fp_zero_ne_one, fp_one_ne_zero]]
  simp only [and_assoc]

/-- **Credit conditions** (`kind = 1`). -/
theorem verdict_credit {s : Nat} (hop : OpAt tr tt s) (hk : tr.cell tt s kind = 1) :
    tr.cell tt (s + 15) coC = 0 ∧ tr.cell tt (s + 15) coT = 0 ∧ tr.cell tt (s + 15) msum ≠ 0 ∧
      ¬ (tr.cell tt (s + 15) boQ = 1 ∧ tr.cell tt (s + 15) boS = 1) := by
  have hH := hop.h
  have hr : s + 15 < tr.height tt := by omega
  have hll := hop.ll 15 (by omega); simp only [ite_true] at hll
  have ek := hop.const 15 (by omega) kind (by simp [opConst])
  have v8 := con hL hr (vmem (e := lastE (.mul (c kind) (c coC))) (by simp [cVerdict]))
  have v9 := con hL hr (vmem (e := lastE (.mul (c kind) (c coT))) (by simp [cVerdict]))
  have v10 := con hL hr (vmem (e := lastE (.mul (c kind) (sub (.mul (c msum) (c minv)) (k 1))))
    (by simp [cVerdict]))
  have v11 := con hL hr (vmem (e := lastE (mul3 (c kind) (c boQ) (c boS))) (by simp [cVerdict]))
  simp only [lastE, eval_mul, eval_mul3, eval_sub, eval_c, eval_k, hll, ek, hk] at v8 v9 v10 v11
  refine ⟨by grind, by grind, fun h => ?_, fun ⟨h1, h2⟩ => ?_⟩
  · rw [h] at v10
    have : ((1 : Nat) : Fp) = 0 := by grind
    exact fp_one_ne_zero this
  · rw [h1, h2] at v11; exact fp_one_ne_zero (by grind)

end

end ZkFormal.NearV3.D1.TxProof
