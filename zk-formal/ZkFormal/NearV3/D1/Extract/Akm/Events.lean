import ZkFormal.NearV3.D1.Extract.Akm.Utf8Body

/-!
# `ZkFormal.NearV3.D1.Extract.Akm.Events` — the events of `akmV3` (string done, method done, accepting
end, method count) and the state transitions between fields
-/

namespace ZkFormal.NearV3.D1.AkmProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.AkmV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem ev_mem {e : Expr} (h : e ∈ cEvents) : e ∈ AkmV3.table.constraints := mem_events h

section
variable (hL : TableLocal AkmV3.table tr tt pub)
include hL

theorem ev {r : Nat} (hr : r < tr.height tt) {e : Expr} (h : e ∈ cEvents) : e.eval tr tt r pub = 0 :=
  con hL hr (ev_mem h)

theorem sd_eq {r : Nat} (hr : r < tr.height tt) :
    tr.cell tt r sd = tr.cell tt r sL * tr.cell tt r fe * tr.cell tt r zA + tr.cell tt r sS * tr.cell tt r fe := by
  have := ev hL hr (e := sub (c sd) (.add (mul3 (c sL) (c fe) (c zA)) (.mul (c sS) (c fe)))) (by simp [cEvents])
  simp only [eval_sub, eval_add, eval_mul3, eval_mul, eval_c] at this; grind

theorem md_eq {r : Nat} (hr : r < tr.height tt) : tr.cell tt r md = tr.cell tt r sd * tr.cell tt r mth := by
  have := ev hL hr (e := sub (c md) (.mul (c sd) (c mth))) (by simp [cEvents])
  simp only [eval_sub, eval_mul, eval_c] at this; grind

theorem endOK_eq {r : Nat} (hr : r < tr.height tt) : tr.cell tt r endOK =
    tr.cell tt r sT * tr.cell tt r (t 1) + tr.cell tt r sG * tr.cell tt r fe * tr.cell tt r (t 3) +
    (tr.cell tt r sC * tr.cell tt r fe * tr.cell tt r zA + (tr.cell tt r md * tr.cell tt r zV + 0)) := by
  have := ev hL hr (e := sub (c endOK) (sum [ .mul (c sT) (c (t 1)), mul3 (c sG) (c fe) (c (t 3)),
    mul3 (c sC) (c fe) (c zA), .mul (c md) (c zV) ])) (by simp [cEvents])
  simp only [eval_sub, eval_sum_cons, eval_sum_nil, eval_mul3, eval_mul, eval_c] at this; grind

theorem eS_eq {r : Nat} (hr : r < tr.height tt) :
    tr.cell tt r eS = tr.cell tt r sL * tr.cell tt r fgo * (1 - tr.cell tt r zA) := by
  have := ev hL hr (e := sub (c eS) (mul3 (c sL) (c fgo) (not (c zA)))) (by simp [cEvents])
  simp only [eval_sub, eval_mul3, eval_not, eval_c] at this; grind

theorem eC_eq {r : Nat} (hr : r < tr.height tt) :
    tr.cell tt r eC = tr.cell tt r sC * tr.cell tt r fgo * (1 - tr.cell tt r zA) := by
  have := ev hL hr (e := sub (c eC) (mul3 (c sC) (c fgo) (not (c zA)))) (by simp [cEvents])
  simp only [eval_sub, eval_mul3, eval_not, eval_c] at this; grind

theorem eM_eq {r : Nat} (hr : r < tr.height tt) :
    tr.cell tt r eM = tr.cell tt r md * (1 - tr.cell tt r zV) := by
  have := ev hL hr (e := sub (c eM) (.mul (c md) (not (c zV)))) (by simp [cEvents])
  simp only [eval_sub, eval_mul, eval_not, eval_c] at this; grind

/-- The method counter. -/
theorem vc_step {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 1) (hl : tr.cell tt r al = 0) :
    tr.cell tt (r + 1) vc = tr.cell tt r vc - tr.cell tt r md +
      tr.cell tt r eC * (tr.cell tt r acc - tr.cell tt r vc) := by
  have := ev hL (by omega : r < _) (e := mul3 (c act) (not (c al)) (sub (n vc) (sum [c vc, .neg (c md),
    .mul (c eC) (sub (c acc) (c vc))]))) (by simp [cEvents])
  simp only [eval_sub, eval_mul3, eval_not, eval_c, eval_n, eval_sum_cons, eval_sum_nil, eval_neg, eval_mul,
    ha, hl, nxt hr] at this; grind

/-- `zV = [vc = 1]` on a method-done row. -/
theorem zV_iff {r : Nat} (hr : r < tr.height tt) (hm : tr.cell tt r md = 1) :
    (tr.cell tt r zV = 0 ∨ tr.cell tt r zV = 1) ∧ (tr.cell tt r zV = 1 ↔ tr.cell tt r vc = 1) := by
  have hb := isBool hL hr (x := zV) (by simp [boolCols])
  have e1 := ev hL hr (e := .mul (c md) (.mul (sub (c vc) (k 1)) (c zV))) (by simp [cEvents])
  have e2 := ev hL hr (e := .mul (c md) (sub (.mul (sub (c vc) (k 1)) (c invV)) (not (c zV)))) (by simp [cEvents])
  simp only [eval_mul, eval_sub, eval_c, eval_k, eval_not, hm] at e1 e2
  refine ⟨hb, fun h => ?_, fun h => ?_⟩
  · rw [h] at e1; grind
  · rw [h] at e2
    rcases hb with hb | hb
    · rw [hb] at e2; exact absurd (by grind) fp_zero_ne_one
    · exact hb

/-- A transition `g · (1 − n x) = 0` with `g = 1`: the next row is in state `x`. -/
theorem trans1 {r : Nat} (hr : r + 1 < tr.height tt) {g : Expr} {x : Nat}
    (hm : Expr.mul g (not (n x)) ∈ cEvents) (hg : g.eval tr tt r pub = 1) : tr.cell tt (r + 1) x = 1 := by
  have := ev hL (by omega : r < _) hm
  simp only [eval_mul, eval_not, eval_n, hg, nxt hr] at this; grind

/-- A transition `g · n x = 0` with `g = 1`: the next row has `x = 0`. -/
theorem trans0 {r : Nat} (hr : r + 1 < tr.height tt) {g : Expr} {x : Nat}
    (hm : Expr.mul g (n x) ∈ cEvents) (hg : g.eval tr tt r pub = 1) : tr.cell tt (r + 1) x = 0 := by
  have := ev hL (by omega : r < _) hm
  simp only [eval_mul, eval_n, hg, nxt hr] at this; grind

theorem trans3 {r : Nat} (hr : r + 1 < tr.height tt) {a b : Expr} {x : Nat}
    (hm : mul3 a b (not (n x)) ∈ cEvents) (ha : a.eval tr tt r pub = 1) (hb : b.eval tr tt r pub = 1) :
    tr.cell tt (r + 1) x = 1 := by
  have := ev hL (by omega : r < _) hm
  simp only [eval_mul3, eval_not, eval_n, ha, hb, nxt hr] at this; grind

theorem trans3z {r : Nat} (hr : r + 1 < tr.height tt) {a b : Expr} {x : Nat}
    (hm : mul3 a b (n x) ∈ cEvents) (ha : a.eval tr tt r pub = 1) (hb : b.eval tr tt r pub = 1) :
    tr.cell tt (r + 1) x = 0 := by
  have := ev hL (by omega : r < _) hm
  simp only [eval_mul3, eval_n, ha, hb, nxt hr] at this; grind

theorem transGo {r : Nat} (hr : r + 1 < tr.height tt) (hal : tr.cell tt r al = 0) {a b : Expr} {x : Nat}
    (hm : go (mul3 a b (not (n x))) ∈ cEvents) (ha : a.eval tr tt r pub = 1) (hb : b.eval tr tt r pub = 1) :
    tr.cell tt (r + 1) x = 1 := by
  have := ev hL (by omega : r < _) hm
  simp only [go, eval_mul, eval_mul3, eval_not, eval_n, eval_c, ha, hb, hal, nxt hr, Dsl.not, eval_sub, eval_k] at this; grind

theorem transGoz {r : Nat} (hr : r + 1 < tr.height tt) (hal : tr.cell tt r al = 0) {a b : Expr} {x : Nat}
    (hm : go (mul3 a b (n x)) ∈ cEvents) (ha : a.eval tr tt r pub = 1) (hb : b.eval tr tt r pub = 1) :
    tr.cell tt (r + 1) x = 0 := by
  have := ev hL (by omega : r < _) hm
  simp only [go, eval_mul, eval_mul3, eval_n, eval_c, ha, hb, hal, nxt hr, Dsl.not, eval_sub, eval_k] at this; grind

end

end ZkFormal.NearV3.D1.AkmProof
