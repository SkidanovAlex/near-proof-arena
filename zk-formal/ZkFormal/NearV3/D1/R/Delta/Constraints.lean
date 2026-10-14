import ZkFormal.NearV3.D1.R.Base

/-!
# `ZkFormal.NearV3.D1.R.Delta.Constraints` — the replaced constraints of `rcptV3D1`, evaluated

Lane `v3-d1-phase2`, item V4.  The four constraints `rcptV3D1` replaces (plan §7, step 3),
each read off one row of a `LocalD1` trace (`hL.ext`: the extension is bytes):

* `tok_first`: `tok_i = TOK0_i` on the first row (`Delta/Tok`);
* `o2_first`: `o2 = O0` on the first row (`Delta/Body`);
* `count_last`: `lastR · (r + rowE + M0 − PH_N) = 0` (`Delta/Count`);
* `age_row`: `DEP · fs · (r + T0 − tprev − bits(xb52…65)) = 0` (`Delta/Age14`).

The two replaced interactions (`MEM` time, `MPOS` position) are not constraints; they are
handled at the traffic level (`Delta/Traffic`).
-/

namespace ZkFormal.NearV3.D1.RcptD1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3 ZkFormal.NearV3.RcptV3
open ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.RcptSkeleton

theorem repl_tok : ∀ i, i < 16 →
    replC' (.mul .isFirst (c (tok i))) = .mul .isFirst (sub (c (tok i)) (.pub (E_TOK0 + i))) := by
  decide

theorem repl_o2 : replC' (.mul .isFirst (sub (c o2) (k 8))) = .mul .isFirst (sub (c o2) o0E) := rfl

theorem repl_count : replC' (.mul (c lastR) (sub (.add (c r) rowE) nPubE)) =
    .mul (c lastR) (sub (sum [c r, rowE, m0E]) nPubE) := rfl

theorem repl_age : replC' (mul3 dp (c fs) (sub (sub (c r) (c tprev)) (bitsX 53 13))) =
    mul3 dp (c fs) (sub (sub (.add (c r) t0E) (c tprev)) (bitsX 52 14)) := rfl

variable {tr : Trace Fp} {t : Nat} {pub : List Fp} (hL : LocalD1 tr t pub)
include hL

theorem tok_first (h0 : 0 < tr.height t) {i : Nat} (hi : i < 16) :
    tr.cell t 0 (tok i) = ((pubNat pub (E_TOK0 + i) : Nat) : Fp) := by
  have hm : Expr.mul .isFirst (c (tok i)) ∈ cRegs := by
    unfold cRegs
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))))
  have h := hL.constr 0 h0 _ (memRepl (e := .mul .isFirst (c (tok i))) (by
    unfold receiptArithmeticCandidate; simp [hm]))
  rw [repl_tok i hi] at h
  simp only [eval_mul, eval_isFirst, eval_sub, eval_c, eval_pub, ite_true] at h
  rw [ZkFormal.Near.RcptProof.pub_eq_cast] at h
  grind

theorem o2_first (h0 : 0 < tr.height t) : tr.cell t 0 o2 = ((o0V pub : Nat) : Fp) := by
  have hm : Expr.mul .isFirst (sub (c o2) (k 8)) ∈ cStates := by simp [cStates]
  have h := hL.constr 0 h0 _ (memRepl (e := .mul .isFirst (sub (c o2) (k 8))) (by
    unfold receiptArithmeticCandidate; simp [hm]))
  rw [repl_o2] at h
  simp only [eval_mul, eval_isFirst, eval_sub, eval_c, ite_true, o0E_eval hL.ext.1] at h
  grind

theorem count_last {q : Nat} (hq : q < tr.height t) :
    tr.cell t q lastR * (tr.cell t q r + rowE.eval tr t q pub + ((m0V pub : Nat) : Fp) -
      nPubE.eval tr t q pub) = 0 := by
  have hm : Expr.mul (c lastR) (sub (.add (c r) rowE) nPubE) ∈ cEnd := by simp [cEnd]
  have h := hL.constr q hq _ (memRepl (e := .mul (c lastR) (sub (.add (c r) rowE) nPubE)) (by
    unfold receiptArithmeticCandidate; simp [hm]))
  rw [repl_count] at h
  simp only [eval_mul, eval_sub, eval_c, eval_sum_cons, eval_sum_nil, m0E_eval hL.ext.1] at h
  rw [← h]; grind

theorem age_row {q : Nat} (hq : q < tr.height t) :
    tr.cell t q sDEP * tr.cell t q fs * (tr.cell t q r + ((t0V pub : Nat) : Fp) - tr.cell t q tprev -
      (bitsX 52 14).eval tr t q pub) = 0 := by
  have hm : mul3 dp (c fs) (sub (sub (c r) (c tprev)) (bitsX 53 13)) ∈ depositAgeConstraints := by
    simp [depositAgeConstraints, depositConstraintsWith]
  have h := hL.constr q hq _ (memRepl (e := mul3 dp (c fs) (sub (sub (c r) (c tprev)) (bitsX 53 13))) (by
    unfold receiptArithmeticCandidate; simp [hm]))
  rw [repl_age] at h
  simp only [dp, eval_mul3, eval_sub, eval_add, eval_c, t0E_eval hL.ext.1] at h
  exact h

end ZkFormal.NearV3.D1.RcptD1
