import ZkFormal.NearV3.D1.Extract.Akm.Field
import ZkFormal.NearV3.D1.Extract.Akm.Utf8Abs

/-!
# `ZkFormal.NearV3.D1.Extract.Akm.Utf8Row` — the byte classes of a string-body row

On an `sS` row: exactly one class is set, and the class fixes the byte's range (`ClassOk`);
the second-byte flags constrain the next byte.
-/

namespace ZkFormal.NearV3.D1.AkmProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.AkmV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- The class of a row as a number (`0` ASCII … `4` 4-byte lead). -/
def clsOf (tr : Trace Fp) (tt r : Nat) : Nat :=
  if tr.cell tt r cC = 1 then 1 else if tr.cell tt r c2 = 1 then 2 else if tr.cell tt r c3 = 1 then 3
  else if tr.cell tt r c4 = 1 then 4 else 0

/-- Bit `i` of the row's byte. -/
abbrev bit (tr : Trace Fp) (tt r i : Nat) : Nat := cv tr tt r (bb i)

theorem bvA_bits (r : Nat) : bvA tr tt r = bit tr tt r 0 + 2 * bit tr tt r 1 + 4 * bit tr tt r 2 +
    8 * bit tr tt r 3 + 16 * bit tr tt r 4 + 32 * bit tr tt r 5 + 64 * bit tr tt r 6 + 128 * bit tr tt r 7 := by
  simp only [bvA, bitsVal, bit, Nat.zero_add]; omega

theorem cls_bool : ∀ x ∈ classes, x ∈ boolCols := by
  intro x hx; simp only [classes, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [boolCols, classes]

/-- `x · y = 0` with `x = 1` ⇒ `y = 0`, for a bit `y` read as a natural. -/
theorem bit_zero {r i : Nat} (h : tr.cell tt r (bb i) = 0) : bit tr tt r i = 0 := by
  unfold bit cv; rw [h]; rfl

theorem bit_one {r i : Nat} (h : tr.cell tt r (bb i) = 1) : bit tr tt r i = 1 := by
  unfold bit cv; rw [h]; rfl

theorem uc_mem {e : Expr} (h : e ∈ cUtf8) : e ∈ AkmV3.table.constraints := mem_utf8 h

section
variable (hL : TableLocal AkmV3.table tr tt pub)
include hL

theorem bit_le {r : Nat} (hr : r < tr.height tt) (i : Nat) (hi : i < 8) : bit tr tt r i ≤ 1 :=
  cv_bool (isBool hL hr (bb_bool i hi))

theorem cl_zero {r : Nat} (hr : r < tr.height tt) {x i : Nat} (hx : tr.cell tt r x = 1)
    (hm : Expr.mul (c x) (bt i) ∈ cUtf8) : tr.cell tt r (bb i) = 0 := by
  have := con hL hr (mem_utf8 hm); simp only [bt, eval_mul, eval_c, hx] at this; grind

theorem cl_one {r : Nat} (hr : r < tr.height tt) {x i : Nat} (hx : tr.cell tt r x = 1)
    (hm : Expr.mul (c x) (not (bt i)) ∈ cUtf8) : tr.cell tt r (bb i) = 1 := by
  have := con hL hr (mem_utf8 hm); simp only [bt, eval_mul, eval_c, eval_not, hx] at this; grind

/-- **The class of an `sS` row fixes the byte range.** -/
theorem classOk_row {r : Nat} (hr : r < tr.height tt) (hS : tr.cell tt r sS = 1) :
    ClassOk (clsOf tr tt r) (bvA tr tt r) := by
  have e0 := con hL hr (uc_mem (e := .mul (c sS) (sub (sum (classes.map c)) (k 1))) (by simp [cUtf8]))
  simp only [classes, List.map_cons, List.map_nil, eval_mul, eval_sub, eval_sum_cons, eval_sum_nil,
    eval_c, eval_k, hS] at e0
  have bc := fun x (hx : x ∈ classes) => isBool hL hr (cls_bool x hx)
  have bA := bc cA (by simp [classes]); have bC := bc cC (by simp [classes])
  have b2 := bc c2 (by simp [classes]); have b3 := bc c3 (by simp [classes])
  have b4 := bc c4 (by simp [classes])
  have bits := fun i (hi : i < 8) => isBool hL hr (bb_bool i hi)
  have hx := bvA_bits (tr := tr) (tt := tt) r
  have bl := fun i (hi : i < 8) => bit_le hL hr i hi
  have g := fun (e : Expr) (he : e ∈ cUtf8) => con hL hr (uc_mem he)
  have z : ∀ {a b : Fp}, a = 1 → a * b = 0 → b = 0 := fun ha h => by rw [ha] at h; grind
  have z' : ∀ {a b : Fp}, a = 1 → a * (1 - b) = 0 → b = 1 := fun ha h => by rw [ha] at h; grind
  unfold clsOf
  rcases bC with hC | hC
  · rw [if_neg (by rw [hC]; exact fp_zero_ne_one)]
    rcases b2 with h2 | h2
    · rw [if_neg (by rw [h2]; exact fp_zero_ne_one)]
      rcases b3 with h3 | h3
      · rw [if_neg (by rw [h3]; exact fp_zero_ne_one)]
        rcases b4 with h4 | h4
        · rw [if_neg (by rw [h4]; exact fp_zero_ne_one)]
          -- ASCII
          have hA : tr.cell tt r cA = 1 := by rw [hC, h2, h3, h4] at e0; grind
          have h7 := cl_zero hL hr (i := 7) hA (by simp [cUtf8])
          have := bit_zero h7
          have := bl 0 (by omega); have := bl 1 (by omega); have := bl 2 (by omega); have := bl 3 (by omega)
          have := bl 4 (by omega); have := bl 5 (by omega); have := bl 6 (by omega)
          left; exact ⟨rfl, by omega⟩
        · rw [if_pos h4]
          have h7 := cl_one hL hr (i := 7) h4 (by simp [cUtf8])
          have h6 := cl_one hL hr (i := 6) h4 (by simp [cUtf8])
          have h5 := cl_one hL hr (i := 5) h4 (by simp [cUtf8])
          have h4' := cl_one hL hr (i := 4) h4 (by simp [cUtf8])
          have h3' := cl_zero hL hr (i := 3) h4 (by simp [cUtf8])
          have h210 : tr.cell tt r (bb 2) * (tr.cell tt r (bb 1) + tr.cell tt r (bb 0)) = 0 := by
            have := g _ (show mul3 (c c4) (bt 2) (.add (bt 1) (bt 0)) ∈ cUtf8 by simp [cUtf8])
            simp only [bt, eval_mul3, eval_add, eval_c, h4] at this; grind
          have := bit_one h7; have := bit_one h6; have := bit_one h5; have := bit_one h4'
          have := bit_zero h3'
          have b2l := bl 2 (by omega); have b1l := bl 1 (by omega); have b0l := bl 0 (by omega)
          rcases bits 2 (by omega) with q2 | q2
          · have := bit_zero q2; right; right; right; right; exact ⟨rfl, by omega, by omega⟩
          · rw [q2] at h210
            have hs : tr.cell tt r (bb 1) + tr.cell tt r (bb 0) = 0 := by grind
            rcases bits 1 (by omega) with q1 | q1 <;> rcases bits 0 (by omega) with q0 | q0
            · have := bit_one q2; have := bit_zero q1; have := bit_zero q0
              right; right; right; right; exact ⟨rfl, by omega, by omega⟩
            all_goals (exfalso; rw [q1, q0] at hs; revert hs; decide)
      · rw [if_pos h3]
        have h7 := cl_one hL hr (i := 7) h3 (by simp [cUtf8])
        have h6 := cl_one hL hr (i := 6) h3 (by simp [cUtf8])
        have h5 := cl_one hL hr (i := 5) h3 (by simp [cUtf8])
        have h4' := cl_zero hL hr (i := 4) h3 (by simp [cUtf8])
        have := bit_one h7; have := bit_one h6; have := bit_one h5; have := bit_zero h4'
        have := bl 0 (by omega); have := bl 1 (by omega); have := bl 2 (by omega); have := bl 3 (by omega)
        right; right; right; left; exact ⟨rfl, by omega, by omega⟩
    · rw [if_pos h2]
      have h7 := cl_one hL hr (i := 7) h2 (by simp [cUtf8])
      have h6 := cl_one hL hr (i := 6) h2 (by simp [cUtf8])
      have h5 := cl_zero hL hr (i := 5) h2 (by simp [cUtf8])
      have hv := g _ (show Expr.mul (c c2) (sub (.mul v2E (c inv2)) (k 1)) ∈ cUtf8 by simp [cUtf8])
      simp only [v2E, eval_mul, eval_sub, eval_c, eval_k, h2] at hv
      rw [eval_bits tr tt r pub (fun x => bb (x + 1)) 0 4 (fun b hb => isBool hL hr (bb_bool _ (by omega)))] at hv
      have hv0 : bitsVal (fun b => cv tr tt r (bb (b + 1))) 0 4 ≠ 0 := by
        intro h0; rw [h0] at hv
        have : (0 : Fp) * tr.cell tt r inv2 = 1 := by
          rw [show ((0 : Nat) : Fp) = 0 from rfl] at hv; grind
        rw [Lean.Grind.Semiring.zero_mul] at this; exact fp_zero_ne_one this
      simp only [bitsVal, Nat.zero_add, Nat.reduceAdd] at hv0
      have := bit_one h7; have := bit_one h6; have := bit_zero h5
      have := bl 0 (by omega); have := bl 1 (by omega); have := bl 2 (by omega); have := bl 3 (by omega)
      have := bl 4 (by omega)
      right; right; left; exact ⟨rfl, by simp only [bit] at *; omega, by omega⟩
  · rw [if_pos hC]
    have h7 := cl_one hL hr (i := 7) hC (by simp [cUtf8])
    have h6 := cl_zero hL hr (i := 6) hC (by simp [cUtf8])
    have := bit_one h7; have := bit_zero h6
    have := bl 0 (by omega); have := bl 1 (by omega); have := bl 2 (by omega); have := bl 3 (by omega)
    have := bl 4 (by omega); have := bl 5 (by omega)
    right; left; exact ⟨rfl, by omega, by omega⟩

theorem cls_onehot {r : Nat} (hr : r < tr.height tt) (hS : tr.cell tt r sS = 1) :
    tr.cell tt r cA + tr.cell tt r cC + tr.cell tt r c2 + tr.cell tt r c3 + tr.cell tt r c4 = 1 := by
  have e0 := con hL hr (uc_mem (e := .mul (c sS) (sub (sum (classes.map c)) (k 1))) (by simp [cUtf8]))
  simp only [classes, List.map_cons, List.map_nil, eval_mul, eval_sub, eval_sum_cons, eval_sum_nil,
    eval_c, eval_k, hS] at e0
  grind

/-- The successor pending count of an `sS` row. -/
theorem ucn_row {r : Nat} (hr : r < tr.height tt) (hS : tr.cell tt r sS = 1) :
    tr.cell tt r ucn = ucnF (clsOf tr tt r) (tr.cell tt r uc) := by
  have e := con hL hr (uc_mem (e := .mul (c sS) (sub (c ucn) (sum [c c2, smul 2 (c c3), smul 3 (c c4),
    .mul (c cC) (sub (c uc) (k 1))]))) (by simp [cUtf8]))
  simp only [eval_mul, eval_sub, eval_sum_cons, eval_sum_nil, eval_c, eval_smul, eval_k, hS] at e
  have oh := cls_onehot hL hr hS
  have bc := fun x (hx : x ∈ classes) => isBool hL hr (cls_bool x hx)
  rcases bc cC (by simp [classes]) with hC | hC <;> rcases bc c2 (by simp [classes]) with h2 | h2 <;>
    rcases bc c3 (by simp [classes]) with h3 | h3 <;> rcases bc c4 (by simp [classes]) with h4 | h4 <;>
    rcases bc cA (by simp [classes]) with hA | hA <;>
    simp only [clsOf, ucnF, hC, h2, h3, h4, hA, fp_zero_ne_one, ite_true, ite_false] at e oh ⊢ <;>
    first | (exfalso; revert oh; decide) | grind

theorem lead_row {r : Nat} (hr : r < tr.height tt) (hS : tr.cell tt r sS = 1) (hk : clsOf tr tt r ≠ 1) :
    tr.cell tt r uc = 0 := by
  have hC : tr.cell tt r cC = 0 := by
    rcases isBool hL hr (cls_bool cC (by simp [classes])) with h | h
    · exact h
    · exact absurd (by simp [clsOf, h]) hk
  have e := con hL hr (uc_mem (e := mul3 (c sS) (not (c cC)) (c uc)) (by simp [cUtf8]))
  simp only [eval_mul3, eval_not, eval_c, hS, hC] at e; grind

theorem step_row {r : Nat} (hr : r + 1 < tr.height tt) (hS : tr.cell tt r sS = 1) (hf : tr.cell tt r fe = 0) :
    tr.cell tt (r + 1) uc = tr.cell tt r ucn := by
  have e := con hL (by omega : r < _) (uc_mem (e := mul3 (c sS) (not (c fe)) (sub (n uc) (c ucn)))
    (by simp [cUtf8]))
  simp only [eval_mul3, eval_not, eval_sub, eval_c, eval_n, hS, hf, nxt hr] at e; grind

theorem stop_row {r : Nat} (hr : r < tr.height tt) (hS : tr.cell tt r sS = 1) (hf : tr.cell tt r fe = 1) :
    tr.cell tt r ucn = 0 := by
  have e := con hL hr (uc_mem (e := mul3 (c sS) (c fe) (c ucn)) (by simp [cUtf8]))
  simp only [eval_mul3, eval_c, hS, hf] at e; grind

/-- A next-row flag: `n p = cls · z` inside a string. -/
theorem flag_next {r : Nat} (hr : r + 1 < tr.height tt) (hS : tr.cell tt r sS = 1) (hf : tr.cell tt r fe = 0)
    {pf cl z : Nat} (hm : mul3 (c sS) (not (c fe)) (sub (n pf) (.mul (c cl) (c z))) ∈ cUtf8)
    (hc : tr.cell tt r cl = 1) (hz : tr.cell tt r z = 1) : tr.cell tt (r + 1) pf = 1 := by
  have e := con hL (by omega : r < _) (uc_mem hm)
  simp only [eval_mul3, eval_mul, eval_not, eval_sub, eval_c, eval_n, hS, hf, hc, hz, nxt hr] at e; grind

/-- A zero test: `z = [e = 0]` for `act · e · z = 0`, `act · (e · i − (1 − z)) = 0`. -/
theorem ztest {r : Nat} (hr : r < tr.height tt) (ha : tr.cell tt r act = 1) {e : Expr} {z i : Nat}
    (h1 : Expr.mul (c act) (.mul e (c z)) ∈ cUtf8)
    (h2 : Expr.mul (c act) (sub (.mul e (c i)) (not (c z))) ∈ cUtf8) (he : e.eval tr tt r pub = 0) :
    tr.cell tt r z = 1 := by
  have e2 := con hL hr (uc_mem h2)
  simp only [eval_mul, eval_sub, eval_c, eval_not, ha, he] at e2; grind

end

end ZkFormal.NearV3.D1.AkmProof
