import WasmBase.Local.Add
/-!
# Local soundness of DIV (i32/i64 div_s, div_u, rem_s, rem_u, with traps)

`div_sound`: from the DIV constraints of an active row and the range facts given by its lookups
(BYTE pairs for the A/B/Q/R bytes, RANGE16 for D, the carries `cy`, the result limbs and `2·ra`,
`2·rb`, `2·rq`) and by the consumed operand messages, the row either traps (`tz + tov = 1`, exactly
when the spec returns `none`: division by zero, or `div_s` of `MIN` by `−1`) or produces
`Num.binop w k a b`.

Structure: the arithmetic core (`core_divU/remU/divS/remS`, `assemble`) is pure `Nat`/`Int`;
`neg_chain`, `pin_of`, `tz_facts`, `tov_fact` and the `eq*` lemmas turn constraint groups into
`Nat` facts; `div8_key` is the byte-product identity (`Q·B + R = A` once the carries are range
checked: without the `cy` lookups the chain only holds mod p).
-/
namespace WasmBase.Local
open ZkFormal.Algebra WasmBase.Chips NearSpecV3.Wasm
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 4000000

/-! ## Arithmetic core (pure `Nat`/`Int`) -/

theorem wrap_nat {w Q : Nat} (h : Q < 2 ^ w) : Num.wrap w (Q : Int) = Q := by
  unfold Num.wrap
  rw [show ((2 : Int) ^ w) = ((2 ^ w : Nat) : Int) by simp, ← Int.natCast_emod, Nat.mod_eq_of_lt h, Int.toNat_natCast]

theorem wrap_neg {w Q : Nat} (h : Q ≤ 2 ^ w) : Num.wrap w (-(Q : Int)) = (2 ^ w - Q) % 2 ^ w := by
  unfold Num.wrap
  rw [show ((2 : Int) ^ w) = ((2 ^ w : Nat) : Int) by simp,
    show -(Q : Int) = ((2 ^ w - Q : Nat) : Int) + ((2 ^ w : Nat) : Int) * (-1) by omega,
    Int.add_mul_emod_self_left, ← Int.natCast_emod, Int.toNat_natCast]

theorem pow_half {w : Nat} (hw : 1 ≤ w) : 2 ^ w = 2 * 2 ^ (w - 1) := by
  rw [← Nat.pow_succ']; congr 1; omega

/-- The signed value from the magnitude. -/
theorem signed_pos {w a : Nat} (h : a < 2 ^ (w - 1)) : Num.signed w a = a := by
  unfold Num.signed; split <;> omega

theorem signed_neg {w a A : Nat} (h : 2 ^ (w - 1) ≤ a) (hA : A + a = 2 ^ w) : Num.signed w a = -(A : Int) := by
  have := congrArg (Nat.cast : Nat → Int) hA; push_cast at this
  unfold Num.signed; split <;> omega

theorem div_uniq {A B Q R : Nat} (h : Q * B + R = A) (hR : R < B) : A / B = Q ∧ A % B = R :=
  (Nat.div_mod_unique (by omega)).mpr ⟨by rw [Nat.mul_comm] at h; omega, hR⟩

theorem core_divU (w a b Q R res tz : Nat) (htzB : tz = 1 ↔ b = 0)
    (hdiv : tz = 0 → Q * b + R = a ∧ R < b) (hres : res = Q) :
    (tz = 1 → Num.binop w 4 a b = none) ∧ (tz = 0 → Num.binop w 4 a b = some res) := by
  refine ⟨fun h => by simp [Num.binop, htzB.mp h], fun h => ?_⟩
  obtain ⟨e, r⟩ := hdiv h
  have hb : b ≠ 0 := by omega
  simp [Num.binop, hb, (div_uniq e r).1, hres]

theorem core_remU (w a b Q R res tz : Nat) (htzB : tz = 1 ↔ b = 0)
    (hdiv : tz = 0 → Q * b + R = a ∧ R < b) (hres : res = R) :
    (tz = 1 → Num.binop w 6 a b = none) ∧ (tz = 0 → Num.binop w 6 a b = some res) := by
  refine ⟨fun h => by simp [Num.binop, htzB.mp h], fun h => ?_⟩
  obtain ⟨e, r⟩ := hdiv h
  have hb : b ≠ 0 := by omega
  simp [Num.binop, hb, (div_uniq e r).2, hres]

theorem tdiv_nat (A B : Nat) : Int.tdiv (A : Int) (B : Int) = ((A / B : Nat) : Int) := (Int.ofNat_tdiv A B).symm
theorem tmod_nat (A B : Nat) : Int.tmod (A : Int) (B : Int) = ((A % B : Nat) : Int) := (Int.ofNat_tmod A B).symm

theorem core_divS (w a b A B Q R res hA hB hQ tz : Nat) (hw : 1 ≤ w)
    (hAb : hA = 0 ∨ hA = 1) (hBb : hB = 0 ∨ hB = 1) (hQb : hQ = 0 ∨ hQ = 1) (htz : tz = 0 ∨ tz = 1)
    (hQlt : Q < 2 ^ w)
    (hsa : Num.signed w a = if hA = 1 then -(A : Int) else A)
    (hsb : Num.signed w b = if hB = 1 then -(B : Int) else B)
    (hA1 : hA = 1 → A ≤ 2 ^ (w - 1)) (hQq : hQ = 1 ↔ 2 ^ (w - 1) ≤ Q)
    (htzB : tz = 1 ↔ b = 0) (hBz : B = 0 ↔ b = 0)
    (hdiv : tz = 0 → Q * B + R = A ∧ R < B)
    (hres0 : hA + hB - 2 * hA * hB = 0 → res = Q)
    (hres1 : hA + hB - 2 * hA * hB = 1 → res = (2 ^ w - Q) % 2 ^ w) :
    tz + (1 - tz) * hA * hB * hQ ≤ 1 ∧
    (tz + (1 - tz) * hA * hB * hQ = 1 → Num.divS w a b = none) ∧
    (tz + (1 - tz) * hA * hB * hQ = 0 → Num.divS w a b = some res) := by
  have hH := Nat.two_pow_pos (w - 1)
  have hN := pow_half hw
  have hHi : ((2 : Int) ^ (w - 1)) = ((2 ^ (w - 1) : Nat) : Int) := by simp
  rcases htz with rfl | rfl
  · obtain ⟨e, r⟩ := hdiv rfl
    have hbne : b ≠ 0 := fun h => by have := hBz.mpr h; omega
    have hq := (div_uniq e r).1
    unfold Num.divS
    rw [if_neg hbne]
    rcases hAb with rfl | rfl <;> rcases hBb with rfl | rfl <;>
      simp only [ite_true, ite_false, show ((0 : Nat) = 1) = False from by simp] at hsa hsb <;>
      rw [hsa, hsb]
    · -- (+, +)
      have hres := hres0 (by decide)
      refine ⟨by omega, by omega, fun _ => ?_⟩
      rw [if_neg (by omega), tdiv_nat, hq, wrap_nat hQlt, hres]
    · -- (+, −)
      have hres := hres1 (by decide)
      refine ⟨by omega, by omega, fun _ => ?_⟩
      rw [if_neg (by omega), Int.tdiv_neg, tdiv_nat, hq, wrap_neg (by omega), hres]
    · -- (−, +)
      have hres := hres1 (by decide)
      refine ⟨by omega, by omega, fun _ => ?_⟩
      rw [if_neg (by omega), Int.neg_tdiv, tdiv_nat, hq, wrap_neg (by omega), hres]
    · -- (−, −)
      have hres := hres0 (by decide)
      have hAle := hA1 rfl
      rcases hQb with rfl | rfl
      · refine ⟨by omega, by omega, fun _ => ?_⟩
        have hQ0 : Q < 2 ^ (w - 1) := by
          rcases Nat.lt_or_ge Q (2 ^ (w - 1)) with h | h
          · exact h
          · exact absurd (hQq.mpr h) (by decide)
        rw [if_neg ?_, Int.neg_tdiv, Int.tdiv_neg, Int.neg_neg, tdiv_nat, hq, wrap_nat hQlt, hres]
        rintro ⟨h1, h2⟩
        have hB1 : B = 1 := by omega
        subst hB1
        omega
      · refine ⟨by omega, fun _ => ?_, by omega⟩
        have hQ1 := hQq.mp rfl
        have hB1 : B = 1 := by
          rcases (show B = 1 ∨ 2 ≤ B by omega) with h | h
          · exact h
          · have : Q * 2 ≤ Q * B := Nat.mul_le_mul_left Q h
            omega
        subst hB1
        rw [if_pos ⟨by omega, by omega⟩]
  · have hb0 := htzB.mp rfl
    refine ⟨by omega, fun _ => by unfold Num.divS; rw [if_pos hb0], by omega⟩

theorem core_remS (w a b A B Q R res hA hB tz : Nat)
    (hsa : Num.signed w a = if hA = 1 then -(A : Int) else A)
    (hsb : Num.signed w b = if hB = 1 then -(B : Int) else B) (hAb : hA = 0 ∨ hA = 1)
    (hRlt : R < 2 ^ w)
    (htzB : tz = 1 ↔ b = 0) (hBz : B = 0 ↔ b = 0)
    (hdiv : tz = 0 → Q * B + R = A ∧ R < B)
    (hres0 : hA = 0 → res = R) (hres1 : hA = 1 → res = (2 ^ w - R) % 2 ^ w) :
    (tz = 1 → Num.remS w a b = none) ∧ (tz = 0 → Num.remS w a b = some res) := by
  refine ⟨fun h => by unfold Num.remS; rw [if_pos (htzB.mp h)], fun h => ?_⟩
  obtain ⟨e, r⟩ := hdiv h
  have hbne : b ≠ 0 := fun h => by have := hBz.mpr h; omega
  have hr := (div_uniq e r).2
  unfold Num.remS
  rw [if_neg hbne]
  rcases hAb with rfl | rfl <;>
    simp only [ite_true, ite_false, show ((0 : Nat) = 1) = False from by simp] at hsa <;> rw [hsa, hsb]
  · rw [hres0 rfl]
    split
    · rw [Int.tmod_neg, tmod_nat, hr, wrap_nat hRlt]
    · rw [tmod_nat, hr, wrap_nat hRlt]
  · rw [hres1 rfl]
    split
    · rw [Int.tmod_neg, Int.neg_tmod, tmod_nat, hr, wrap_neg (by omega : R ≤ 2 ^ w)]
    · rw [Int.neg_tmod, tmod_nat, hr, wrap_neg (by omega : R ≤ 2 ^ w)]

theorem binop3 (w a b : Nat) : Num.binop w 3 a b = Num.divS w a b := rfl
theorem binop4 (w a b : Nat) : Num.binop w 4 a b = if b = 0 then none else some (a / b) := rfl
theorem binop5 (w a b : Nat) : Num.binop w 5 a b = Num.remS w a b := rfl
theorem binop6 (w a b : Nat) : Num.binop w 6 a b = if b = 0 then none else some (a % b) := rfl

/-- Magnitude facts give the signed value. -/
theorem signed_mag {w a A hA : Nat} (hAb : hA = 0 ∨ hA = 1) (hAa : hA = 1 ↔ 2 ^ (w - 1) ≤ a)
    (h0 : hA = 0 → A = a) (h1 : hA = 1 → A + a = 2 ^ w) :
    Num.signed w a = if hA = 1 then -(A : Int) else A := by
  rcases hAb with rfl | rfl
  · have : a < 2 ^ (w - 1) := Nat.lt_of_not_le fun h => absurd (hAa.mpr h) (by decide)
    rw [if_neg (by decide), signed_pos this, h0 rfl]
  · rw [if_pos rfl, signed_neg (hAa.mp rfl) (h1 rfl)]

/-- The four operations from the magnitude-level facts. -/
theorem assemble (w a b A B Q R res fS fU rS rU hA hB hQ tz tov : Nat) (hw : 1 ≤ w)
    (hf : (fS = 1 ∧ fU = 0 ∧ rS = 0 ∧ rU = 0) ∨ (fS = 0 ∧ fU = 1 ∧ rS = 0 ∧ rU = 0) ∨
      (fS = 0 ∧ fU = 0 ∧ rS = 1 ∧ rU = 0) ∨ (fS = 0 ∧ fU = 0 ∧ rS = 0 ∧ rU = 1))
    (hAb : hA = 0 ∨ hA = 1) (hBb : hB = 0 ∨ hB = 1) (hQb : hQ = 0 ∨ hQ = 1) (htz : tz = 0 ∨ tz = 1)
    (hb : b < 2 ^ w) (hQlt : Q < 2 ^ w) (hRlt : R < 2 ^ w)
    (hAa : hA = 1 ↔ 2 ^ (w - 1) ≤ a) (hBb' : hB = 1 ↔ 2 ^ (w - 1) ≤ b) (hQq : hQ = 1 ↔ 2 ^ (w - 1) ≤ Q)
    (hnA0 : (fS + rS) * hA = 0 → A = a) (hnA1 : (fS + rS) * hA = 1 → A + a = 2 ^ w)
    (hnB0 : (fS + rS) * hB = 0 → B = b) (hnB1 : (fS + rS) * hB = 1 → B + b = 2 ^ w)
    (htzB : tz = 1 ↔ B = 0) (htov : tov = (1 - tz) * fS * hA * hB * hQ)
    (hdiv : tz = 0 → Q * B + R = A ∧ R < B)
    (hr0 : fS * (hA + hB - 2 * hA * hB) + rS * hA = 0 → res = (fS + fU) * Q + (rS + rU) * R)
    (hr1 : fS * (hA + hB - 2 * hA * hB) + rS * hA = 1 →
      res = (2 ^ w - ((fS + fU) * Q + (rS + rU) * R)) % 2 ^ w) :
    tz + tov ≤ 1 ∧
    (tz + tov = 1 → Num.binop w (3 + fU + 2 * rS + 3 * rU) a b = none) ∧
    (tz + tov = 0 → Num.binop w (3 + fU + 2 * rS + 3 * rU) a b = some res) := by
  have hH := Nat.two_pow_pos (w - 1)
  have hN := pow_half hw
  rcases hf with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
    simp only [Nat.zero_add, Nat.add_zero, Nat.zero_mul, Nat.mul_zero, Nat.one_mul, Nat.mul_one, Nat.reduceAdd,
      Nat.reduceMul, forall_const, true_implies] at *
  · -- div_s
    have hsa := signed_mag hAb hAa hnA0 hnA1
    have hsb := signed_mag hBb hBb' hnB0 hnB1
    have hBz : B = 0 ↔ b = 0 := by
      rcases hBb with rfl | rfl
      · rw [hnB0 rfl]
      · have := hnB1 rfl; have := hBb'.mp rfl; omega
    have hA1 : hA = 1 → A ≤ 2 ^ (w - 1) := fun h => by have := hnA1 h; have := hAa.mp h; omega
    have := core_divS w a b A B Q R res hA hB hQ tz hw hAb hBb hQb htz hQlt hsa hsb hA1 hQq
      (htzB.trans hBz) hBz hdiv hr0 (fun h => by rw [hr1 h])
    rw [htov]
    rw [binop3]
    simpa [Nat.mul_assoc] using this
  · -- div_u
    have hBb0 := hnB0
    subst hBb0
    have hA0 := hnA0
    subst hA0
    have := core_divU w A B Q R res tz htzB hdiv hr0
    rw [htov]
    rw [binop4]
    exact ⟨by omega, fun h => this.1 (by omega), fun h => this.2 (by omega)⟩
  · -- rem_s
    have hsa := signed_mag hAb hAa hnA0 hnA1
    have hsb := signed_mag hBb hBb' hnB0 hnB1
    have hBz : B = 0 ↔ b = 0 := by
      rcases hBb with rfl | rfl
      · rw [hnB0 rfl]
      · have := hnB1 rfl; have := hBb'.mp rfl; omega
    have := core_remS w a b A B Q R res hA hB tz hsa hsb hAb hRlt (htzB.trans hBz) hBz hdiv hr0 hr1
    rw [htov]
    rw [binop5]
    obtain ⟨t1, t2⟩ := this
    refine ⟨?_, fun h => t1 ?_, fun h => t2 ?_⟩
    · omega
    · omega
    · omega
  · -- rem_u
    have hBb0 := hnB0
    subst hBb0
    have hA0 := hnA0
    subst hA0
    have := core_remU w A B Q R res tz htzB hdiv hr0
    rw [htov]
    rw [binop6]
    exact ⟨by omega, fun h => this.1 (by omega), fun h => this.2 (by omega)⟩

/-! ## From the constraints to `Nat` facts -/

@[simp] theorem natRow_cur (c : Nat → Nat) (rw : Row) (i : Nat) : (natRow c rw).cur i = (c i : F) := rfl

theorem bit_of {c : Nat → Nat} {rw : Row} {i : Nat} (hP : ∀ i, c i < P)
    (h : Expr.eval (natRow c rw) (Chips.bool (v i)) = 0) : c i ≤ 1 := by
  simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Expr.eval_col, natRow_cur] at h
  have := bool_nat (hP i) h; omega

theorem zero_of {c : Nat → Nat} {rw : Row} {j : Nat} (hP : ∀ i, c i < P) (h9 : c 9 = 0)
    (h : Expr.eval (natRow c rw) ((1 - v Div.is64) * v j) = 0) : c j = 0 := by
  simp only [v, Div.is64, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Expr.eval_col, natRow_cur, h9] at h
  exact zero_of_sel0 (hP j) h

theorem L_eval (c : Nat → Nat) (rw : Row) (base i : Nat) :
    (Div.L base i).eval (natRow c rw) = ((c (base + 2 * i) + 256 * c (base + 2 * i + 1) : Nat) : F) := by
  simp only [Div.L, v, Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', Expr.eval_col, natRow_cur,
    Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul] <;> grind

theorem sel_eval (c : Nat → Nat) (rw : Row) (X Y : Expr) (x y : Nat) (h9 : c 9 ≤ 1)
    (hx : X.eval (natRow c rw) = (x : F)) (hy : Y.eval (natRow c rw) = (y : F)) :
    (v Div.is64 * X + (1 - v Div.is64) * Y).eval (natRow c rw) = ((if c 9 = 1 then x else y : Nat) : F) := by
  simp only [v, Div.is64, Expr.eval_add', Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Expr.eval_col, natRow_cur,
    hx, hy]
  rcases (show c 9 = 0 ∨ c 9 = 1 by omega) with h | h <;> rw [h] <;> grind

/-- A pinned top limb: `top = 2^15 hb + r` with `2 r` range-checked mod `p`. -/
theorem pin_of {c : Nat → Nat} {rw : Row} {hbI rI top : Nat} {topE : Expr} (hP : ∀ i, c i < P)
    (htop : topE.eval (natRow c rw) = (top : F)) (htl : top < 65536) (hb : c hbI ≤ 1)
    (h2r : (2 * c rI) % P < 65536)
    (h : Expr.eval (natRow c rw) (topE - 32768 * v hbI - v rI) = 0) :
    top = 32768 * c hbI + c rI ∧ c rI < 32768 := by
  have hP' := P_val
  have hr := hP rI
  simp only [v, Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', Expr.eval_col, natRow_cur, htop] at h
  have e : ((top : Nat) : F) = ((32768 * c hbI + c rI : Nat) : F) := by fp_ring
  have := congrArg Fp.toNat e
  rw [Fp.toNat_cast, Fp.toNat_cast, Nat.mod_eq_of_lt (show top < P by omega)] at this
  rw [hP'] at this h2r hr
  rcases (show c hbI = 0 ∨ c hbI = 1 by omega) with g | g <;> rw [g] at this ⊢
  · rw [Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt hr] at this
    subst this
    rw [Nat.mod_eq_of_lt (by omega)] at h2r
    omega
  · by_cases hw : 32768 * 1 + c rI < 2013265921
    · rw [Nat.mod_eq_of_lt hw] at this
      rw [Nat.mod_eq_of_lt (by omega)] at h2r
      omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at this
      exfalso
      rw [show 2 * c rI = (2 * top + 2013265921 - 65536) + 2013265921 by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)] at h2r
      omega

theorem act_eval {c : Nat → Nat} {rw : Row} (hact : c 5 + c 6 + c 7 + c 8 = 1) :
    Div.act.eval (natRow c rw) = ((1 : Nat) : F) := by
  simp only [Div.act, v, Div.fDivS, Div.fDivU, Div.fRemS, Div.fRemU, Expr.eval_add', Expr.eval_col, natRow_cur]
  rw [← hact]; simp only [Lean.Grind.Semiring.natCast_add]

theorem tz_facts {c : Nat → Nat} {rw : Row} (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (hbB : ∀ i, i < 8 → c (34 + i) < 256)
    (t1 : Expr.eval (natRow c rw) (v Div.tz - Div.act * (1 - Div.bsum * v Div.invB)) = 0)
    (t2 : Expr.eval (natRow c rw) (Div.bsum * v Div.tz) = 0) :
    (c 82 = 0 ∨ c 82 = 1) ∧
    (c 82 = 1 ↔ c 34 + c 35 + c 36 + c 37 + c 38 + c 39 + c 40 + c 41 = 0) := by
  have hP' := P_val
  have hs : Div.bsum.eval (natRow c rw) = ((c 34 + c 35 + c 36 + c 37 + c 38 + c 39 + c 40 + c 41 : Nat) : F) := by
    simp only [Div.bsum, List.range, List.range.loop, List.map, List.foldl, v, Div.BB, Expr.eval_add',
      Expr.eval_ofNat', Expr.eval_col, natRow_cur, Nat.reduceAdd]
    fp_ring
  have b0 := hbB 0 (by decide); have b1 := hbB 1 (by decide); have b2 := hbB 2 (by decide)
  have b3 := hbB 3 (by decide); have b4 := hbB 4 (by decide); have b5 := hbB 5 (by decide)
  have b6 := hbB 6 (by decide); have b7 := hbB 7 (by decide)
  simp only [Nat.reduceAdd] at b0 b1 b2 b3 b4 b5 b6 b7
  simp only [v, Div.tz, Div.invB, Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', Expr.eval_col, natRow_cur,
    hs, act_eval hact] at t1 t2
  rcases zero_of_mul_nat (by omega) (hP 82) t2 with h | h
  · have e : ((c 82 : Nat) : F) = ((1 : Nat) : F) := by rw [h] at t1; grind
    have := natEq e (hP 82) (by decide)
    omega
  · rw [h] at t1
    have hne : c 34 + c 35 + c 36 + c 37 + c 38 + c 39 + c 40 + c 41 ≠ 0 := by
      intro h0; rw [h0] at t1; grind
    omega

theorem tov_fact {c : Nat → Nat} {rw : Row} (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1) (h82 : c 82 ≤ 1) (h5 : c 5 ≤ 1) (h22 : c 22 ≤ 1)
    (h24 : c 24 ≤ 1) (h84 : c 84 ≤ 1)
    (t3 : Expr.eval (natRow c rw) (v Div.tov - Div.nt * v Div.fDivS * v Div.hbA * v Div.hbB * v Div.hbQ) = 0) :
    c 86 = (1 - c 82) * c 5 * c 22 * c 24 * c 84 := by
  have hP' := P_val
  simp only [v, Div.nt, Div.tz, Div.tov, Div.fDivS, Div.hbA, Div.hbB, Div.hbQ, Expr.eval_sub', Expr.eval_mul',
    Expr.eval_ofNat', Expr.eval_col, natRow_cur, act_eval hact] at t3
  have hle : (1 - c 82) * c 5 * c 22 * c 24 * c 84 ≤ 1 * 1 * 1 * 1 * 1 :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by omega) h5) h22) h24) h84
  have e : ((c 86 : Nat) : F) = (((1 - c 82) * c 5 * c 22 * c 24 * c 84 : Nat) : F) := by
    rcases (show c 82 = 0 ∨ c 82 = 1 by omega) with h | h <;> rw [h] at t3 ⊢ <;> fp_ring
  exact natEq e (hP 86) (by omega)

theorem neg_limb {s X x cin cout g : Nat} (hs : s = 0 ∨ s = 1) (hg : g = 1)
    (hX : X < 65536) (hx : x < 65536) (hcin : cin ≤ 1) (hcout : cout ≤ 1)
    (h1 : (g : F) * ((((1 : Nat) : F) - (s : F)) * ((X : F) - (x : F))) = 0)
    (h2 : (g : F) * ((s : F) * ((X : F) + (x : F) + (cin : F) - ((65536 : Nat) : F) * (cout : F))) = 0) :
    (s = 0 → X = x) ∧ (s = 1 → X + x + cin = 65536 * cout) := by
  have hP' := P_val
  subst hg
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h; exact natEq (by first | fp_ring | grind) (by omega) (by omega)
  · subst h; exact natEq (by first | fp_ring | grind) (by omega) (by omega)

theorem neg_chain (c : Nat → Nat) (rw : Row) (sE : Expr) (s : Nat) (Xe xe : Nat → Expr) (Xn xn : Nat → Nat)
    (cb : Nat)
    (h : ∀ x ∈ Div.negChain sE Xe xe cb, x.eval (natRow c rw) = 0)
    (hsE : sE.eval (natRow c rw) = (s : F)) (hs : s = 0 ∨ s = 1)
    (hXe : ∀ i, (Xe i).eval (natRow c rw) = (Xn i : F)) (hxe : ∀ i, (xe i).eval (natRow c rw) = (xn i : F))
    (hX : ∀ i, i < 4 → Xn i < 65536) (hx : ∀ i, i < 4 → xn i < 65536)
    (hcb : ∀ i, i < 4 → c (cb + i) ≤ 1) :
    (s = 0 → Xn 0 = xn 0 ∧ Xn 1 = xn 1) ∧
    (s = 1 → Xn 0 + xn 0 = 65536 * c cb ∧ Xn 1 + xn 1 + c cb = 65536 * c (cb + 1)) ∧
    (c 9 = 1 → (s = 0 → Xn 2 = xn 2 ∧ Xn 3 = xn 3) ∧
      (s = 1 → Xn 2 + xn 2 + c (cb + 1) = 65536 * c (cb + 2) ∧ Xn 3 + xn 3 + c (cb + 2) = 65536 * c (cb + 3))) := by
  simp only [Div.negChain, List.forall_mem_flatMap, List.mem_range, List.forall_mem_cons, List.forall_mem_nil,
    and_true] at h
  have hP' := P_val
  obtain ⟨a1, a2, -⟩ := h 0 (by decide)
  obtain ⟨b1, b2, -⟩ := h 1 (by decide)
  obtain ⟨c1, c2, -⟩ := h 2 (by decide)
  obtain ⟨d1, d2, -⟩ := h 3 (by decide)
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat', hsE, hXe, hxe, Div.cIn, B16, v,
    Expr.eval_col, natRow_cur, Div.is64, ite_true, ite_false, Nat.add_zero,
    show (1 : Nat) ≠ 0 from by decide, show (2 : Nat) ≠ 0 from by decide,
    show (3 : Nat) ≠ 0 from by decide, show ¬ ((2 : Nat) < 2) from by decide, show ¬ ((3 : Nat) < 2) from by decide,
    show ((0 : Nat) < 2) from by decide, show ((1 : Nat) < 2) from by decide,
    show cb + 2 - 1 = cb + 1 from by omega, show cb + 3 - 1 = cb + 2 from by omega,
    show cb + 1 - 1 = cb from by omega] at a1 a2 b1 b2 c1 c2 d1 d2
  have x0 := hX 0 (by decide); have x1 := hX 1 (by decide); have x2 := hX 2 (by decide); have x3 := hX 3 (by decide)
  have y0 := hx 0 (by decide); have y1 := hx 1 (by decide); have y2 := hx 2 (by decide); have y3 := hx 3 (by decide)
  have k0 := hcb 0 (by decide); have k1 := hcb 1 (by decide); have k2 := hcb 2 (by decide)
  have k3 := hcb 3 (by decide)
  simp only [Nat.add_zero] at k0
  have L0 := neg_limb (cin := 0) hs rfl x0 y0 (by omega) k0 a1 a2
  have L1 := neg_limb hs rfl x1 y1 k0 k1 b1 b2
  refine ⟨fun h => ⟨L0.1 h, L1.1 h⟩, fun h => ⟨by have := L0.2 h; omega, L1.2 h⟩, fun h9 => ?_⟩
  rw [h9] at c1 c2 d1 d2
  have L2 := neg_limb hs rfl x2 y2 k1 k2 c1 c2
  have L3 := neg_limb hs rfl x3 y3 k2 k3 d1 d2
  exact ⟨fun h => ⟨L2.1 h, L3.1 h⟩, fun h => ⟨L2.2 h, L3.2 h⟩⟩
theorem div8_key (q0 q1 q2 q3 q4 q5 q6 q7 b0 b1 b2 b3 b4 b5 b6 b7 r0 r1 r2 r3 r4 r5 r6 r7 a0 a1 a2 a3 a4 a5 a6 a7 c0 c1 c2 c3 c4 c5 c6 : Nat)
        (E0 : q0 * b0 + r0 = a0 + 256 * c0)
    (E1 : q0 * b1 + q1 * b0 + r1 + c0 = a1 + 256 * c1)
    (E2 : q0 * b2 + q1 * b1 + q2 * b0 + r2 + c1 = a2 + 256 * c2)
    (E3 : q0 * b3 + q1 * b2 + q2 * b1 + q3 * b0 + r3 + c2 = a3 + 256 * c3)
    (E4 : q0 * b4 + q1 * b3 + q2 * b2 + q3 * b1 + q4 * b0 + r4 + c3 = a4 + 256 * c4)
    (E5 : q0 * b5 + q1 * b4 + q2 * b3 + q3 * b2 + q4 * b1 + q5 * b0 + r5 + c4 = a5 + 256 * c5)
    (E6 : q0 * b6 + q1 * b5 + q2 * b4 + q3 * b3 + q4 * b2 + q5 * b1 + q6 * b0 + r6 + c5 = a6 + 256 * c6)
    (E7 : q0 * b7 + q1 * b6 + q2 * b5 + q3 * b4 + q4 * b3 + q5 * b2 + q6 * b1 + q7 * b0 + r7 + c6 = a7)
    (Z8 : q1 * b7 + q2 * b6 + q3 * b5 + q4 * b4 + q5 * b3 + q6 * b2 + q7 * b1 = 0)
    (Z9 : q2 * b7 + q3 * b6 + q4 * b5 + q5 * b4 + q6 * b3 + q7 * b2 = 0)
    (Z10 : q3 * b7 + q4 * b6 + q5 * b5 + q6 * b4 + q7 * b3 = 0)
    (Z11 : q4 * b7 + q5 * b6 + q6 * b5 + q7 * b4 = 0)
    (Z12 : q5 * b7 + q6 * b6 + q7 * b5 = 0)
    (Z13 : q6 * b7 + q7 * b6 = 0)
    (Z14 : q7 * b7 = 0) :
    (q0 + 2 ^ 8 * q1 + 2 ^ 16 * q2 + 2 ^ 24 * q3 + 2 ^ 32 * q4 + 2 ^ 40 * q5 + 2 ^ 48 * q6 + 2 ^ 56 * q7) * (b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3 + 2 ^ 32 * b4 + 2 ^ 40 * b5 + 2 ^ 48 * b6 + 2 ^ 56 * b7) + (r0 + 2 ^ 8 * r1 + 2 ^ 16 * r2 + 2 ^ 24 * r3 + 2 ^ 32 * r4 + 2 ^ 40 * r5 + 2 ^ 48 * r6 + 2 ^ 56 * r7) = (a0 + 2 ^ 8 * a1 + 2 ^ 16 * a2 + 2 ^ 24 * a3 + 2 ^ 32 * a4 + 2 ^ 40 * a5 + 2 ^ 48 * a6 + 2 ^ 56 * a7) := by
  grind


macro "fpr" : tactic =>
  `(tactic| first | (simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul] <;> grind) | grind)

theorem eqP0 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (hy : ∀ i, i < 32 → c (26 + i) < 256) (hcy : ∀ k, k < 8 → c (66 + k) < 65536)
    (hd : ∀ i, i < 4 → c (74 + i) < 65536)
    (h : Expr.eval (natRow c rw) (Div.nt * Div.prodEq 0) = 0) (h82 : c 82 = 0) :
    c 42 * c 34 + c 50 = c 26 + 256 * c 66 := by
  have hP' := P_val
  have mb : ∀ x y : Nat, x < 256 → y < 256 → x * y ≤ 65025 := fun x y hx hy =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)) (by decide)
  have y26 : c 26 < 256 := hy 0 (by decide)
  have y34 : c 34 < 256 := hy 8 (by decide)
  have y42 : c 42 < 256 := hy 16 (by decide)
  have y50 : c 50 < 256 := hy 24 (by decide)
  have k66 : c 66 < 65536 := hcy 0 (by decide)
  have p42_34 := mb _ _ y42 y34
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82] at h
  exact natEq (by fpr) (by omega) (by omega)

theorem eqP1 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (hy : ∀ i, i < 32 → c (26 + i) < 256) (hcy : ∀ k, k < 8 → c (66 + k) < 65536)
    (hd : ∀ i, i < 4 → c (74 + i) < 65536)
    (h : Expr.eval (natRow c rw) (Div.nt * Div.prodEq 1) = 0) (h82 : c 82 = 0) :
    c 42 * c 35 + c 43 * c 34 + c 51 + c 66 = c 27 + 256 * c 67 := by
  have hP' := P_val
  have mb : ∀ x y : Nat, x < 256 → y < 256 → x * y ≤ 65025 := fun x y hx hy =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)) (by decide)
  have y27 : c 27 < 256 := hy 1 (by decide)
  have y34 : c 34 < 256 := hy 8 (by decide)
  have y35 : c 35 < 256 := hy 9 (by decide)
  have y42 : c 42 < 256 := hy 16 (by decide)
  have y43 : c 43 < 256 := hy 17 (by decide)
  have y51 : c 51 < 256 := hy 25 (by decide)
  have k67 : c 67 < 65536 := hcy 1 (by decide)
  have k66 : c 66 < 65536 := hcy 0 (by decide)
  have p42_35 := mb _ _ y42 y35
  have p43_34 := mb _ _ y43 y34
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82] at h
  exact natEq (by fpr) (by omega) (by omega)

theorem eqP2 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (hy : ∀ i, i < 32 → c (26 + i) < 256) (hcy : ∀ k, k < 8 → c (66 + k) < 65536)
    (hd : ∀ i, i < 4 → c (74 + i) < 65536)
    (h : Expr.eval (natRow c rw) (Div.nt * Div.prodEq 2) = 0) (h82 : c 82 = 0) :
    c 42 * c 36 + c 43 * c 35 + c 44 * c 34 + c 52 + c 67 = c 28 + 256 * c 68 := by
  have hP' := P_val
  have mb : ∀ x y : Nat, x < 256 → y < 256 → x * y ≤ 65025 := fun x y hx hy =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)) (by decide)
  have y28 : c 28 < 256 := hy 2 (by decide)
  have y34 : c 34 < 256 := hy 8 (by decide)
  have y35 : c 35 < 256 := hy 9 (by decide)
  have y36 : c 36 < 256 := hy 10 (by decide)
  have y42 : c 42 < 256 := hy 16 (by decide)
  have y43 : c 43 < 256 := hy 17 (by decide)
  have y44 : c 44 < 256 := hy 18 (by decide)
  have y52 : c 52 < 256 := hy 26 (by decide)
  have k68 : c 68 < 65536 := hcy 2 (by decide)
  have k67 : c 67 < 65536 := hcy 1 (by decide)
  have p42_36 := mb _ _ y42 y36
  have p43_35 := mb _ _ y43 y35
  have p44_34 := mb _ _ y44 y34
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82] at h
  exact natEq (by fpr) (by omega) (by omega)

theorem eqP3 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (hy : ∀ i, i < 32 → c (26 + i) < 256) (hcy : ∀ k, k < 8 → c (66 + k) < 65536)
    (hd : ∀ i, i < 4 → c (74 + i) < 65536)
    (h : Expr.eval (natRow c rw) (Div.nt * Div.prodEq 3) = 0) (h82 : c 82 = 0) :
    c 42 * c 37 + c 43 * c 36 + c 44 * c 35 + c 45 * c 34 + c 53 + c 68 = c 29 + 256 * c 69 := by
  have hP' := P_val
  have mb : ∀ x y : Nat, x < 256 → y < 256 → x * y ≤ 65025 := fun x y hx hy =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)) (by decide)
  have y29 : c 29 < 256 := hy 3 (by decide)
  have y34 : c 34 < 256 := hy 8 (by decide)
  have y35 : c 35 < 256 := hy 9 (by decide)
  have y36 : c 36 < 256 := hy 10 (by decide)
  have y37 : c 37 < 256 := hy 11 (by decide)
  have y42 : c 42 < 256 := hy 16 (by decide)
  have y43 : c 43 < 256 := hy 17 (by decide)
  have y44 : c 44 < 256 := hy 18 (by decide)
  have y45 : c 45 < 256 := hy 19 (by decide)
  have y53 : c 53 < 256 := hy 27 (by decide)
  have k69 : c 69 < 65536 := hcy 3 (by decide)
  have k68 : c 68 < 65536 := hcy 2 (by decide)
  have p42_37 := mb _ _ y42 y37
  have p43_36 := mb _ _ y43 y36
  have p44_35 := mb _ _ y44 y35
  have p45_34 := mb _ _ y45 y34
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82] at h
  exact natEq (by fpr) (by omega) (by omega)

theorem eqP4 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (hy : ∀ i, i < 32 → c (26 + i) < 256) (hcy : ∀ k, k < 8 → c (66 + k) < 65536)
    (hd : ∀ i, i < 4 → c (74 + i) < 65536)
    (h : Expr.eval (natRow c rw) (Div.nt * Div.prodEq 4) = 0) (h82 : c 82 = 0) :
    c 42 * c 38 + c 43 * c 37 + c 44 * c 36 + c 45 * c 35 + c 46 * c 34 + c 54 + c 69 = c 30 + 256 * c 70 := by
  have hP' := P_val
  have mb : ∀ x y : Nat, x < 256 → y < 256 → x * y ≤ 65025 := fun x y hx hy =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)) (by decide)
  have y30 : c 30 < 256 := hy 4 (by decide)
  have y34 : c 34 < 256 := hy 8 (by decide)
  have y35 : c 35 < 256 := hy 9 (by decide)
  have y36 : c 36 < 256 := hy 10 (by decide)
  have y37 : c 37 < 256 := hy 11 (by decide)
  have y38 : c 38 < 256 := hy 12 (by decide)
  have y42 : c 42 < 256 := hy 16 (by decide)
  have y43 : c 43 < 256 := hy 17 (by decide)
  have y44 : c 44 < 256 := hy 18 (by decide)
  have y45 : c 45 < 256 := hy 19 (by decide)
  have y46 : c 46 < 256 := hy 20 (by decide)
  have y54 : c 54 < 256 := hy 28 (by decide)
  have k70 : c 70 < 65536 := hcy 4 (by decide)
  have k69 : c 69 < 65536 := hcy 3 (by decide)
  have p42_38 := mb _ _ y42 y38
  have p43_37 := mb _ _ y43 y37
  have p44_36 := mb _ _ y44 y36
  have p45_35 := mb _ _ y45 y35
  have p46_34 := mb _ _ y46 y34
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82] at h
  exact natEq (by fpr) (by omega) (by omega)

theorem eqP5 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (hy : ∀ i, i < 32 → c (26 + i) < 256) (hcy : ∀ k, k < 8 → c (66 + k) < 65536)
    (hd : ∀ i, i < 4 → c (74 + i) < 65536)
    (h : Expr.eval (natRow c rw) (Div.nt * Div.prodEq 5) = 0) (h82 : c 82 = 0) :
    c 42 * c 39 + c 43 * c 38 + c 44 * c 37 + c 45 * c 36 + c 46 * c 35 + c 47 * c 34 + c 55 + c 70 = c 31 + 256 * c 71 := by
  have hP' := P_val
  have mb : ∀ x y : Nat, x < 256 → y < 256 → x * y ≤ 65025 := fun x y hx hy =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)) (by decide)
  have y31 : c 31 < 256 := hy 5 (by decide)
  have y34 : c 34 < 256 := hy 8 (by decide)
  have y35 : c 35 < 256 := hy 9 (by decide)
  have y36 : c 36 < 256 := hy 10 (by decide)
  have y37 : c 37 < 256 := hy 11 (by decide)
  have y38 : c 38 < 256 := hy 12 (by decide)
  have y39 : c 39 < 256 := hy 13 (by decide)
  have y42 : c 42 < 256 := hy 16 (by decide)
  have y43 : c 43 < 256 := hy 17 (by decide)
  have y44 : c 44 < 256 := hy 18 (by decide)
  have y45 : c 45 < 256 := hy 19 (by decide)
  have y46 : c 46 < 256 := hy 20 (by decide)
  have y47 : c 47 < 256 := hy 21 (by decide)
  have y55 : c 55 < 256 := hy 29 (by decide)
  have k71 : c 71 < 65536 := hcy 5 (by decide)
  have k70 : c 70 < 65536 := hcy 4 (by decide)
  have p42_39 := mb _ _ y42 y39
  have p43_38 := mb _ _ y43 y38
  have p44_37 := mb _ _ y44 y37
  have p45_36 := mb _ _ y45 y36
  have p46_35 := mb _ _ y46 y35
  have p47_34 := mb _ _ y47 y34
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82] at h
  exact natEq (by fpr) (by omega) (by omega)

theorem eqP6 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (hy : ∀ i, i < 32 → c (26 + i) < 256) (hcy : ∀ k, k < 8 → c (66 + k) < 65536)
    (hd : ∀ i, i < 4 → c (74 + i) < 65536)
    (h : Expr.eval (natRow c rw) (Div.nt * Div.prodEq 6) = 0) (h82 : c 82 = 0) :
    c 42 * c 40 + c 43 * c 39 + c 44 * c 38 + c 45 * c 37 + c 46 * c 36 + c 47 * c 35 + c 48 * c 34 + c 56 + c 71 = c 32 + 256 * c 72 := by
  have hP' := P_val
  have mb : ∀ x y : Nat, x < 256 → y < 256 → x * y ≤ 65025 := fun x y hx hy =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)) (by decide)
  have y32 : c 32 < 256 := hy 6 (by decide)
  have y34 : c 34 < 256 := hy 8 (by decide)
  have y35 : c 35 < 256 := hy 9 (by decide)
  have y36 : c 36 < 256 := hy 10 (by decide)
  have y37 : c 37 < 256 := hy 11 (by decide)
  have y38 : c 38 < 256 := hy 12 (by decide)
  have y39 : c 39 < 256 := hy 13 (by decide)
  have y40 : c 40 < 256 := hy 14 (by decide)
  have y42 : c 42 < 256 := hy 16 (by decide)
  have y43 : c 43 < 256 := hy 17 (by decide)
  have y44 : c 44 < 256 := hy 18 (by decide)
  have y45 : c 45 < 256 := hy 19 (by decide)
  have y46 : c 46 < 256 := hy 20 (by decide)
  have y47 : c 47 < 256 := hy 21 (by decide)
  have y48 : c 48 < 256 := hy 22 (by decide)
  have y56 : c 56 < 256 := hy 30 (by decide)
  have k72 : c 72 < 65536 := hcy 6 (by decide)
  have k71 : c 71 < 65536 := hcy 5 (by decide)
  have p42_40 := mb _ _ y42 y40
  have p43_39 := mb _ _ y43 y39
  have p44_38 := mb _ _ y44 y38
  have p45_37 := mb _ _ y45 y37
  have p46_36 := mb _ _ y46 y36
  have p47_35 := mb _ _ y47 y35
  have p48_34 := mb _ _ y48 y34
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82] at h
  exact natEq (by fpr) (by omega) (by omega)

theorem eqP7 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (hy : ∀ i, i < 32 → c (26 + i) < 256) (hcy : ∀ k, k < 8 → c (66 + k) < 65536)
    (hd : ∀ i, i < 4 → c (74 + i) < 65536)
    (h : Expr.eval (natRow c rw) (Div.nt * Div.prodEq 7) = 0) (h82 : c 82 = 0) :
    c 42 * c 41 + c 43 * c 40 + c 44 * c 39 + c 45 * c 38 + c 46 * c 37 + c 47 * c 36 + c 48 * c 35 + c 49 * c 34 + c 57 + c 72 = c 33 + 256 * c 73 := by
  have hP' := P_val
  have mb : ∀ x y : Nat, x < 256 → y < 256 → x * y ≤ 65025 := fun x y hx hy =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)) (by decide)
  have y33 : c 33 < 256 := hy 7 (by decide)
  have y34 : c 34 < 256 := hy 8 (by decide)
  have y35 : c 35 < 256 := hy 9 (by decide)
  have y36 : c 36 < 256 := hy 10 (by decide)
  have y37 : c 37 < 256 := hy 11 (by decide)
  have y38 : c 38 < 256 := hy 12 (by decide)
  have y39 : c 39 < 256 := hy 13 (by decide)
  have y40 : c 40 < 256 := hy 14 (by decide)
  have y41 : c 41 < 256 := hy 15 (by decide)
  have y42 : c 42 < 256 := hy 16 (by decide)
  have y43 : c 43 < 256 := hy 17 (by decide)
  have y44 : c 44 < 256 := hy 18 (by decide)
  have y45 : c 45 < 256 := hy 19 (by decide)
  have y46 : c 46 < 256 := hy 20 (by decide)
  have y47 : c 47 < 256 := hy 21 (by decide)
  have y48 : c 48 < 256 := hy 22 (by decide)
  have y49 : c 49 < 256 := hy 23 (by decide)
  have y57 : c 57 < 256 := hy 31 (by decide)
  have k73 : c 73 < 65536 := hcy 7 (by decide)
  have k72 : c 72 < 65536 := hcy 6 (by decide)
  have p42_41 := mb _ _ y42 y41
  have p43_40 := mb _ _ y43 y40
  have p44_39 := mb _ _ y44 y39
  have p45_38 := mb _ _ y45 y38
  have p46_37 := mb _ _ y46 y37
  have p47_36 := mb _ _ y47 y36
  have p48_35 := mb _ _ y48 y35
  have p49_34 := mb _ _ y49 y34
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82] at h
  exact natEq (by fpr) (by omega) (by omega)

theorem eqT0 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (hy : ∀ i, i < 32 → c (26 + i) < 256) (hcy : ∀ k, k < 8 → c (66 + k) < 65536)
    (hd : ∀ i, i < 4 → c (74 + i) < 65536) (hbw : ∀ i, i < 4 → c (78 + i) ≤ 1)
    (h : Expr.eval (natRow c rw) (Div.nt * Div.ltEq 0) = 0) (h82 : c 82 = 0) :
    c 34 + 256 * c 35 + 65536 * c 78 = c 50 + 256 * c 51 + 1 + c 74 := by
  have hP' := P_val
  have mb : ∀ x y : Nat, x < 256 → y < 256 → x * y ≤ 65025 := fun x y hx hy =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)) (by decide)
  have y34 : c 34 < 256 := hy 8 (by decide)
  have y35 : c 35 < 256 := hy 9 (by decide)
  have y50 : c 50 < 256 := hy 24 (by decide)
  have y51 : c 51 < 256 := hy 25 (by decide)
  have d74 : c 74 < 65536 := hd 0 (by decide)
  have w78 : c 78 ≤ 1 := hbw 0 (by decide)
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82] at h
  exact natEq (by fpr) (by omega) (by omega)

theorem eqT1 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (hy : ∀ i, i < 32 → c (26 + i) < 256) (hcy : ∀ k, k < 8 → c (66 + k) < 65536)
    (hd : ∀ i, i < 4 → c (74 + i) < 65536) (hbw : ∀ i, i < 4 → c (78 + i) ≤ 1)
    (h : Expr.eval (natRow c rw) (Div.nt * Div.ltEq 1) = 0) (h82 : c 82 = 0) :
    c 36 + 256 * c 37 + 65536 * c 79 = c 52 + 256 * c 53 + c 78 + c 75 := by
  have hP' := P_val
  have mb : ∀ x y : Nat, x < 256 → y < 256 → x * y ≤ 65025 := fun x y hx hy =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)) (by decide)
  have y36 : c 36 < 256 := hy 10 (by decide)
  have y37 : c 37 < 256 := hy 11 (by decide)
  have y52 : c 52 < 256 := hy 26 (by decide)
  have y53 : c 53 < 256 := hy 27 (by decide)
  have d75 : c 75 < 65536 := hd 1 (by decide)
  have w79 : c 79 ≤ 1 := hbw 1 (by decide)
  have w78 : c 78 ≤ 1 := hbw 0 (by decide)
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82] at h
  exact natEq (by fpr) (by omega) (by omega)

theorem eqT2 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (hy : ∀ i, i < 32 → c (26 + i) < 256) (hcy : ∀ k, k < 8 → c (66 + k) < 65536)
    (hd : ∀ i, i < 4 → c (74 + i) < 65536) (hbw : ∀ i, i < 4 → c (78 + i) ≤ 1)
    (h : Expr.eval (natRow c rw) (Div.nt * Div.ltEq 2) = 0) (h82 : c 82 = 0) :
    c 38 + 256 * c 39 + 65536 * c 80 = c 54 + 256 * c 55 + c 79 + c 76 := by
  have hP' := P_val
  have mb : ∀ x y : Nat, x < 256 → y < 256 → x * y ≤ 65025 := fun x y hx hy =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)) (by decide)
  have y38 : c 38 < 256 := hy 12 (by decide)
  have y39 : c 39 < 256 := hy 13 (by decide)
  have y54 : c 54 < 256 := hy 28 (by decide)
  have y55 : c 55 < 256 := hy 29 (by decide)
  have d76 : c 76 < 65536 := hd 2 (by decide)
  have w80 : c 80 ≤ 1 := hbw 2 (by decide)
  have w79 : c 79 ≤ 1 := hbw 1 (by decide)
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82] at h
  exact natEq (by fpr) (by omega) (by omega)

theorem eqT3 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (hy : ∀ i, i < 32 → c (26 + i) < 256) (hcy : ∀ k, k < 8 → c (66 + k) < 65536)
    (hd : ∀ i, i < 4 → c (74 + i) < 65536) (hbw : ∀ i, i < 4 → c (78 + i) ≤ 1)
    (h : Expr.eval (natRow c rw) (Div.nt * Div.ltEq 3) = 0) (h82 : c 82 = 0) :
    c 40 + 256 * c 41 + 65536 * c 81 = c 56 + 256 * c 57 + c 80 + c 77 := by
  have hP' := P_val
  have mb : ∀ x y : Nat, x < 256 → y < 256 → x * y ≤ 65025 := fun x y hx hy =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)) (by decide)
  have y40 : c 40 < 256 := hy 14 (by decide)
  have y41 : c 41 < 256 := hy 15 (by decide)
  have y56 : c 56 < 256 := hy 30 (by decide)
  have y57 : c 57 < 256 := hy 31 (by decide)
  have d77 : c 77 < 65536 := hd 3 (by decide)
  have w81 : c 81 ≤ 1 := hbw 3 (by decide)
  have w80 : c 80 ≤ 1 := hbw 2 (by decide)
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82] at h
  exact natEq (by fpr) (by omega) (by omega)

theorem eqZ8 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (hy : ∀ i, i < 32 → c (26 + i) < 256) (hcy : ∀ k, k < 8 → c (66 + k) < 65536)
    (hd : ∀ i, i < 4 → c (74 + i) < 65536)
    (h : Expr.eval (natRow c rw) (Div.nt * v Div.is64 * Div.conv 8) = 0) (h82 : c 82 = 0) (h9 : c 9 = 1) :
    c 43 * c 41 + c 44 * c 40 + c 45 * c 39 + c 46 * c 38 + c 47 * c 37 + c 48 * c 36 + c 49 * c 35 = 0 := by
  have hP' := P_val
  have mb : ∀ x y : Nat, x < 256 → y < 256 → x * y ≤ 65025 := fun x y hx hy =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)) (by decide)
  have y35 : c 35 < 256 := hy 9 (by decide)
  have y36 : c 36 < 256 := hy 10 (by decide)
  have y37 : c 37 < 256 := hy 11 (by decide)
  have y38 : c 38 < 256 := hy 12 (by decide)
  have y39 : c 39 < 256 := hy 13 (by decide)
  have y40 : c 40 < 256 := hy 14 (by decide)
  have y41 : c 41 < 256 := hy 15 (by decide)
  have y43 : c 43 < 256 := hy 17 (by decide)
  have y44 : c 44 < 256 := hy 18 (by decide)
  have y45 : c 45 < 256 := hy 19 (by decide)
  have y46 : c 46 < 256 := hy 20 (by decide)
  have y47 : c 47 < 256 := hy 21 (by decide)
  have y48 : c 48 < 256 := hy 22 (by decide)
  have y49 : c 49 < 256 := hy 23 (by decide)
  have p43_41 := mb _ _ y43 y41
  have p44_40 := mb _ _ y44 y40
  have p45_39 := mb _ _ y45 y39
  have p46_38 := mb _ _ y46 y38
  have p47_37 := mb _ _ y47 y37
  have p48_36 := mb _ _ y48 y36
  have p49_35 := mb _ _ y49 y35
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82, h9] at h
  exact natEq (L := c 43 * c 41 + c 44 * c 40 + c 45 * c 39 + c 46 * c 38 + c 47 * c 37 + c 48 * c 36 + c 49 * c 35) (R := 0) (by fpr) (by omega) (by omega)

theorem eqZ9 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (hy : ∀ i, i < 32 → c (26 + i) < 256) (hcy : ∀ k, k < 8 → c (66 + k) < 65536)
    (hd : ∀ i, i < 4 → c (74 + i) < 65536)
    (h : Expr.eval (natRow c rw) (Div.nt * v Div.is64 * Div.conv 9) = 0) (h82 : c 82 = 0) (h9 : c 9 = 1) :
    c 44 * c 41 + c 45 * c 40 + c 46 * c 39 + c 47 * c 38 + c 48 * c 37 + c 49 * c 36 = 0 := by
  have hP' := P_val
  have mb : ∀ x y : Nat, x < 256 → y < 256 → x * y ≤ 65025 := fun x y hx hy =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)) (by decide)
  have y36 : c 36 < 256 := hy 10 (by decide)
  have y37 : c 37 < 256 := hy 11 (by decide)
  have y38 : c 38 < 256 := hy 12 (by decide)
  have y39 : c 39 < 256 := hy 13 (by decide)
  have y40 : c 40 < 256 := hy 14 (by decide)
  have y41 : c 41 < 256 := hy 15 (by decide)
  have y44 : c 44 < 256 := hy 18 (by decide)
  have y45 : c 45 < 256 := hy 19 (by decide)
  have y46 : c 46 < 256 := hy 20 (by decide)
  have y47 : c 47 < 256 := hy 21 (by decide)
  have y48 : c 48 < 256 := hy 22 (by decide)
  have y49 : c 49 < 256 := hy 23 (by decide)
  have p44_41 := mb _ _ y44 y41
  have p45_40 := mb _ _ y45 y40
  have p46_39 := mb _ _ y46 y39
  have p47_38 := mb _ _ y47 y38
  have p48_37 := mb _ _ y48 y37
  have p49_36 := mb _ _ y49 y36
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82, h9] at h
  exact natEq (L := c 44 * c 41 + c 45 * c 40 + c 46 * c 39 + c 47 * c 38 + c 48 * c 37 + c 49 * c 36) (R := 0) (by fpr) (by omega) (by omega)

theorem eqZ10 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (hy : ∀ i, i < 32 → c (26 + i) < 256) (hcy : ∀ k, k < 8 → c (66 + k) < 65536)
    (hd : ∀ i, i < 4 → c (74 + i) < 65536)
    (h : Expr.eval (natRow c rw) (Div.nt * v Div.is64 * Div.conv 10) = 0) (h82 : c 82 = 0) (h9 : c 9 = 1) :
    c 45 * c 41 + c 46 * c 40 + c 47 * c 39 + c 48 * c 38 + c 49 * c 37 = 0 := by
  have hP' := P_val
  have mb : ∀ x y : Nat, x < 256 → y < 256 → x * y ≤ 65025 := fun x y hx hy =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)) (by decide)
  have y37 : c 37 < 256 := hy 11 (by decide)
  have y38 : c 38 < 256 := hy 12 (by decide)
  have y39 : c 39 < 256 := hy 13 (by decide)
  have y40 : c 40 < 256 := hy 14 (by decide)
  have y41 : c 41 < 256 := hy 15 (by decide)
  have y45 : c 45 < 256 := hy 19 (by decide)
  have y46 : c 46 < 256 := hy 20 (by decide)
  have y47 : c 47 < 256 := hy 21 (by decide)
  have y48 : c 48 < 256 := hy 22 (by decide)
  have y49 : c 49 < 256 := hy 23 (by decide)
  have p45_41 := mb _ _ y45 y41
  have p46_40 := mb _ _ y46 y40
  have p47_39 := mb _ _ y47 y39
  have p48_38 := mb _ _ y48 y38
  have p49_37 := mb _ _ y49 y37
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82, h9] at h
  exact natEq (L := c 45 * c 41 + c 46 * c 40 + c 47 * c 39 + c 48 * c 38 + c 49 * c 37) (R := 0) (by fpr) (by omega) (by omega)

theorem eqZ11 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (hy : ∀ i, i < 32 → c (26 + i) < 256) (hcy : ∀ k, k < 8 → c (66 + k) < 65536)
    (hd : ∀ i, i < 4 → c (74 + i) < 65536)
    (h : Expr.eval (natRow c rw) (Div.nt * v Div.is64 * Div.conv 11) = 0) (h82 : c 82 = 0) (h9 : c 9 = 1) :
    c 46 * c 41 + c 47 * c 40 + c 48 * c 39 + c 49 * c 38 = 0 := by
  have hP' := P_val
  have mb : ∀ x y : Nat, x < 256 → y < 256 → x * y ≤ 65025 := fun x y hx hy =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)) (by decide)
  have y38 : c 38 < 256 := hy 12 (by decide)
  have y39 : c 39 < 256 := hy 13 (by decide)
  have y40 : c 40 < 256 := hy 14 (by decide)
  have y41 : c 41 < 256 := hy 15 (by decide)
  have y46 : c 46 < 256 := hy 20 (by decide)
  have y47 : c 47 < 256 := hy 21 (by decide)
  have y48 : c 48 < 256 := hy 22 (by decide)
  have y49 : c 49 < 256 := hy 23 (by decide)
  have p46_41 := mb _ _ y46 y41
  have p47_40 := mb _ _ y47 y40
  have p48_39 := mb _ _ y48 y39
  have p49_38 := mb _ _ y49 y38
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82, h9] at h
  exact natEq (L := c 46 * c 41 + c 47 * c 40 + c 48 * c 39 + c 49 * c 38) (R := 0) (by fpr) (by omega) (by omega)

theorem eqZ12 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (hy : ∀ i, i < 32 → c (26 + i) < 256) (hcy : ∀ k, k < 8 → c (66 + k) < 65536)
    (hd : ∀ i, i < 4 → c (74 + i) < 65536)
    (h : Expr.eval (natRow c rw) (Div.nt * v Div.is64 * Div.conv 12) = 0) (h82 : c 82 = 0) (h9 : c 9 = 1) :
    c 47 * c 41 + c 48 * c 40 + c 49 * c 39 = 0 := by
  have hP' := P_val
  have mb : ∀ x y : Nat, x < 256 → y < 256 → x * y ≤ 65025 := fun x y hx hy =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)) (by decide)
  have y39 : c 39 < 256 := hy 13 (by decide)
  have y40 : c 40 < 256 := hy 14 (by decide)
  have y41 : c 41 < 256 := hy 15 (by decide)
  have y47 : c 47 < 256 := hy 21 (by decide)
  have y48 : c 48 < 256 := hy 22 (by decide)
  have y49 : c 49 < 256 := hy 23 (by decide)
  have p47_41 := mb _ _ y47 y41
  have p48_40 := mb _ _ y48 y40
  have p49_39 := mb _ _ y49 y39
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82, h9] at h
  exact natEq (L := c 47 * c 41 + c 48 * c 40 + c 49 * c 39) (R := 0) (by fpr) (by omega) (by omega)

theorem eqZ13 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (hy : ∀ i, i < 32 → c (26 + i) < 256) (hcy : ∀ k, k < 8 → c (66 + k) < 65536)
    (hd : ∀ i, i < 4 → c (74 + i) < 65536)
    (h : Expr.eval (natRow c rw) (Div.nt * v Div.is64 * Div.conv 13) = 0) (h82 : c 82 = 0) (h9 : c 9 = 1) :
    c 48 * c 41 + c 49 * c 40 = 0 := by
  have hP' := P_val
  have mb : ∀ x y : Nat, x < 256 → y < 256 → x * y ≤ 65025 := fun x y hx hy =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)) (by decide)
  have y40 : c 40 < 256 := hy 14 (by decide)
  have y41 : c 41 < 256 := hy 15 (by decide)
  have y48 : c 48 < 256 := hy 22 (by decide)
  have y49 : c 49 < 256 := hy 23 (by decide)
  have p48_41 := mb _ _ y48 y41
  have p49_40 := mb _ _ y49 y40
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82, h9] at h
  exact natEq (L := c 48 * c 41 + c 49 * c 40) (R := 0) (by fpr) (by omega) (by omega)

theorem eqZ14 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (hy : ∀ i, i < 32 → c (26 + i) < 256) (hcy : ∀ k, k < 8 → c (66 + k) < 65536)
    (hd : ∀ i, i < 4 → c (74 + i) < 65536)
    (h : Expr.eval (natRow c rw) (Div.nt * v Div.is64 * Div.conv 14) = 0) (h82 : c 82 = 0) (h9 : c 9 = 1) :
    c 49 * c 41 = 0 := by
  have hP' := P_val
  have mb : ∀ x y : Nat, x < 256 → y < 256 → x * y ≤ 65025 := fun x y hx hy =>
    Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)) (by decide)
  have y41 : c 41 < 256 := hy 15 (by decide)
  have y49 : c 49 < 256 := hy 23 (by decide)
  have p49_41 := mb _ _ y49 y41
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82, h9] at h
  exact natEq (L := c 49 * c 41) (R := 0) (by fpr) (by omega) (by omega)

theorem eqBw3 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (h : Expr.eval (natRow c rw) (Div.nt * v (Div.bw + 3)) = 0) (h82 : c 82 = 0) : c 81 = 0 := by
  have hP' := P_val
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82] at h; exact natEq (by fpr) (hP 81) (by omega)

theorem eqCy7 (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (h : Expr.eval (natRow c rw) (Div.nt * v Div.is64 * v (Div.cy + 7)) = 0) (h82 : c 82 = 0) (h9 : c 9 = 1) :
    c 73 = 0 := by
  have hP' := P_val
  simp (config := {decide := true}) only [Div.nt, Div.prodEq, Div.conv, Div.cIn, Div.ltEq, List.range, List.range.loop, List.filterMap_cons,
      List.filterMap_nil, List.foldl_cons, List.foldl_nil, Expr.eval_mul', Expr.eval_sub', Expr.eval_add',
      Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Div.QB, Div.BB, Div.RB, Div.AB, Div.cy, Div.bw, Div.dd, Div.tz,
      Div.is64, B16, L_eval, act_eval hact, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceLeDiff, Nat.reduceLT, and_true, and_false, true_and, false_and] at h
  rw [h82, h9] at h; exact natEq (by fpr) (hP 73) (by omega)
/-- The DIV chip: from the constraints of an active row and the range facts its lookups and consumed
messages give, the row computes `Num.binop` (div_s, div_u, rem_s, rem_u) or the op traps. -/
theorem div_sound (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P)
    (hc : ∀ e ∈ Div.constraints, e.eval (natRow c rw) = 0)
    (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (ha : ∀ i, i < 4 → c (10 + i) < 65536) (hb : ∀ i, i < 4 → c (16 + i) < 65536)
    (hra : (2 * c 23) % P < 65536) (hrb : (2 * c 25) % P < 65536) (hrq : (2 * c 85) % P < 65536)
    (hbytes : ∀ i, i < 32 → c (26 + i) < 256) (hcy : ∀ k, k < 8 → c (66 + k) < 65536)
    (hd : ∀ i, i < 4 → c (74 + i) < 65536) (hres : ∀ i, i < 4 → c (87 + i) < 65536) :
    (c 9 = 0 ∨ c 9 = 1) ∧
    (c 9 = 0 → c 12 = 0 ∧ c 13 = 0 ∧ c 18 = 0 ∧ c 19 = 0 ∧ c 89 = 0 ∧ c 90 = 0) ∧
    c 82 + c 86 ≤ 1 ∧
    (c 82 + c 86 = 1 → Num.binop (32 + 32 * c 9) (3 + c 6 + 2 * c 7 + 3 * c 8)
        (val4 (c 10) (c 11) (c 12) (c 13)) (val4 (c 16) (c 17) (c 18) (c 19)) = none) ∧
    (c 82 + c 86 = 0 → Num.binop (32 + 32 * c 9) (3 + c 6 + 2 * c 7 + 3 * c 8)
        (val4 (c 10) (c 11) (c 12) (c 13)) (val4 (c 16) (c 17) (c 18) (c 19)) =
        some (val4 (c 87) (c 88) (c 89) (c 90))) := by
  have hP' := P_val
  simp only [Div.constraints, List.forall_mem_append, List.forall_mem_flatMap, List.forall_mem_map,
    List.mem_range, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, List.forall_mem_cons,
    List.forall_mem_nil, and_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩ := hc
  obtain ⟨g2, g3, g4, g5, g6, g7, g8, gtA, gtB, gza2, gza3, gzb2, gzb3, gzr2, gzr3, g16, gtQ⟩ := h2
  obtain ⟨t1, t2, t3⟩ := h10
  -- range facts

  have y26 : c 26 < 256 := hbytes 0 (by decide)
  have y27 : c 27 < 256 := hbytes 1 (by decide)
  have y28 : c 28 < 256 := hbytes 2 (by decide)
  have y29 : c 29 < 256 := hbytes 3 (by decide)
  have y30 : c 30 < 256 := hbytes 4 (by decide)
  have y31 : c 31 < 256 := hbytes 5 (by decide)
  have y32 : c 32 < 256 := hbytes 6 (by decide)
  have y33 : c 33 < 256 := hbytes 7 (by decide)
  have y34 : c 34 < 256 := hbytes 8 (by decide)
  have y35 : c 35 < 256 := hbytes 9 (by decide)
  have y36 : c 36 < 256 := hbytes 10 (by decide)
  have y37 : c 37 < 256 := hbytes 11 (by decide)
  have y38 : c 38 < 256 := hbytes 12 (by decide)
  have y39 : c 39 < 256 := hbytes 13 (by decide)
  have y40 : c 40 < 256 := hbytes 14 (by decide)
  have y41 : c 41 < 256 := hbytes 15 (by decide)
  have y42 : c 42 < 256 := hbytes 16 (by decide)
  have y43 : c 43 < 256 := hbytes 17 (by decide)
  have y44 : c 44 < 256 := hbytes 18 (by decide)
  have y45 : c 45 < 256 := hbytes 19 (by decide)
  have y46 : c 46 < 256 := hbytes 20 (by decide)
  have y47 : c 47 < 256 := hbytes 21 (by decide)
  have y48 : c 48 < 256 := hbytes 22 (by decide)
  have y49 : c 49 < 256 := hbytes 23 (by decide)
  have y50 : c 50 < 256 := hbytes 24 (by decide)
  have y51 : c 51 < 256 := hbytes 25 (by decide)
  have y52 : c 52 < 256 := hbytes 26 (by decide)
  have y53 : c 53 < 256 := hbytes 27 (by decide)
  have y54 : c 54 < 256 := hbytes 28 (by decide)
  have y55 : c 55 < 256 := hbytes 29 (by decide)
  have y56 : c 56 < 256 := hbytes 30 (by decide)
  have y57 : c 57 < 256 := hbytes 31 (by decide)
  have a10 : c 10 < 65536 := ha 0 (by decide)
  have b16 : c 16 < 65536 := hb 0 (by decide)
  have d74 : c 74 < 65536 := hd 0 (by decide)
  have r87 : c 87 < 65536 := hres 0 (by decide)
  have a11 : c 11 < 65536 := ha 1 (by decide)
  have b17 : c 17 < 65536 := hb 1 (by decide)
  have d75 : c 75 < 65536 := hd 1 (by decide)
  have r88 : c 88 < 65536 := hres 1 (by decide)
  have a12 : c 12 < 65536 := ha 2 (by decide)
  have b18 : c 18 < 65536 := hb 2 (by decide)
  have d76 : c 76 < 65536 := hd 2 (by decide)
  have r89 : c 89 < 65536 := hres 2 (by decide)
  have a13 : c 13 < 65536 := ha 3 (by decide)
  have b19 : c 19 < 65536 := hb 3 (by decide)
  have d77 : c 77 < 65536 := hd 3 (by decide)
  have r90 : c 90 < 65536 := hres 3 (by decide)
  have k66 : c 66 < 65536 := hcy 0 (by decide)
  have k67 : c 67 < 65536 := hcy 1 (by decide)
  have k68 : c 68 < 65536 := hcy 2 (by decide)
  have k69 : c 69 < 65536 := hcy 3 (by decide)
  have k70 : c 70 < 65536 := hcy 4 (by decide)
  have k71 : c 71 < 65536 := hcy 5 (by decide)
  have k72 : c 72 < 65536 := hcy 6 (by decide)
  have k73 : c 73 < 65536 := hcy 7 (by decide)
  -- bits
  have b9 : c 9 ≤ 1 := bit_of hP g6
  have bA : c 22 ≤ 1 := bit_of hP g7
  have bB : c 24 ≤ 1 := bit_of hP g8
  have bQ : c 84 ≤ 1 := bit_of hP g16
  have kca : ∀ i, i < 4 → c (58 + i) ≤ 1 := fun i hi => bit_of hP (h4 i hi)
  have q58 : c 58 ≤ 1 := kca 0 (by decide)
  have q59 : c 59 ≤ 1 := kca 1 (by decide)
  have q60 : c 60 ≤ 1 := kca 2 (by decide)
  have q61 : c 61 ≤ 1 := kca 3 (by decide)
  have kcb : ∀ i, i < 4 → c (62 + i) ≤ 1 := fun i hi => bit_of hP (h5 i hi)
  have q62 : c 62 ≤ 1 := kcb 0 (by decide)
  have q63 : c 63 ≤ 1 := kcb 1 (by decide)
  have q64 : c 64 ≤ 1 := kcb 2 (by decide)
  have q65 : c 65 ≤ 1 := kcb 3 (by decide)
  have kcr : ∀ i, i < 4 → c (91 + i) ≤ 1 := fun i hi => bit_of hP (h6 i hi)
  have q91 : c 91 ≤ 1 := kcr 0 (by decide)
  have q92 : c 92 ≤ 1 := kcr 1 (by decide)
  have q93 : c 93 ≤ 1 := kcr 2 (by decide)
  have q94 : c 94 ≤ 1 := kcr 3 (by decide)
  have kbw : ∀ i, i < 4 → c (78 + i) ≤ 1 := fun i hi => bit_of hP (h7 i hi)
  have q78 : c 78 ≤ 1 := kbw 0 (by decide)
  have q79 : c 79 ≤ 1 := kbw 1 (by decide)
  have q80 : c 80 ≤ 1 := kbw 2 (by decide)
  have q81 : c 81 ≤ 1 := kbw 3 (by decide)
  -- pinned top limbs
  have tA := pin_of hP (sel_eval c rw (v (Div.a + 3)) (v (Div.a + 1)) (c 13) (c 11) b9 rfl rfl)
    (by split <;> omega) bA hra gtA
  have tB := pin_of hP (sel_eval c rw (v (Div.b + 3)) (v (Div.b + 1)) (c 19) (c 17) b9 rfl rfl)
    (by split <;> omega) bB hrb gtB
  have tQ := pin_of hP (sel_eval c rw (Div.L Div.QB 3) (Div.L Div.QB 1) _ _ b9 (L_eval c rw Div.QB 3)
    (L_eval c rw Div.QB 1)) (by simp only [Div.QB, Nat.reduceMul, Nat.reduceAdd]; split <;> omega) bQ hrq gtQ
  simp only [Div.QB, Nat.reduceMul, Nat.reduceAdd] at tQ
  -- the trap flags
  have TZ := tz_facts hP hact (fun i hi => by
    have := hbytes (8 + i) (by omega); rwa [show 26 + (8 + i) = 34 + i by omega] at this) t1 t2
  have TOV := tov_fact hP hact (by omega) (by omega) bA bB bQ t3
  -- negation chains
  have hsA : (c 5 + c 7) * c 22 = 0 ∨ (c 5 + c 7) * c 22 = 1 := by
    rcases (show c 22 = 0 ∨ c 22 = 1 by omega) with h | h <;> rw [h] <;> omega
  have hsB : (c 5 + c 7) * c 24 = 0 ∨ (c 5 + c 7) * c 24 = 1 := by
    rcases (show c 24 = 0 ∨ c 24 = 1 by omega) with h | h <;> rw [h] <;> omega
  have eA : Div.sa.eval (natRow c rw) = (((c 5 + c 7) * c 22 : Nat) : F) := by
    simp only [Div.sa, Div.signed, v, Div.fDivS, Div.fRemS, Div.hbA, Expr.eval_add', Expr.eval_mul', Expr.eval_col,
      natRow_cur]; fpr
  have eB : Div.sb.eval (natRow c rw) = (((c 5 + c 7) * c 24 : Nat) : F) := by
    simp only [Div.sb, Div.signed, v, Div.fDivS, Div.fRemS, Div.hbB, Expr.eval_add', Expr.eval_mul', Expr.eval_col,
      natRow_cur]; fpr
  have NA := neg_chain c rw Div.sa _ (Div.L Div.AB) (fun i => v (Div.a + i))
    (fun i => c (Div.AB + 2 * i) + 256 * c (Div.AB + 2 * i + 1)) (fun i => c (Div.a + i)) Div.ca h8 eA hsA
    (fun i => L_eval c rw Div.AB i) (fun i => rfl)
    (fun i hi => by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
        simp only [Div.AB, Nat.reduceMul, Nat.reduceAdd] <;> omega)
    (fun i hi => ha i hi) kca
  have NB := neg_chain c rw Div.sb _ (Div.L Div.BB) (fun i => v (Div.b + i))
    (fun i => c (Div.BB + 2 * i) + 256 * c (Div.BB + 2 * i + 1)) (fun i => c (Div.b + i)) Div.cb h9 eB hsB
    (fun i => L_eval c rw Div.BB i) (fun i => rfl)
    (fun i hi => by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
        simp only [Div.BB, Nat.reduceMul, Nat.reduceAdd] <;> omega)
    (fun i hi => hb i hi) kcb
  simp only [Div.AB, Div.BB, Div.a, Div.b, Div.ca, Div.cb, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero,
    Nat.add_zero] at NA NB
  -- the result chain
  have hfl : (c 5 + c 6 = 1 ∧ c 7 + c 8 = 0) ∨ (c 5 + c 6 = 0 ∧ c 7 + c 8 = 1) := by omega
  have hsR : c 5 * (c 22 + c 24 - 2 * c 22 * c 24) + c 7 * c 22 = 0 ∨
      c 5 * (c 22 + c 24 - 2 * c 22 * c 24) + c 7 * c 22 = 1 := by
    rcases (show c 22 = 0 ∨ c 22 = 1 by omega) with h | h <;> rcases (show c 24 = 0 ∨ c 24 = 1 by omega) with h' | h' <;>
      rw [h, h'] <;> simp <;> omega
  have eR : Div.sres.eval (natRow c rw) = ((c 5 * (c 22 + c 24 - 2 * c 22 * c 24) + c 7 * c 22 : Nat) : F) := by
    simp only [Div.sres, v, Div.fDivS, Div.fRemS, Div.hbA, Div.hbB, Expr.eval_add', Expr.eval_sub', Expr.eval_mul',
      Expr.eval_ofNat', Expr.eval_col, natRow_cur]
    rcases (show c 22 = 0 ∨ c 22 = 1 by omega) with h | h <;> rcases (show c 24 = 0 ∨ c 24 = 1 by omega) with h' | h' <;>
      rw [h, h'] <;> simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] <;> fpr
  have NR := neg_chain c rw Div.sres _ (fun i => v (Div.res + i)) Div.X (fun i => c (Div.res + i))
    (fun i => (c 5 + c 6) * (c (Div.QB + 2 * i) + 256 * c (Div.QB + 2 * i + 1)) +
      (c 7 + c 8) * (c (Div.RB + 2 * i) + 256 * c (Div.RB + 2 * i + 1))) Div.cr h17 eR hsR (fun i => rfl)
    (fun i => by
      simp only [Div.X, Div.isDiv, Div.isRem, v, Div.fDivS, Div.fDivU, Div.fRemS, Div.fRemU, Expr.eval_add',
        Expr.eval_mul', Expr.eval_col, natRow_cur, L_eval]; fpr)
    (fun i hi => hres i hi)
    (fun i hi => by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
        rcases hfl with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [e1, e2, Div.QB, Div.RB, Nat.reduceMul, Nat.reduceAdd,
          Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add] <;> omega)
    kcr
  simp only [Div.QB, Div.RB, Div.res, Div.cr, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at NR
  -- the division equations (rows with `tz = 0`)
  have E0 := eqP0 c rw hP hact hbytes hcy hd (h11 0 (by decide))
  have E1 := eqP1 c rw hP hact hbytes hcy hd (h11 1 (by decide))
  have E2 := eqP2 c rw hP hact hbytes hcy hd (h11 2 (by decide))
  have E3 := eqP3 c rw hP hact hbytes hcy hd (h11 3 (by decide))
  have E4 := eqP4 c rw hP hact hbytes hcy hd (h11 4 (by decide))
  have E5 := eqP5 c rw hP hact hbytes hcy hd (h11 5 (by decide))
  have E6 := eqP6 c rw hP hact hbytes hcy hd (h11 6 (by decide))
  have E7 := eqP7 c rw hP hact hbytes hcy hd (h11 7 (by decide))
  have T0 := eqT0 c rw hP hact hbytes hcy hd kbw (h15 0 (by decide))
  have T1 := eqT1 c rw hP hact hbytes hcy hd kbw (h15 1 (by decide))
  have T2 := eqT2 c rw hP hact hbytes hcy hd kbw (h15 2 (by decide))
  have T3 := eqT3 c rw hP hact hbytes hcy hd kbw (h15 3 (by decide))
  have T4 := eqBw3 c rw hP hact h16
  have Z8 := eqZ8 c rw hP hact hbytes hcy hd (h14 0 (by decide))
  have Z9 := eqZ9 c rw hP hact hbytes hcy hd (h14 1 (by decide))
  have Z10 := eqZ10 c rw hP hact hbytes hcy hd (h14 2 (by decide))
  have Z11 := eqZ11 c rw hP hact hbytes hcy hd (h14 3 (by decide))
  have Z12 := eqZ12 c rw hP hact hbytes hcy hd (h14 4 (by decide))
  have Z13 := eqZ13 c rw hP hact hbytes hcy hd (h14 5 (by decide))
  have Z14 := eqZ14 c rw hP hact hbytes hcy hd (h14 6 (by decide))
  have C73 := eqCy7 c rw hP hact h12.2
  obtain ⟨tz01, tzB⟩ := TZ
  have z9 : c 9 = 0 → c 12 = 0 ∧ c 13 = 0 ∧ c 18 = 0 ∧ c 19 = 0 ∧ c 89 = 0 ∧ c 90 = 0 := fun h9 =>
    ⟨zero_of hP h9 gza2, zero_of hP h9 gza3, zero_of hP h9 gzb2, zero_of hP h9 gzb3, zero_of hP h9 gzr2,
      zero_of hP h9 gzr3⟩
  refine ⟨by omega, z9, ?_⟩
  rcases (show c 9 = 0 ∨ c 9 = 1 by omega) with h9 | h9
  · -- i32
    simp only [h9, show ((0 : Nat) = 1) = False from by decide, ite_false] at tA tB tQ
    obtain ⟨NA0, NA1, -⟩ := NA
    obtain ⟨NB0, NB1, -⟩ := NB
    obtain ⟨NR0, NR1, -⟩ := NR
    obtain ⟨za2, za3, zb2, zb3, zr2, zr3⟩ := z9 h9
    obtain ⟨u01, u02, u03, u04, u05⟩ := h3 0 (by decide)
    have zA30 : c 30 = 0 := zero_of hP h9 u01
    have zB38 : c 38 = 0 := zero_of hP h9 u02
    have zQ46 : c 46 = 0 := zero_of hP h9 u03
    have zR54 : c 54 = 0 := zero_of hP h9 u04
    have zC70 : c 70 = 0 := zero_of hP h9 u05
    obtain ⟨u11, u12, u13, u14, u15⟩ := h3 1 (by decide)
    have zA31 : c 31 = 0 := zero_of hP h9 u11
    have zB39 : c 39 = 0 := zero_of hP h9 u12
    have zQ47 : c 47 = 0 := zero_of hP h9 u13
    have zR55 : c 55 = 0 := zero_of hP h9 u14
    have zC71 : c 71 = 0 := zero_of hP h9 u15
    obtain ⟨u21, u22, u23, u24, u25⟩ := h3 2 (by decide)
    have zA32 : c 32 = 0 := zero_of hP h9 u21
    have zB40 : c 40 = 0 := zero_of hP h9 u22
    have zQ48 : c 48 = 0 := zero_of hP h9 u23
    have zR56 : c 56 = 0 := zero_of hP h9 u24
    have zC72 : c 72 = 0 := zero_of hP h9 u25
    obtain ⟨u31, u32, u33, u34, u35⟩ := h3 3 (by decide)
    have zA33 : c 33 = 0 := zero_of hP h9 u31
    have zB41 : c 41 = 0 := zero_of hP h9 u32
    have zQ49 : c 49 = 0 := zero_of hP h9 u33
    have zR57 : c 57 = 0 := zero_of hP h9 u34
    have zC73 : c 73 = 0 := zero_of hP h9 u35
    have hbW : val4 (c 16) (c 17) (c 18) (c 19) < 2 ^ 32 := by simp only [val4]; omega
    have hQW : (c 42 + 2 ^ 8 * c 43 + 2 ^ 16 * c 44 + 2 ^ 24 * c 45 + 2 ^ 32 * c 46 + 2 ^ 40 * c 47 + 2 ^ 48 * c 48 + 2 ^ 56 * c 49) < 2 ^ 32 := by omega
    have hRW : (c 50 + 2 ^ 8 * c 51 + 2 ^ 16 * c 52 + 2 ^ 24 * c 53 + 2 ^ 32 * c 54 + 2 ^ 40 * c 55 + 2 ^ 48 * c 56 + 2 ^ 56 * c 57) < 2 ^ 32 := by omega
    have hAa : c 22 = 1 ↔ 2 ^ (32 - 1) ≤ val4 (c 10) (c 11) (c 12) (c 13) := by simp only [val4, Nat.reduceSub]; omega
    have hBb' : c 24 = 1 ↔ 2 ^ (32 - 1) ≤ val4 (c 16) (c 17) (c 18) (c 19) := by simp only [val4, Nat.reduceSub]; omega
    have hQq : c 84 = 1 ↔ 2 ^ (32 - 1) ≤ (c 42 + 2 ^ 8 * c 43 + 2 ^ 16 * c 44 + 2 ^ 24 * c 45 + 2 ^ 32 * c 46 + 2 ^ 40 * c 47 + 2 ^ 48 * c 48 + 2 ^ 56 * c 49) := by simp only [Nat.reduceSub]; omega
    have hnA0 : (c 5 + c 7) * c 22 = 0 → (c 26 + 2 ^ 8 * c 27 + 2 ^ 16 * c 28 + 2 ^ 24 * c 29 + 2 ^ 32 * c 30 + 2 ^ 40 * c 31 + 2 ^ 48 * c 32 + 2 ^ 56 * c 33) = val4 (c 10) (c 11) (c 12) (c 13) := fun h => by
      obtain ⟨u0, u1⟩ := NA0 h; simp only [val4]; omega
    have hnA1 : (c 5 + c 7) * c 22 = 1 → (c 26 + 2 ^ 8 * c 27 + 2 ^ 16 * c 28 + 2 ^ 24 * c 29 + 2 ^ 32 * c 30 + 2 ^ 40 * c 31 + 2 ^ 48 * c 32 + 2 ^ 56 * c 33) + val4 (c 10) (c 11) (c 12) (c 13) = 2 ^ 32 := fun h => by
      have e : c 22 = 1 := by
        rcases (show c 22 = 0 ∨ c 22 = 1 by omega) with z | z
        · rw [z, Nat.mul_zero] at h; omega
        · exact z
      obtain ⟨u0, u1⟩ := NA1 h; simp only [val4]; omega
    have hnB0 : (c 5 + c 7) * c 24 = 0 → (c 34 + 2 ^ 8 * c 35 + 2 ^ 16 * c 36 + 2 ^ 24 * c 37 + 2 ^ 32 * c 38 + 2 ^ 40 * c 39 + 2 ^ 48 * c 40 + 2 ^ 56 * c 41) = val4 (c 16) (c 17) (c 18) (c 19) := fun h => by
      obtain ⟨u0, u1⟩ := NB0 h; simp only [val4]; omega
    have hnB1 : (c 5 + c 7) * c 24 = 1 → (c 34 + 2 ^ 8 * c 35 + 2 ^ 16 * c 36 + 2 ^ 24 * c 37 + 2 ^ 32 * c 38 + 2 ^ 40 * c 39 + 2 ^ 48 * c 40 + 2 ^ 56 * c 41) + val4 (c 16) (c 17) (c 18) (c 19) = 2 ^ 32 := fun h => by
      have e : c 24 = 1 := by
        rcases (show c 24 = 0 ∨ c 24 = 1 by omega) with z | z
        · rw [z, Nat.mul_zero] at h; omega
        · exact z
      obtain ⟨u0, u1⟩ := NB1 h; simp only [val4]; omega
    have htzB : c 82 = 1 ↔ (c 34 + 2 ^ 8 * c 35 + 2 ^ 16 * c 36 + 2 ^ 24 * c 37 + 2 ^ 32 * c 38 + 2 ^ 40 * c 39 + 2 ^ 48 * c 40 + 2 ^ 56 * c 41) = 0 := ⟨fun h => by have := tzB.mp h; omega, fun h => tzB.mpr (by omega)⟩
    have hdiv : c 82 = 0 → (c 42 + 2 ^ 8 * c 43 + 2 ^ 16 * c 44 + 2 ^ 24 * c 45 + 2 ^ 32 * c 46 + 2 ^ 40 * c 47 + 2 ^ 48 * c 48 + 2 ^ 56 * c 49) * (c 34 + 2 ^ 8 * c 35 + 2 ^ 16 * c 36 + 2 ^ 24 * c 37 + 2 ^ 32 * c 38 + 2 ^ 40 * c 39 + 2 ^ 48 * c 40 + 2 ^ 56 * c 41) + (c 50 + 2 ^ 8 * c 51 + 2 ^ 16 * c 52 + 2 ^ 24 * c 53 + 2 ^ 32 * c 54 + 2 ^ 40 * c 55 + 2 ^ 48 * c 56 + 2 ^ 56 * c 57) = (c 26 + 2 ^ 8 * c 27 + 2 ^ 16 * c 28 + 2 ^ 24 * c 29 + 2 ^ 32 * c 30 + 2 ^ 40 * c 31 + 2 ^ 48 * c 32 + 2 ^ 56 * c 33) ∧ (c 50 + 2 ^ 8 * c 51 + 2 ^ 16 * c 52 + 2 ^ 24 * c 53 + 2 ^ 32 * c 54 + 2 ^ 40 * c 55 + 2 ^ 48 * c 56 + 2 ^ 56 * c 57) < (c 34 + 2 ^ 8 * c 35 + 2 ^ 16 * c 36 + 2 ^ 24 * c 37 + 2 ^ 32 * c 38 + 2 ^ 40 * c 39 + 2 ^ 48 * c 40 + 2 ^ 56 * c 41) := fun h82 =>
      ⟨div8_key (c 42) (c 43) (c 44) (c 45) (c 46) (c 47) (c 48) (c 49) (c 34) (c 35) (c 36) (c 37) (c 38) (c 39) (c 40) (c 41) (c 50) (c 51) (c 52) (c 53) (c 54) (c 55) (c 56) (c 57) (c 26) (c 27) (c 28) (c 29) (c 30) (c 31) (c 32) (c 33) (c 66) (c 67) (c 68) (c 69) (c 70) (c 71) (c 72)
        (E0 h82) (E1 h82) (E2 h82) (E3 h82) (E4 h82) (E5 h82) (E6 h82) (by have := E7 h82; omega)
        (by simp only [zQ46, zQ47, zQ48, zQ49, zB38, zB39, zB40, zB41, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]) (by simp only [zQ46, zQ47, zQ48, zQ49, zB38, zB39, zB40, zB41, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]) (by simp only [zQ46, zQ47, zQ48, zQ49, zB38, zB39, zB40, zB41, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]) (by simp only [zQ46, zQ47, zQ48, zQ49, zB38, zB39, zB40, zB41, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]) (by simp only [zQ46, zQ47, zQ48, zQ49, zB38, zB39, zB40, zB41, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]) (by simp only [zQ46, zQ47, zQ48, zQ49, zB38, zB39, zB40, zB41, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]) (by simp only [zQ46, zQ47, zQ48, zQ49, zB38, zB39, zB40, zB41, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]),
       by have := T0 h82; have := T1 h82; have := T2 h82; have := T3 h82; have := T4 h82; omega⟩
    have hr0 : c 5 * (c 22 + c 24 - 2 * c 22 * c 24) + c 7 * c 22 = 0 → val4 (c 87) (c 88) (c 89) (c 90) = (c 5 + c 6) * (c 42 + 2 ^ 8 * c 43 + 2 ^ 16 * c 44 + 2 ^ 24 * c 45 + 2 ^ 32 * c 46 + 2 ^ 40 * c 47 + 2 ^ 48 * c 48 + 2 ^ 56 * c 49) + (c 7 + c 8) * (c 50 + 2 ^ 8 * c 51 + 2 ^ 16 * c 52 + 2 ^ 24 * c 53 + 2 ^ 32 * c 54 + 2 ^ 40 * c 55 + 2 ^ 48 * c 56 + 2 ^ 56 * c 57) := fun h => by
      obtain ⟨u0, u1⟩ := NR0 h; rcases hfl with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [e1, e2, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add, val4] at u0 u1 ⊢ <;> omega
    have hr1 : c 5 * (c 22 + c 24 - 2 * c 22 * c 24) + c 7 * c 22 = 1 → val4 (c 87) (c 88) (c 89) (c 90) = (2 ^ 32 - ((c 5 + c 6) * (c 42 + 2 ^ 8 * c 43 + 2 ^ 16 * c 44 + 2 ^ 24 * c 45 + 2 ^ 32 * c 46 + 2 ^ 40 * c 47 + 2 ^ 48 * c 48 + 2 ^ 56 * c 49) + (c 7 + c 8) * (c 50 + 2 ^ 8 * c 51 + 2 ^ 16 * c 52 + 2 ^ 24 * c 53 + 2 ^ 32 * c 54 + 2 ^ 40 * c 55 + 2 ^ 48 * c 56 + 2 ^ 56 * c 57))) % 2 ^ 32 := fun h => by
      obtain ⟨u0, u1⟩ := NR1 h; rcases hfl with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [e1, e2, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add, val4] at u0 u1 ⊢ <;> omega
    have X := assemble 32 (val4 (c 10) (c 11) (c 12) (c 13)) (val4 (c 16) (c 17) (c 18) (c 19)) (c 26 + 2 ^ 8 * c 27 + 2 ^ 16 * c 28 + 2 ^ 24 * c 29 + 2 ^ 32 * c 30 + 2 ^ 40 * c 31 + 2 ^ 48 * c 32 + 2 ^ 56 * c 33) (c 34 + 2 ^ 8 * c 35 + 2 ^ 16 * c 36 + 2 ^ 24 * c 37 + 2 ^ 32 * c 38 + 2 ^ 40 * c 39 + 2 ^ 48 * c 40 + 2 ^ 56 * c 41) (c 42 + 2 ^ 8 * c 43 + 2 ^ 16 * c 44 + 2 ^ 24 * c 45 + 2 ^ 32 * c 46 + 2 ^ 40 * c 47 + 2 ^ 48 * c 48 + 2 ^ 56 * c 49) (c 50 + 2 ^ 8 * c 51 + 2 ^ 16 * c 52 + 2 ^ 24 * c 53 + 2 ^ 32 * c 54 + 2 ^ 40 * c 55 + 2 ^ 48 * c 56 + 2 ^ 56 * c 57) (val4 (c 87) (c 88) (c 89) (c 90))
      (c 5) (c 6) (c 7) (c 8) (c 22) (c 24) (c 84) (c 82) (c 86) (by decide) (by omega) (by omega) (by omega)
      (by omega) tz01 hbW hQW hRW hAa hBb' hQq hnA0 hnA1 hnB0 hnB1 htzB TOV hdiv hr0 hr1
    rw [show 32 + 32 * c 9 = 32 by omega]
    exact X
  · -- i64
    simp only [h9, ite_true] at tA tB tQ
    obtain ⟨NA0, NA1, NA2⟩ := NA; obtain ⟨NA20, NA21⟩ := NA2 h9
    obtain ⟨NB0, NB1, NB2⟩ := NB; obtain ⟨NB20, NB21⟩ := NB2 h9
    obtain ⟨NR0, NR1, NR2⟩ := NR; obtain ⟨NR20, NR21⟩ := NR2 h9
    have hbW : val4 (c 16) (c 17) (c 18) (c 19) < 2 ^ 64 := by simp only [val4]; omega
    have hQW : (c 42 + 2 ^ 8 * c 43 + 2 ^ 16 * c 44 + 2 ^ 24 * c 45 + 2 ^ 32 * c 46 + 2 ^ 40 * c 47 + 2 ^ 48 * c 48 + 2 ^ 56 * c 49) < 2 ^ 64 := by omega
    have hRW : (c 50 + 2 ^ 8 * c 51 + 2 ^ 16 * c 52 + 2 ^ 24 * c 53 + 2 ^ 32 * c 54 + 2 ^ 40 * c 55 + 2 ^ 48 * c 56 + 2 ^ 56 * c 57) < 2 ^ 64 := by omega
    have hAa : c 22 = 1 ↔ 2 ^ (64 - 1) ≤ val4 (c 10) (c 11) (c 12) (c 13) := by simp only [val4, Nat.reduceSub]; omega
    have hBb' : c 24 = 1 ↔ 2 ^ (64 - 1) ≤ val4 (c 16) (c 17) (c 18) (c 19) := by simp only [val4, Nat.reduceSub]; omega
    have hQq : c 84 = 1 ↔ 2 ^ (64 - 1) ≤ (c 42 + 2 ^ 8 * c 43 + 2 ^ 16 * c 44 + 2 ^ 24 * c 45 + 2 ^ 32 * c 46 + 2 ^ 40 * c 47 + 2 ^ 48 * c 48 + 2 ^ 56 * c 49) := by simp only [Nat.reduceSub]; omega
    have hnA0 : (c 5 + c 7) * c 22 = 0 → (c 26 + 2 ^ 8 * c 27 + 2 ^ 16 * c 28 + 2 ^ 24 * c 29 + 2 ^ 32 * c 30 + 2 ^ 40 * c 31 + 2 ^ 48 * c 32 + 2 ^ 56 * c 33) = val4 (c 10) (c 11) (c 12) (c 13) := fun h => by
      obtain ⟨u0, u1⟩ := NA0 h; obtain ⟨u2, u3⟩ := NA20 h; simp only [val4]; omega
    have hnA1 : (c 5 + c 7) * c 22 = 1 → (c 26 + 2 ^ 8 * c 27 + 2 ^ 16 * c 28 + 2 ^ 24 * c 29 + 2 ^ 32 * c 30 + 2 ^ 40 * c 31 + 2 ^ 48 * c 32 + 2 ^ 56 * c 33) + val4 (c 10) (c 11) (c 12) (c 13) = 2 ^ 64 := fun h => by
      have e : c 22 = 1 := by
        rcases (show c 22 = 0 ∨ c 22 = 1 by omega) with z | z
        · rw [z, Nat.mul_zero] at h; omega
        · exact z
      obtain ⟨u0, u1⟩ := NA1 h; obtain ⟨u2, u3⟩ := NA21 h; simp only [val4]; omega
    have hnB0 : (c 5 + c 7) * c 24 = 0 → (c 34 + 2 ^ 8 * c 35 + 2 ^ 16 * c 36 + 2 ^ 24 * c 37 + 2 ^ 32 * c 38 + 2 ^ 40 * c 39 + 2 ^ 48 * c 40 + 2 ^ 56 * c 41) = val4 (c 16) (c 17) (c 18) (c 19) := fun h => by
      obtain ⟨u0, u1⟩ := NB0 h; obtain ⟨u2, u3⟩ := NB20 h; simp only [val4]; omega
    have hnB1 : (c 5 + c 7) * c 24 = 1 → (c 34 + 2 ^ 8 * c 35 + 2 ^ 16 * c 36 + 2 ^ 24 * c 37 + 2 ^ 32 * c 38 + 2 ^ 40 * c 39 + 2 ^ 48 * c 40 + 2 ^ 56 * c 41) + val4 (c 16) (c 17) (c 18) (c 19) = 2 ^ 64 := fun h => by
      have e : c 24 = 1 := by
        rcases (show c 24 = 0 ∨ c 24 = 1 by omega) with z | z
        · rw [z, Nat.mul_zero] at h; omega
        · exact z
      obtain ⟨u0, u1⟩ := NB1 h; obtain ⟨u2, u3⟩ := NB21 h; simp only [val4]; omega
    have htzB : c 82 = 1 ↔ (c 34 + 2 ^ 8 * c 35 + 2 ^ 16 * c 36 + 2 ^ 24 * c 37 + 2 ^ 32 * c 38 + 2 ^ 40 * c 39 + 2 ^ 48 * c 40 + 2 ^ 56 * c 41) = 0 := ⟨fun h => by have := tzB.mp h; omega, fun h => tzB.mpr (by omega)⟩
    have hdiv : c 82 = 0 → (c 42 + 2 ^ 8 * c 43 + 2 ^ 16 * c 44 + 2 ^ 24 * c 45 + 2 ^ 32 * c 46 + 2 ^ 40 * c 47 + 2 ^ 48 * c 48 + 2 ^ 56 * c 49) * (c 34 + 2 ^ 8 * c 35 + 2 ^ 16 * c 36 + 2 ^ 24 * c 37 + 2 ^ 32 * c 38 + 2 ^ 40 * c 39 + 2 ^ 48 * c 40 + 2 ^ 56 * c 41) + (c 50 + 2 ^ 8 * c 51 + 2 ^ 16 * c 52 + 2 ^ 24 * c 53 + 2 ^ 32 * c 54 + 2 ^ 40 * c 55 + 2 ^ 48 * c 56 + 2 ^ 56 * c 57) = (c 26 + 2 ^ 8 * c 27 + 2 ^ 16 * c 28 + 2 ^ 24 * c 29 + 2 ^ 32 * c 30 + 2 ^ 40 * c 31 + 2 ^ 48 * c 32 + 2 ^ 56 * c 33) ∧ (c 50 + 2 ^ 8 * c 51 + 2 ^ 16 * c 52 + 2 ^ 24 * c 53 + 2 ^ 32 * c 54 + 2 ^ 40 * c 55 + 2 ^ 48 * c 56 + 2 ^ 56 * c 57) < (c 34 + 2 ^ 8 * c 35 + 2 ^ 16 * c 36 + 2 ^ 24 * c 37 + 2 ^ 32 * c 38 + 2 ^ 40 * c 39 + 2 ^ 48 * c 40 + 2 ^ 56 * c 41) := fun h82 =>
      ⟨div8_key (c 42) (c 43) (c 44) (c 45) (c 46) (c 47) (c 48) (c 49) (c 34) (c 35) (c 36) (c 37) (c 38) (c 39) (c 40) (c 41) (c 50) (c 51) (c 52) (c 53) (c 54) (c 55) (c 56) (c 57) (c 26) (c 27) (c 28) (c 29) (c 30) (c 31) (c 32) (c 33) (c 66) (c 67) (c 68) (c 69) (c 70) (c 71) (c 72)
        (E0 h82) (E1 h82) (E2 h82) (E3 h82) (E4 h82) (E5 h82) (E6 h82) (by have := E7 h82; have := C73 h82 h9; omega)
        (Z8 h82 h9) (Z9 h82 h9) (Z10 h82 h9) (Z11 h82 h9) (Z12 h82 h9) (Z13 h82 h9) (Z14 h82 h9),
       by have := T0 h82; have := T1 h82; have := T2 h82; have := T3 h82; have := T4 h82; omega⟩
    have hr0 : c 5 * (c 22 + c 24 - 2 * c 22 * c 24) + c 7 * c 22 = 0 → val4 (c 87) (c 88) (c 89) (c 90) = (c 5 + c 6) * (c 42 + 2 ^ 8 * c 43 + 2 ^ 16 * c 44 + 2 ^ 24 * c 45 + 2 ^ 32 * c 46 + 2 ^ 40 * c 47 + 2 ^ 48 * c 48 + 2 ^ 56 * c 49) + (c 7 + c 8) * (c 50 + 2 ^ 8 * c 51 + 2 ^ 16 * c 52 + 2 ^ 24 * c 53 + 2 ^ 32 * c 54 + 2 ^ 40 * c 55 + 2 ^ 48 * c 56 + 2 ^ 56 * c 57) := fun h => by
      obtain ⟨u0, u1⟩ := NR0 h; obtain ⟨u2, u3⟩ := NR20 h; rcases hfl with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [e1, e2, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add, val4] at u0 u1 u2 u3 ⊢ <;> omega
    have hr1 : c 5 * (c 22 + c 24 - 2 * c 22 * c 24) + c 7 * c 22 = 1 → val4 (c 87) (c 88) (c 89) (c 90) = (2 ^ 64 - ((c 5 + c 6) * (c 42 + 2 ^ 8 * c 43 + 2 ^ 16 * c 44 + 2 ^ 24 * c 45 + 2 ^ 32 * c 46 + 2 ^ 40 * c 47 + 2 ^ 48 * c 48 + 2 ^ 56 * c 49) + (c 7 + c 8) * (c 50 + 2 ^ 8 * c 51 + 2 ^ 16 * c 52 + 2 ^ 24 * c 53 + 2 ^ 32 * c 54 + 2 ^ 40 * c 55 + 2 ^ 48 * c 56 + 2 ^ 56 * c 57))) % 2 ^ 64 := fun h => by
      obtain ⟨u0, u1⟩ := NR1 h; obtain ⟨u2, u3⟩ := NR21 h; rcases hfl with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [e1, e2, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add, val4] at u0 u1 u2 u3 ⊢ <;> omega
    have X := assemble 64 (val4 (c 10) (c 11) (c 12) (c 13)) (val4 (c 16) (c 17) (c 18) (c 19)) (c 26 + 2 ^ 8 * c 27 + 2 ^ 16 * c 28 + 2 ^ 24 * c 29 + 2 ^ 32 * c 30 + 2 ^ 40 * c 31 + 2 ^ 48 * c 32 + 2 ^ 56 * c 33) (c 34 + 2 ^ 8 * c 35 + 2 ^ 16 * c 36 + 2 ^ 24 * c 37 + 2 ^ 32 * c 38 + 2 ^ 40 * c 39 + 2 ^ 48 * c 40 + 2 ^ 56 * c 41) (c 42 + 2 ^ 8 * c 43 + 2 ^ 16 * c 44 + 2 ^ 24 * c 45 + 2 ^ 32 * c 46 + 2 ^ 40 * c 47 + 2 ^ 48 * c 48 + 2 ^ 56 * c 49) (c 50 + 2 ^ 8 * c 51 + 2 ^ 16 * c 52 + 2 ^ 24 * c 53 + 2 ^ 32 * c 54 + 2 ^ 40 * c 55 + 2 ^ 48 * c 56 + 2 ^ 56 * c 57) (val4 (c 87) (c 88) (c 89) (c 90))
      (c 5) (c 6) (c 7) (c 8) (c 22) (c 24) (c 84) (c 82) (c 86) (by decide) (by omega) (by omega) (by omega)
      (by omega) tz01 hbW hQW hRW hAa hBb' hQq hnA0 hnA1 hnB0 hnB1 htzB TOV hdiv hr0 hr1
    rw [show 32 + 32 * c 9 = 64 by omega]
    exact X
