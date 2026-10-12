import ZkFormal.NearV3.Rcpt.Extract.SizeProof
import ZkFormal.NearV3.Tables.UnfoldA7

/-!
# ZkFormal.NearV3.Assembly.A7SizeView — the A7 view of `sizeA7` (soundness)

`sizeA7` (table 21) appends to `sizeV3`: on its active rows `t = 0, 1, 2` it receives
`SIZE (t + 3, y_t)`; the running sum `u` of `y` is checked on the last active row (`la`, row 2):
`B0 − u` is a 24-bit value.

* `size_rows` — the row pattern of any `TableLocal sizeV3` trace (rows `0,1,2` active with
  `t = 0,1,2`, row 2 the last active one, every row from `3` on inactive), as in `size_view_at`;
* **`sizeA7_view`**: the appended interaction's traffic is exactly the receives
  `[3, y_0], [4, y_1], [5, y_2]` (`a7SizeTraffic`), with `y_t < P` and
  `(b + y_0 + y_1 + y_2) % P = B0` for some `b < 2^24` (`A7SizeWf`).
-/

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- The three A7 totals received by `sizeA7`. -/
structure A7Y where
  y0 : Nat
  y1 : Nat
  y2 : Nat
  deriving Repr, Inhabited

/-- The A7 receives of `sizeA7`: `SIZE (3, y_0)`, `SIZE (4, y_1)`, `SIZE (5, y_2)`. -/
def a7SizeTraffic (a : A7Y) : Traffic :=
  ⟨fun _ => [], fun b => if b = B_SIZE then [[3, a.y0], [4, a.y1], [5, a.y2]] else []⟩

/-- The A7 bound as a field fact: `B0 − Σ y_t` is a 24-bit value. -/
structure A7SizeWf (a : A7Y) : Prop where
  canon : a.y0 < P ∧ a.y1 < P ∧ a.y2 < P
  slack : ∃ b, b < 2 ^ 24 ∧ (b + a.y0 + a.y1 + a.y2) % P = UnfoldA7.B0

end ZkFormal.NearV3

namespace ZkFormal.NearV3.SizeProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.SizeV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- The row pattern of a local `sizeV3` trace (any cap `≤ 22`). -/
theorem size_rows {cap : Nat} (hcap : cap ≤ 22) (hL : TableLocal { SizeV3.table with maxLog := cap } tr tt pub) :
    4 ≤ tr.height tt ∧ tr.height tt < P ∧
    tr.cell tt 0 act = 1 ∧ tr.cell tt 1 act = 1 ∧ tr.cell tt 2 act = 1 ∧
    tr.cell tt 0 t = 0 ∧ tr.cell tt 1 t = 1 ∧ tr.cell tt 2 t = 2 ∧
    tr.cell tt 0 la = 0 ∧ tr.cell tt 1 la = 0 ∧ tr.cell tt 2 la = 1 ∧
    ∀ q, 3 ≤ q → q < tr.height tt → tr.cell tt q act = 0 := by
  have hP : tr.height tt < P := by
    have h2 := hL.log_le
    have : tr.height tt ≤ 2 ^ 22 := by
      unfold Trace.height; exact Nat.pow_le_pow_right (by decide) (by simp at h2; omega)
    unfold P; omega
  have hH : tr.height tt = 2 ∨ 4 ≤ tr.height tt := by
    have h1 := hL.log_ge
    unfold Trace.height
    rcases Nat.lt_or_ge (tr.log tt) 2 with h | h
    · left; rw [show tr.log tt = 1 by omega]
    · right; exact Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) h)
  have h2 : 1 < tr.height tt := by omega
  obtain ⟨a0, t0, -, -, -⟩ := firstF hL h2
  have ne : ∀ a b : Nat, a < P → b < P → a ≠ b → ¬ ((a : Fp) = (b : Fp)) := fun a b ha hb h e =>
    h (ofNat_inj ha hb e)
  have la0 : tr.cell tt 0 SizeV3.la = 0 := by
    rcases isB hL (r := 0) (by omega) (y := SizeV3.la) (by simp) with h | h
    · exact h
    · have := ((rowF hL (r := 0) (by omega)).2 h).1
      rw [t0] at this; exact absurd (show ((0 : Nat) : Fp) = ((2 : Nat) : Fp) from this) (ne 0 2 (by decide) (by decide) (by decide))
  obtain ⟨a1, -, t1', -⟩ := trF hL (r := 0) h2
  have act1 := a1 a0 la0
  have t1 : tr.cell tt 1 SizeV3.t = 1 := by rw [t1' a0, t0]; grind
  have la1 : tr.cell tt 1 SizeV3.la = 0 := by
    rcases isB hL (r := 1) (by omega) (y := SizeV3.la) (by simp) with h | h
    · exact h
    · have := ((rowF hL (r := 1) (by omega)).2 h).1
      rw [t1] at this; exact absurd (show ((1 : Nat) : Fp) = ((2 : Nat) : Fp) from this) (ne 1 2 (by decide) (by decide) (by decide))
  have h4 : 4 ≤ tr.height tt := by
    rcases hH with h | h
    · exfalso
      have := lastF hL (by omega) (by rw [h]; exact act1)
      rw [h] at this; simp only [show 2 - 1 = 1 from rfl] at this; rw [la1] at this; exact fp_zero_ne_one this
    · exact h
  obtain ⟨b1, -, t2', -⟩ := trF hL (r := 1) (by omega)
  have act2 := b1 act1 la1
  have t2 : tr.cell tt 2 SizeV3.t = 2 := by rw [t2' act1, t1]; grind
  obtain ⟨c1, c2, t3', -⟩ := trF hL (r := 2) (by omega)
  have la2 : tr.cell tt 2 SizeV3.la = 1 := by
    rcases isB hL (r := 2) (by omega) (y := SizeV3.la) (by simp) with h | h
    · exfalso
      have act3 := c1 act2 h
      have t3 : tr.cell tt 3 SizeV3.t = ((3 : Nat) : Fp) := by rw [t3' act2, t2]; grind
      obtain ⟨aL, -, lL⟩ := runF hL hP (r := 3) (Nat.le_refl 3) (tr.height tt - 4) (by omega) act3 t3
      rw [show 3 + (tr.height tt - 4) = tr.height tt - 1 by omega] at aL lL
      have := lastF hL (by omega) aL
      rw [lL] at this; exact fp_zero_ne_one this
    · exact h
  have act3 : tr.cell tt 3 SizeV3.act = 0 := c2 la2
  have actP : ∀ q, 3 ≤ q → q < tr.height tt → tr.cell tt q SizeV3.act = 0 := by
    intro q h3 hq
    induction q with
    | zero => omega
    | succ q ih =>
      rcases Nat.lt_or_ge q 3 with h | h
      · rw [show q + 1 = 3 by omega]; exact act3
      · exact padF hL hq (ih h (by omega))
  exact ⟨h4, hP, a0, act1, act2, t0, t1, t2, la0, la1, la2, actP⟩

end ZkFormal.NearV3.SizeProof

namespace ZkFormal.NearV3.A7SizeProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.SizeV3
  ZkFormal.NearV3.UnfoldA7 ZkFormal.NearV3.SizeProof

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem memA7 {e : Expr} (h : e ∈ Size.constraints) : e ∈ sizeA7.constraints :=
  List.mem_append_right _ h

theorem rowA7 (q bb : Nat) (sd : Bool) :
    rowTraffic Size.interactions tr tt q pub bb sd =
      if bb = B_SIZE ∧ sd = false ∧ tr.cell tt q act = 1 then
        [[tr.cell tt q SizeV3.t + ((3 : Nat) : Fp), tr.cell tt q Size.y]] else [] := by
  simp only [rowTraffic, Size.interactions, List.flatMap_cons, List.flatMap_nil, Dsl.recv,
    Interaction.multNat, multNat1, Interaction.msgVal, List.map_cons, List.map_nil, eval_c, eval_add,
    eval_k, List.append_nil]
  by_cases h1 : bb = B_SIZE <;> by_cases h2 : sd = false <;> by_cases h3 : tr.cell tt q act = 1 <;>
    simp_all [eq_comm]

/-- **The A7 view of `sizeA7`.** -/
theorem sizeA7_view (hL : TableLocal sizeA7 tr tt pub) :
    ∃ a, A7SizeWf a ∧ TableTraffic Size.interactions tr tt pub (a7SizeTraffic a) := by
  have hB : TableLocal { SizeV3.table with maxLog := 4 } tr tt pub :=
    ⟨hL.log_ge, hL.log_le, fun r hr e he => hL.constr r hr e (List.mem_append_left _ he),
      fun r hr i hi b hb => hL.bits r hr i (List.mem_append_left _ hi) b hb⟩
  obtain ⟨h4, -, a0, a1, a2, t0, t1, t2, -, -, la2, actP⟩ := size_rows (by decide) hB
  have con : ∀ r, r < tr.height tt → ∀ e ∈ Size.constraints, e.eval tr tt r pub = 0 :=
    fun r hr e he => hL.constr r hr e (memA7 he)
  -- the running sum
  have u0 : tr.cell tt 0 Size.u = tr.cell tt 0 Size.y := by
    have := con 0 (by omega) (.mul .isFirst (sub (c Size.u) (c Size.y))) (by simp [Size.constraints])
    simp only [eval_mul, eval_c, eval_sub, eval_isFirst, if_pos rfl] at this; grind
  have uS : ∀ r, r + 1 < tr.height tt → tr.cell tt (r + 1) act = 1 →
      tr.cell tt (r + 1) Size.u = tr.cell tt r Size.u + tr.cell tt (r + 1) Size.y := by
    intro r hr ha
    have := con r (by omega) (mul3 .isTransition (n act) (sub (n Size.u) (.add (c Size.u) (n Size.y))))
      (by simp [Size.constraints])
    simp only [eval_mul3, eval_c, eval_n, eval_sub, eval_add, eval_isTransition, Nat.mod_eq_of_lt hr,
      if_neg (show ¬ r + 1 = tr.height tt by omega), ha] at this
    grind
  have u2 : tr.cell tt 2 Size.u = tr.cell tt 0 Size.y + tr.cell tt 1 Size.y + tr.cell tt 2 Size.y := by
    rw [uS 1 (by omega) a2, uS 0 (by omega) a1, u0]
  -- the bits
  have isUB : ∀ e, e < 24 → tr.cell tt 2 (Size.ub e) = 0 ∨ tr.cell tt 2 (Size.ub e) = 1 := by
    intro e he
    have := con 2 (by omega) (Dsl.bool (c (Size.ub e)))
      (List.mem_append_left _ (List.mem_map_of_mem (f := fun e => Dsl.bool (c (Size.ub e))) (List.mem_range.2 he)))
    simp only [eval_bool, eval_c] at this
    exact bool_cases this
  have hb : Size.ubitsE.eval tr tt 2 pub = ((bitsVal (fun b => cv tr tt 2 (Size.ub b)) 0 24 : Nat) : Fp) :=
    eval_bits tr tt 2 pub Size.ub 0 24 (fun b hb => by rw [Nat.zero_add]; exact isUB b (by omega))
  have bl : bitsVal (fun b => cv tr tt 2 (Size.ub b)) 0 24 < 2 ^ 24 :=
    bitsVal_lt _ 0 24 (fun b hb => cv_bool (by rw [Nat.zero_add]; exact isUB b (by omega)))
  have hbd := con 2 (by omega) (.mul (c la) (sub Size.ubitsE (sub (k B0) (c Size.u)))) (by simp [Size.constraints])
  simp only [eval_mul, eval_c, eval_sub, eval_k, hb, la2] at hbd
  let yN := fun r => (tr.cell tt r Size.y).toNat
  have cy : ∀ r, tr.cell tt r Size.y = ((yN r : Nat) : Fp) := fun r => (Fp.ofNat_toNat _).symm
  have hs : (bitsVal (fun b => cv tr tt 2 (Size.ub b)) 0 24 + (yN 0 + yN 1 + yN 2)) % P = B0 := by
    apply slack_of _ (by decide)
    rw [natCast_add, natCast_add, ← cy, ← cy, ← cy, ← u2]; grind
  refine ⟨⟨yN 0, yN 1, yN 2⟩, ⟨⟨Fp.toNat_lt _, Fp.toNat_lt _, Fp.toNat_lt _⟩, ⟨_, bl, ?_⟩⟩, fun bb m => ⟨?_, ?_⟩⟩
  · rw [← hs]; dsimp only; congr 1; omega
  · rw [tableBusCount_eq]
    simp only [rowA7, a7SizeTraffic, List.map_nil]
    simp [flatMap_nil_fun]
  · have hsplit : List.range (tr.height tt) = List.range 3 ++ (List.range (tr.height tt - 3)).map (3 + ·) := by
      rw [← List.range_add, Nat.add_sub_cancel' (by omega)]
    have hrest : ((List.range (tr.height tt - 3)).map (3 + ·)).flatMap
        (fun r => rowTraffic Size.interactions tr tt r pub bb false) = [] := by
      refine List.flatMap_eq_nil_iff.2 fun q hq => ?_
      obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
      have := List.mem_range.1 hq'
      rw [rowA7, actP (3 + q') (by omega) (by omega)]
      simp
    rw [tableBusCount_eq, hsplit, List.flatMap_append, hrest, List.append_nil]
    simp only [rowA7, a7SizeTraffic, show List.range 3 = [0, 1, 2] from rfl, List.flatMap_cons,
      List.flatMap_nil, a0, a1, a2, t0, t1, t2]
    by_cases hb' : bb = B_SIZE
    · simp only [hb', true_and, if_true, List.append_nil, List.cons_append,
        List.nil_append, List.map_cons, List.map_nil, Msg.toFp]
      simp only [yN, Fp.ofNat_toNat]
      congr 3 <;> grind
    · simp [hb']

end ZkFormal.NearV3.A7SizeProof
