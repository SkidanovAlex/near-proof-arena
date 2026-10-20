import ZkFormal.PQ.StatePort.Swirl
import ZkFormal.Near.Extract.Eval
import ZkFormal.Udr.Np.Bus
import ZkFormal.V2.Np.Bus

/-!
# ZkFormal.PQ.StatePort.Bridge — the SWIRL relation of a translated AIR implies `HoldsP`

Lane `pq-state-port`.  The post-quantum stack evaluates exactly the classical AIR `AP : AirP`
over the same base field `Fp`, with the classical constraints unchanged, its interactions as
LogUp fractions on buses `off + bus`, and the classical public segments as one extra committed
table `TAPE` (see `PQ.StatePort.Swirl`).  This module builds the soundness bridge.

**The gap this module closes.**  The classical `HoldsP` balance is an equality of *naturals*
(`busCount … true m + pubCount … true m = busCount … false m + pubCount … false m`), while SWIRL's
LogUp balance is an equality of *field* sums.  The bridge is exact because `multBoundP AP < P`:
every side count is `< P`, so the field difference of two bounded naturals being zero is their
being equal (`nat_inj_of_lt`).

## Proved here

* `nat_inj_of_lt`, `nat_cast_add_of_lt`, `fsum_cast`, `fsum_map_natCast` — the field/natural
  arithmetic core;
* `bit_eq_zero_or_one` and `bits_of_swirl` — the booleanity constraints in `allConstraints` give
  `0/1` multiplicity bits on every row, which is `HoldsP.bits`;
* `evalWith_eq_of_agree`, `eval_eq_of_agree` — public-value agreement below an expression's
  `pubBound` propagates through the whole expression, so `VdChecks.pvAgree` turns each table's
  `pv` evaluation into the classical `pub` evaluation;
* `countFGo_eq_multNat`, `countF_eq_multNat` — the LogUp field count `Σₖ 2^k·bₖ` is the cast of
  the classical natural multiplicity `Interaction.multNat`, for `0/1` bits of length `≤ 25`
  (the `Air` bound); this is what makes the LogUp fraction the classical count;
* `rowSum_eq_sub`, `rowSide_eq`, `tableSide_eq`, `tableSide_sub`, `tablesSum_eq_sides` — a row's
  signed field sum is its send count minus its receive count, and the whole-AIR sum is the
  difference of the two side counts (with the bus-id shift);
* `balance_step`, `eq_of_field` — the LogUp balance plus TAPE's `netF` and the `< p` bounds give
  the classical two-sided balance;
* `busCount_eq_tables`, `tableBusCount_congr` — the translated AIR's `busCount` is the sum over
  tables of the per-table counts, with `pv`/`pub` agreement;
* `tableBusCount_le_side`, `busCount_le_multBound` — every trace side count is `≤ Air.multBound`
  when heights respect `maxLog`, so `multBoundP AP < P` bounds it;
* `nearAirV3_multBoundP_lt` and `nearAirV3D1_multBoundP_lt` — the kernel-checked P2 facts.

## The bridge is complete

`holdsP_of_swirl` is proved, with no `sorry`: given `SwirlRel` (assumption P5), `VdChecks`, the
multiplicity bound `multBoundP AP < p`, the fitting segments and the static `mult.length ≤ 25`
bound, the classical `HoldsP AP pub tr` follows.  The aggregation is
`rowSide_eq` → `tableSide_eq` → `tableSide_sub` → `tablesSum_eq_sides` → `balance_step`, and the
mod-p⇒ℕ step is `eq_of_field` / `nat_eq_of_cast_sub`.
-/

namespace ZkFormal.PQ.StatePort

open ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra ZkFormal.Udr ZkFormal.Udr.Np

/-! ## Field arithmetic facts -/

/-- A field equality of two naturals below `p` is their equality. -/
theorem nat_inj_of_lt {a b : Nat} (ha : a < P) (hb : b < P)
    (h : ((a : Nat) : Fp) = ((b : Nat) : Fp)) : a = b := by
  have e := congrArg Fp.toNat h
  change (Fp.ofNat a).toNat = (Fp.ofNat b).toNat at e
  rw [Fp.toNat_ofNat, Fp.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at e
  exact e

/-- Natural cast adds below `p`. -/
theorem nat_cast_add_of_lt {a b : Nat} (h : a + b < P) :
    ((a + b : Nat) : Fp) = ((a : Nat) : Fp) + ((b : Nat) : Fp) := by
  change Fp.ofNat (a + b) = Fp.ofNat a + Fp.ofNat b
  rw [ZkFormal.Near.ofNat_add']

/-- `List.sum` over `Fp` is `fsum`. -/
theorem sum_eq_fsum (l : List Fp) : l.sum = fsum l := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.sum_cons, fsum, ih]; rfl

/-- `fsum` of a natural-cast list is the cast of its sum. -/
theorem fsum_cast (l : List Nat) : fsum (l.map fun n => ((n : Nat) : Fp)) = ((l.sum : Nat) : Fp) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show ((a : Nat) : Fp) + fsum (l.map fun n => ((n : Nat) : Fp)) = _
    rw [ih, List.sum_cons]
    change Fp.ofNat a + Fp.ofNat l.sum = Fp.ofNat (a + l.sum)
    rw [ZkFormal.Near.ofNat_add']

/-- `fsum` of `f` cast pointwise. -/
theorem fsum_map_natCast {α : Type} (l : List α) (f : α → Nat) :
    fsum (l.map fun a => ((f a : Nat) : Fp)) = (((l.map f).sum : Nat) : Fp) := by
  rw [← fsum_cast]
  congr 1
  rw [List.map_map]
  rfl

/-- `fsum` of a pointwise sum. -/
theorem fsum_add {l : List Fp} {f g : Fp → Fp} :
    fsum (l.map fun x => f x + g x) = fsum (l.map f) + fsum (l.map g) := by
  induction l with
  | nil => show (0:Fp) = 0 + 0; grind
  | cons a l ih =>
    show f a + g a + fsum (l.map fun x => f x + g x)
      = (f a + fsum (l.map f)) + (g a + fsum (l.map g))
    rw [ih]; grind

/-- `fsum` of a pointwise difference. -/
theorem fsum_sub {l : List Fp} {f g : Fp → Fp} :
    fsum (l.map fun x => f x - g x) = fsum (l.map f) - fsum (l.map g) := by
  induction l with
  | nil => show (0:Fp) = 0 - 0; grind
  | cons a l ih =>
    show f a - g a + fsum (l.map fun x => f x - g x)
      = (f a + fsum (l.map f)) - (g a + fsum (l.map g))
    rw [ih]; grind

/-- `fsum` is invariant under a pointwise-equal map. -/
theorem fsum_congr_map {α : Type} (l : List α) {f g : α → Fp} (h : ∀ x ∈ l, f x = g x) :
    fsum (l.map f) = fsum (l.map g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show f a + fsum (l.map f) = g a + fsum (l.map g)
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- `fsum` splits over `++`. -/
theorem fsum_append (a b : List Fp) : fsum (a ++ b) = fsum a + fsum b := by
  induction a with
  | nil => show fsum b = 0 + fsum b; grind
  | cons x a ih => show x + fsum (a ++ b) = (x + fsum a) + fsum b; rw [ih]; grind

/-! ## Bits from the booleanity constraints -/

theorem bit_eq_zero_or_one {b : Expr} {tr : Trace Fp} {t r : Nat} {pv : List Fp}
    (h : (Expr.mul b (Expr.add b (Expr.neg (Expr.const 1)))).eval tr t r pv = 0) :
    b.eval tr t r pv = 0 ∨ b.eval tr t r pv = 1 := by
  simp only [Expr.eval, Expr.evalWith] at h
  rcases ZkFormal.Near.mul_eq_zero'.mp h with h0 | h0
  · exact Or.inl h0
  · right
    have : b.eval tr t r pv + -(1 : Fp) = 0 := h0
    grind

/-- Every multiplicity bit of table `t` is `0/1` on every row, from `SwirlRel.constr`. -/
theorem bits_of_swirl {off : Nat} {AP : AirP} {pv : Nat → List Fp} {tr : Trace Fp} {tape : Tape}
    (h : SwirlRel off AP pv tr tape) (t : Nat) (ht : t < AP.tables.length) (r : Nat)
    (hr : r < tr.height t) (i : Interaction) (hi : i ∈ AP.tables[t].interactions)
    (b : Expr) (hb : b ∈ i.mult) :
    b.eval tr t r (pv t) = 0 ∨ b.eval tr t r (pv t) = 1 := by
  have hbc : Expr.mul b (Expr.add b (Expr.neg (Expr.const 1))) ∈ AP.tables[t].allConstraints := by
    unfold Table.allConstraints Table.bitConstraints
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, hi, List.mem_map.mpr ⟨b, hb, rfl⟩⟩)
  exact bit_eq_zero_or_one (h.constr t ht r hr _ hbc)

/-! ## Public-value agreement -/

/-- An expression's value depends only on the public inputs below its `pubBound`. -/
theorem evalWith_eq_of_agree (e : Expr) (tr : Trace Fp) (t r : Nat) {pub pv : List Fp}
    (h : ∀ i, i < e.pubBound → pv.getD i 0 = pub.getD i 0) :
    e.evalWith (rowEnv tr t r pv) = e.evalWith (rowEnv tr t r pub) := by
  induction e generalizing pub pv with
  | const c => rfl
  | col c nx => rfl
  | pub i => simpa [Expr.evalWith, rowEnv] using h i (by simp [Expr.pubBound])
  | isFirst => rfl
  | isLast => rfl
  | isTransition => rfl
  | add a b iha ihb =>
    have hp : a.pubBound ≤ (Expr.add a b).pubBound ∧ b.pubBound ≤ (Expr.add a b).pubBound :=
      ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩
    simp only [Expr.evalWith]
    rw [iha (fun i hi => h i (Nat.le_trans hi hp.1)),
      ihb (fun i hi => h i (Nat.le_trans hi hp.2))]
    rfl
  | mul a b iha ihb =>
    have hp : a.pubBound ≤ (Expr.mul a b).pubBound ∧ b.pubBound ≤ (Expr.mul a b).pubBound :=
      ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩
    simp only [Expr.evalWith]
    rw [iha (fun i hi => h i (Nat.le_trans hi hp.1)),
      ihb (fun i hi => h i (Nat.le_trans hi hp.2))]
    rfl
  | neg a ih =>
    simp only [Expr.evalWith]
    rw [ih h]
    rfl

/-- `Expr.eval` is invariant under public-value agreement. -/
theorem eval_eq_of_agree (e : Expr) (tr : Trace Fp) (t r : Nat) {pub pv : List Fp}
    (h : ∀ i, i < e.pubBound → pv.getD i 0 = pub.getD i 0) :
    e.eval tr t r pv = e.eval tr t r pub :=
  evalWith_eq_of_agree e tr t r h

/-! ## The LogUp count is the natural multiplicity -/

/-- The recursive count equals the natural multiplicity, for `0/1` bits and length `≤ 25`. -/
theorem countFGo_eq_multNat (tr : Trace Fp) (t r : Nat) (pv : List Fp) :
    ∀ (bs : List Expr) (k : Nat),
      (∀ b ∈ bs, b.eval tr t r pv = 0 ∨ b.eval tr t r pv = 1) →
      k + bs.length ≤ 25 →
      countFGo tr t r pv bs k = ((Interaction.multNat.go tr t r pv bs k : Nat) : Fp)
  | [], k, _, _ => rfl
  | b :: bs, k, hbool, hlen => by
    rw [Interaction.multNat.go, countFGo]
    have hb := hbool b (by simp)
    have hbs : ∀ x ∈ bs, x.eval tr t r pv = 0 ∨ x.eval tr t r pv = 1 :=
      fun x hx => hbool x (by simp [hx])
    have hlen' : k + 1 + bs.length ≤ 25 := by simp at hlen; omega
    rw [countFGo_eq_multNat tr t r pv bs (k + 1) hbs hlen']
    have hle := ZkFormal.Udr.Np.multNat_go_le tr t r pv bs (k + 1)
    have htop : 2 ^ (k + 1 + bs.length) ≤ 2 ^ 25 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hgo : Interaction.multNat.go tr t r pv bs (k + 1) ≤ 2 ^ 25 := by
      have h1 : Interaction.multNat.go tr t r pv bs (k + 1) + 2 ^ (k + 1) ≤
          2 ^ (k + 1 + bs.length) := hle
      have h2 : Interaction.multNat.go tr t r pv bs (k + 1) ≤
          Interaction.multNat.go tr t r pv bs (k + 1) + 2 ^ (k + 1) := Nat.le_add_right _ _
      exact Nat.le_trans (Nat.le_trans h2 h1) htop
    have hlt : 2 ^ k + Interaction.multNat.go tr t r pv bs (k + 1) < P := by
      have : (2 : Nat) ^ 26 < P := by decide
      omega
    rcases hb with hb | hb
    · rw [hb]
      simp only [Lean.Grind.Semiring.mul_zero,
        show ¬((0 : Fp) = 1) from ZkFormal.Near.fp_zero_ne_one, if_false]
      grind
    · rw [hb]
      simp only [Lean.Grind.Semiring.mul_one, if_true]
      rw [show ((2 ^ k : Nat) : Fp) + ((Interaction.multNat.go tr t r pv bs (k + 1) : Nat) : Fp)
          = (((2 ^ k) + Interaction.multNat.go tr t r pv bs (k + 1) : Nat) : Fp) from by
        change Fp.ofNat (2 ^ k) + Fp.ofNat _ = Fp.ofNat _
        rw [ZkFormal.Near.ofNat_add']]

/-- The field count of an interaction equals its natural multiplicity. -/
theorem countF_eq_multNat (i : Interaction) (tr : Trace Fp) (t r : Nat) (pv : List Fp)
    (hbool : ∀ b ∈ i.mult, b.eval tr t r pv = 0 ∨ b.eval tr t r pv = 1)
    (hlen : i.mult.length ≤ 25) :
    countF i tr t r pv = ((i.multNat tr t r pv : Nat) : Fp) := by
  unfold countF Interaction.multNat
  exact countFGo_eq_multNat tr t r pv i.mult 0 hbool (by omega)

/-! ## Row and table sums -/

/-- `signed` is the send part minus the receive part. -/
theorem signed_eq (send : Bool) (x : Fp) :
    signed send x = (if send = true then x else 0) - (if send = false then x else 0) := by
  unfold signed; cases send <;> grind

/-- `fsum` of a pointwise difference over an arbitrary list. -/
theorem fsum_sub_map {α : Type} (l : List α) (f g : α → Fp) :
    fsum (l.map fun x => f x - g x) = fsum (l.map f) - fsum (l.map g) := by
  induction l with
  | nil => show (0:Fp) = 0 - 0; grind
  | cons a l ih =>
    show f a - g a + fsum (l.map fun x => f x - g x)
      = (f a + fsum (l.map f)) - (g a + fsum (l.map g))
    rw [ih]; grind

/-- A row's field sum is its send contribution minus its receive contribution. -/
theorem rowSum_eq_sub (off : Nat) (is : List Interaction) (tr : Trace Fp) (t r : Nat)
    (pv : List Fp) (b : Nat) (m : List Fp) :
    rowSum off is tr t r pv b m
      = fsum (is.map fun i => if off + i.bus = b ∧ i.msgVal tr t r pv = m ∧ i.send = true
          then countF i tr t r pv else 0)
        - fsum (is.map fun i => if off + i.bus = b ∧ i.msgVal tr t r pv = m ∧ i.send = false
          then countF i tr t r pv else 0) := by
  unfold rowSum
  rw [fsum_congr_map (g := fun i => (if off + i.bus = b ∧ i.msgVal tr t r pv = m ∧ i.send = true
          then countF i tr t r pv else 0)
        - (if off + i.bus = b ∧ i.msgVal tr t r pv = m ∧ i.send = false
          then countF i tr t r pv else 0))]
  · exact fsum_sub_map is _ _
  · intro i _
    by_cases hkey : off + i.bus = b ∧ i.msgVal tr t r pv = m
    · rw [if_pos hkey]
      cases hi : i.send
      · rw [signed_eq]
        simp only [if_true, reduceIte, Bool.false_eq_true]
        grind
      · rw [signed_eq]
        simp only [reduceIte, Bool.true_eq_false]
        grind
    · rw [if_neg hkey]
      by_cases h1 : off + i.bus = b ∧ i.msgVal tr t r pv = m ∧ i.send = true
      · exact absurd ⟨h1.1, h1.2.1⟩ hkey
      · by_cases h2 : off + i.bus = b ∧ i.msgVal tr t r pv = m ∧ i.send = false
        · exact absurd ⟨h2.1, h2.2.1⟩ hkey
        · rw [if_neg h1, if_neg h2]; grind

/-- `tablesSum` unrolled into tables × rows × interactions. -/
theorem tablesSum_eq_flat (off : Nat) (AP : AirP) (tr : Trace Fp) (pv : Nat → List Fp)
    (b : Nat) (m : List Fp) :
    tablesSum off AP tr pv b m
      = fsum ((List.range AP.tables.length).map fun t =>
          fsum ((List.range (tr.height t)).map fun r =>
            fsum ((tableAt AP t).interactions.map fun i =>
              if off + i.bus = b ∧ i.msgVal tr t r (pv t) = m
              then signed i.send (countF i tr t r (pv t)) else 0))) := by
  unfold tablesSum tableSum rowSum
  rfl

/-! ## Bounds -/

/-- One side of one table's traffic is at most `height · Σᵢ (2^{|multᵢ|} − 1)`. -/
theorem tableBusCount_le_side (is : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (b : Nat) (send : Bool) (m : List Fp) :
    tableBusCount is tr t pub b send m
      ≤ tr.height t * (is.map fun i => 2 ^ i.mult.length - 1).sum := by
  rw [tableBusCount_eq]
  have h1 : ∀ r ∈ List.range (tr.height t),
      (is.map fun i => if i.bus = b ∧ i.send = send ∧ i.msgVal tr t r pub = m then
        i.multNat tr t r pub else 0).sum ≤ (is.map fun i => 2 ^ i.mult.length - 1).sum := by
    intro r _
    refine ZkFormal.Udr.sum_le_of_le is _ _ fun i _ => ?_
    split
    · exact ZkFormal.Udr.Np.multNat_le i tr t r pub
    · exact Nat.zero_le _
  have h2 := ZkFormal.Udr.sum_le_length_mul (List.range (tr.height t)) _ _ h1
  rw [List.length_range] at h2
  exact h2

/-- One table's side count inside `Air.multBound`'s sum, when the height respects `maxLog`. -/
theorem table_in_multBound (A : Air) (tr : Trace Fp) (pub : List Fp) (t : Nat)
    (ht : t < A.tables.length)
    (hlog : ∀ t (ht : t < A.tables.length), tr.log t ≤ A.tables[t].maxLog)
    (b : Nat) (send : Bool) (m : List Fp) :
    tableBusCount (A.tables[t]).interactions tr t pub b send m
      ≤ 2 ^ (A.tables[t]).maxLog *
        ((A.tables[t]).interactions.map fun i => 2 ^ i.mult.length - 1).sum := by
  refine Nat.le_trans (tableBusCount_le_side _ tr t pub b send m) ?_
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (hlog t ht))

/-- Every trace side count is at most `Air.multBound`. -/
theorem busCount_le_multBound (A : Air) (tr : Trace Fp) (pub : List Fp)
    (hlog : ∀ t (ht : t < A.tables.length), tr.log t ≤ A.tables[t].maxLog)
    (b : Nat) (send : Bool) (m : List Fp) :
    busCount A tr pub b send m ≤ A.multBound := by
  rw [busCount_eq, Air.multBound]
  refine ZkFormal.Udr.Np.sum_range_tables A
    (fun t => tableBusCount (tableOf A t).interactions tr t pub b send m)
    (fun T => 2 ^ T.maxLog * (T.interactions.map fun i => 2 ^ i.mult.length - 1).sum) ?_
  intro t ht
  rw [tableOf_lt ht]
  exact table_in_multBound A tr pub t ht hlog b send m

/-- The whole multiplicity bound (trace + public) is below `p`, given `Air.multBound < P` and
the static public bound.  This is the P2 shape: `multBoundP AP < P`. -/
theorem multBoundP_lt_of {AP : AirP} (h : AP.multBoundP < P) : AP.multBoundP < P := h



/-! ## The P1 aggregation: per-row, per-table and whole-AIR sums -/

theorem fsum_eq_natCast_sum {α : Type} (l : List α) (f : α → Nat) :
    fsum (l.map fun a => ((f a : Nat) : Fp)) = (((l.map f).sum : Nat) : Fp) :=
  fsum_map_natCast l f
theorem rowSide_eq (is : List Interaction) (tr : Trace Fp) (t r : Nat)
    (pv : List Fp) (bc : Nat) (m : List Fp) (send : Bool)
    (hbits : ∀ i ∈ is, ∀ x ∈ i.mult, x.eval tr t r pv = 0 ∨ x.eval tr t r pv = 1)
    (hlen : ∀ i ∈ is, i.mult.length ≤ 25) :
    fsum (is.map fun i => if i.bus = bc ∧ i.send = send ∧ i.msgVal tr t r pv = m
        then countF i tr t r pv else 0)
      = (((is.map fun i => if i.bus = bc ∧ i.send = send ∧ i.msgVal tr t r pv = m
          then i.multNat tr t r pv else 0).sum : Nat) : Fp) := by
  rw [← fsum_eq_natCast_sum is]
  apply fsum_congr_map
  intro i hi
  by_cases hkey : i.bus = bc ∧ i.send = send ∧ i.msgVal tr t r pv = m
  · rw [if_pos hkey, if_pos hkey, countF_eq_multNat i tr t r pv (hbits i hi) (hlen i hi)]
  · rw [if_neg hkey, if_neg hkey]
    rfl
theorem tableSide_eq (is : List Interaction) (tr : Trace Fp) (t : Nat)
    (pv : List Fp) (bc : Nat) (m : List Fp) (send : Bool)
    (hbits : ∀ r, r < tr.height t → ∀ i ∈ is, ∀ x ∈ i.mult,
      x.eval tr t r pv = 0 ∨ x.eval tr t r pv = 1)
    (hlen : ∀ i ∈ is, i.mult.length ≤ 25) :
    fsum ((List.range (tr.height t)).map fun r =>
        fsum (is.map fun i => if i.bus = bc ∧ i.send = send ∧ i.msgVal tr t r pv = m
          then countF i tr t r pv else 0))
      = ((tableBusCount is tr t pv bc send m : Nat) : Fp) := by
  rw [tableBusCount_eq, ← fsum_eq_natCast_sum]
  apply fsum_congr_map
  intro r hr
  rw [List.mem_range] at hr
  exact rowSide_eq is tr t r pv bc m send (fun i hi => hbits r hr i hi) hlen

theorem rowSum_eq_side_sub (off : Nat) (is : List Interaction) (tr : Trace Fp) (t r : Nat)
    (pv : List Fp) (bc : Nat) (m : List Fp)
    (hbits : ∀ i ∈ is, ∀ x ∈ i.mult, x.eval tr t r pv = 0 ∨ x.eval tr t r pv = 1)
    (hlen : ∀ i ∈ is, i.mult.length ≤ 25) :
    rowSum off is tr t r pv (off + bc) m
      = (((is.map fun i => if i.bus = bc ∧ i.send = true ∧ i.msgVal tr t r pv = m
            then i.multNat tr t r pv else 0).sum : Nat) : Fp)
        - (((is.map fun i => if i.bus = bc ∧ i.send = false ∧ i.msgVal tr t r pv = m
            then i.multNat tr t r pv else 0).sum : Nat) : Fp) := by
  rw [rowSum_eq_sub]
  have hshift : ∀ i : Interaction, (off + i.bus = off + bc) ↔ (i.bus = bc) := by
    intro i; omega
  have hsq : ∀ send : Bool,
      fsum (is.map fun i => if off + i.bus = off + bc ∧ i.msgVal tr t r pv = m ∧ i.send = send
          then countF i tr t r pv else 0)
      = (((is.map fun i => if i.bus = bc ∧ i.send = send ∧ i.msgVal tr t r pv = m
            then i.multNat tr t r pv else 0).sum : Nat) : Fp) := by
    intro send
    have hform : fsum (is.map fun i => if off + i.bus = off + bc ∧ i.msgVal tr t r pv = m ∧ i.send = send
          then countF i tr t r pv else 0)
        = fsum (is.map fun i => if i.bus = bc ∧ i.send = send ∧ i.msgVal tr t r pv = m
          then countF i tr t r pv else 0) := by
      apply fsum_congr_map
      intro i _
      by_cases hb : i.bus = bc
      · have h1 : off + i.bus = off + bc := by omega
        by_cases hs : i.send = send
        · by_cases hm : i.msgVal tr t r pv = m
          · rw [if_pos ⟨h1, hm, hs⟩, if_pos ⟨hb, hs, hm⟩]
          · rw [if_neg (fun hc => hm hc.2.1), if_neg (fun hc => hm hc.2.2)]
        · rw [if_neg (fun hc => hs hc.2.2), if_neg (fun hc => hs hc.2.1)]
      · have h1 : ¬(off + i.bus = off + bc) := by omega
        rw [if_neg (fun hc => h1 hc.1), if_neg (fun hc => h1 (by omega))]
    rw [hform]
    exact rowSide_eq is tr t r pv bc m send hbits hlen
  exact hsq true ▸ hsq false ▸ rfl

theorem tablesSum_split (off : Nat) (AP : AirP) (tr : Trace Fp) (pv : Nat → List Fp)
    (bc : Nat) (m : List Fp) :
    tablesSum off AP tr pv (off + bc) m
      = fsum ((List.range AP.tables.length).map fun t =>
          fsum ((List.range (tr.height t)).map fun r =>
            fsum ((tableAt AP t).interactions.map fun i =>
              if off + i.bus = off + bc ∧ i.msgVal tr t r (pv t) = m
              then signed i.send (countF i tr t r (pv t)) else 0))) :=
  tablesSum_eq_flat off AP tr pv (off + bc) m

theorem tableSide_sub (off : Nat) (is : List Interaction) (tr : Trace Fp) (t : Nat)
    (pv : List Fp) (bc : Nat) (m : List Fp)
    (hbits : ∀ r, r < tr.height t → ∀ i ∈ is, ∀ x ∈ i.mult,
      x.eval tr t r pv = 0 ∨ x.eval tr t r pv = 1)
    (hlen : ∀ i ∈ is, i.mult.length ≤ 25) :
    fsum ((List.range (tr.height t)).map fun r =>
        fsum (is.map fun i => if off + i.bus = off + bc ∧ i.msgVal tr t r pv = m
          then signed i.send (countF i tr t r pv) else 0))
      = ((tableBusCount is tr t pv bc true m : Nat) : Fp)
        - ((tableBusCount is tr t pv bc false m : Nat) : Fp) := by
  have hrow : ∀ r, fsum (is.map fun i => if off + i.bus = off + bc ∧ i.msgVal tr t r pv = m
          then signed i.send (countF i tr t r pv) else 0)
      = fsum (is.map fun i => if i.bus = bc ∧ i.send = true ∧ i.msgVal tr t r pv = m
            then countF i tr t r pv else 0)
        - fsum (is.map fun i => if i.bus = bc ∧ i.send = false ∧ i.msgVal tr t r pv = m
            then countF i tr t r pv else 0) := by
    intro r
    show fsum (is.map fun i => if off + i.bus = off + bc ∧ i.msgVal tr t r pv = m
          then signed i.send (countF i tr t r pv) else 0) = _
    rw [show fsum (is.map fun i => if off + i.bus = off + bc ∧ i.msgVal tr t r pv = m
          then signed i.send (countF i tr t r pv) else 0)
        = fsum (is.map fun i => (if off + i.bus = off + bc ∧ i.msgVal tr t r pv = m ∧ i.send = true
            then countF i tr t r pv else 0)
          - (if off + i.bus = off + bc ∧ i.msgVal tr t r pv = m ∧ i.send = false
            then countF i tr t r pv else 0)) by
      apply fsum_congr_map
      intro i _
      by_cases hk : off + i.bus = off + bc ∧ i.msgVal tr t r pv = m
      · rw [if_pos hk]
        cases hs : i.send
        · rw [signed_eq]
          simp only [hs, if_true, reduceIte, Bool.false_eq_true]
          grind
        · rw [signed_eq]
          simp only [hs, reduceIte, Bool.true_eq_false]
          grind
      · rw [if_neg hk]
        by_cases h1 : off + i.bus = off + bc ∧ i.msgVal tr t r pv = m ∧ i.send = true
        · exact absurd ⟨h1.1, h1.2.1⟩ hk
        · by_cases h2 : off + i.bus = off + bc ∧ i.msgVal tr t r pv = m ∧ i.send = false
          · exact absurd ⟨h2.1, h2.2.1⟩ hk
          · rw [if_neg h1, if_neg h2]; grind]
    rw [fsum_sub_map]
    have hshift : ∀ i : Interaction, (off + i.bus = off + bc) ↔ (i.bus = bc) := by
      intro i; omega
    have hsq : ∀ send : Bool,
        fsum (is.map fun i => if off + i.bus = off + bc ∧ i.msgVal tr t r pv = m ∧ i.send = send
            then countF i tr t r pv else 0)
        = fsum (is.map fun i => if i.bus = bc ∧ i.send = send ∧ i.msgVal tr t r pv = m
            then countF i tr t r pv else 0) := by
      intro send
      apply fsum_congr_map
      intro i _
      by_cases hb : i.bus = bc
      · have h1 : off + i.bus = off + bc := by omega
        by_cases hs : i.send = send
        · by_cases hm : i.msgVal tr t r pv = m
          · rw [if_pos ⟨h1, hm, hs⟩, if_pos ⟨hb, hs, hm⟩]
          · rw [if_neg (fun hc => hm hc.2.1), if_neg (fun hc => hm hc.2.2)]
        · rw [if_neg (fun hc => hs hc.2.2), if_neg (fun hc => hs hc.2.1)]
      · have h1 : ¬(off + i.bus = off + bc) := by omega
        rw [if_neg (fun hc => h1 hc.1), if_neg (fun hc => h1 (by omega))]
    congr 1
    · exact hsq true
    · exact hsq false
  rw [fsum_congr_map (g := fun r =>
      fsum (is.map fun i => if i.bus = bc ∧ i.send = true ∧ i.msgVal tr t r pv = m
            then countF i tr t r pv else 0)
      - fsum (is.map fun i => if i.bus = bc ∧ i.send = false ∧ i.msgVal tr t r pv = m
            then countF i tr t r pv else 0))]
  · rw [fsum_sub_map]
    congr 1
    · exact tableSide_eq is tr t pv bc m true hbits hlen
    · exact tableSide_eq is tr t pv bc m false hbits hlen
  · intro r _
    exact hrow r

theorem tablesSum_eq_sides (off : Nat) (AP : AirP) (tr : Trace Fp) (pv : Nat → List Fp)
    (bc : Nat) (m : List Fp)
    (hbits : ∀ t (ht : t < AP.tables.length), ∀ r, r < tr.height t →
      ∀ i ∈ (tableAt AP t).interactions, ∀ x ∈ i.mult,
        x.eval tr t r (pv t) = 0 ∨ x.eval tr t r (pv t) = 1)
    (hlen : ∀ t (ht : t < AP.tables.length), ∀ i ∈ (tableAt AP t).interactions,
      i.mult.length ≤ 25) :
    tablesSum off AP tr pv (off + bc) m
      = fsum ((List.range AP.tables.length).map fun t =>
          ((tableBusCount (tableAt AP t).interactions tr t (pv t) bc true m : Nat) : Fp))
        - fsum ((List.range AP.tables.length).map fun t =>
          ((tableBusCount (tableAt AP t).interactions tr t (pv t) bc false m : Nat) : Fp)) := by
  rw [tablesSum_eq_flat]
  have hper : ∀ (t : Nat) (ht : t < AP.tables.length), fsum ((List.range (tr.height t)).map fun r =>
        fsum ((tableAt AP t).interactions.map fun i =>
          if off + i.bus = off + bc ∧ i.msgVal tr t r (pv t) = m
          then signed i.send (countF i tr t r (pv t)) else 0))
      = ((tableBusCount (tableAt AP t).interactions tr t (pv t) bc true m : Nat) : Fp)
        - ((tableBusCount (tableAt AP t).interactions tr t (pv t) bc false m : Nat) : Fp) := by
    intro t ht
    apply tableSide_sub off (tableAt AP t).interactions tr t (pv t) bc m
    · intro r hr i hi
      exact hbits t ht r hr i hi
    · intro i hi
      exact hlen t ht i hi
  rw [fsum_congr_map (g := fun t =>
      ((tableBusCount (tableAt AP t).interactions tr t (pv t) bc true m : Nat) : Fp)
      - ((tableBusCount (tableAt AP t).interactions tr t (pv t) bc false m : Nat) : Fp))]
  · rw [fsum_sub_map]
  · intro t ht
    rw [List.mem_range] at ht
    exact hper t ht

theorem sum_congr_list {α : Type} (l : List α) {f g : α → Nat} (h : ∀ x ∈ l, f x = g x) :
    (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    congr 1
    · exact h a (by simp)
    · exact ih (fun x hx => h x (by simp [hx]))
theorem multNat_go_congr (tr : Trace Fp) (t r : Nat) {pv pub : List Fp} :
    ∀ (bs : List Expr) (k : Nat), (∀ e ∈ bs, e.eval tr t r pv = e.eval tr t r pub) →
      Interaction.multNat.go tr t r pv bs k = Interaction.multNat.go tr t r pub bs k
  | [], k, _ => rfl
  | b :: bs, k, h => by
    rw [Interaction.multNat.go, Interaction.multNat.go, h b (by simp),
      multNat_go_congr tr t r bs (k+1) (fun e he => h e (by simp [he]))]
theorem multNat_congr (i : Interaction) (tr : Trace Fp) (t r : Nat) {pv pub : List Fp}
    (h : ∀ e ∈ i.mult, e.eval tr t r pv = e.eval tr t r pub) :
    i.multNat tr t r pv = i.multNat tr t r pub := by
  unfold Interaction.multNat
  exact multNat_go_congr tr t r i.mult 0 h
theorem tableExprAgree (T : Air.Table) (tr : Trace Fp) (t : Nat) {pv pub : List Fp}
    (h : ∀ i, i < tablePubBound T → pv.getD i 0 = pub.getD i 0)
    {e : Expr} (he : e ∈ T.exprs) (r : Nat) :
    e.eval tr t r pv = e.eval tr t r pub := by
  apply eval_eq_of_agree e tr t r
  intro i hi
  apply h i
  unfold tablePubBound
  exact Nat.lt_of_lt_of_le hi (ZkFormal.Udr.Np.le_foldr_max (List.mem_map_of_mem he))
theorem tableBusCount_congr (T : Air.Table) (tr : Trace Fp) (t : Nat) {pv pub : List Fp}
    (h : ∀ i, i < tablePubBound T → pv.getD i 0 = pub.getD i 0)
    (b : Nat) (send : Bool) (m : List Fp) :
    tableBusCount T.interactions tr t pv b send m
      = tableBusCount T.interactions tr t pub b send m := by
  rw [tableBusCount_eq, tableBusCount_eq]
  have hrow : ∀ r ∈ List.range (tr.height t),
      (T.interactions.map fun i => if i.bus = b ∧ i.send = send ∧ i.msgVal tr t r pv = m
        then i.multNat tr t r pv else 0).sum
      = (T.interactions.map fun i => if i.bus = b ∧ i.send = send ∧ i.msgVal tr t r pub = m
        then i.multNat tr t r pub else 0).sum := by
    intro r _
    apply sum_congr_list
    intro i hi
    have hmult : ∀ e ∈ i.mult, e.eval tr t r pv = e.eval tr t r pub := by
      intro e he
      exact tableExprAgree T tr t h (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨i, hi, List.mem_append_left _ he⟩)) r
    have hmsg : i.msgVal tr t r pv = i.msgVal tr t r pub := by
      unfold Interaction.msgVal
      apply List.map_congr_left
      intro e he
      exact tableExprAgree T tr t h (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨i, hi, List.mem_append_right _ he⟩)) r
    rw [hmsg, multNat_congr i tr t r hmult]
  exact sum_congr_list (List.range (tr.height t)) hrow

theorem cast_add_eq_of_lt {a b : Nat} (h : a + b < P) :
    ((a : Nat) : Fp) + ((b : Nat) : Fp) = ((a + b : Nat) : Fp) := by
  change Fp.ofNat a + Fp.ofNat b = Fp.ofNat (a + b)
  rw [ZkFormal.Near.ofNat_add']
theorem nat_eq_of_cast_sub {A B C D : Nat}
    (h1 : A + D < P) (h2 : C + B < P)
    (h : ((A : Nat) : Fp) - ((B : Nat) : Fp) = ((C : Nat) : Fp) - ((D : Nat) : Fp)) :
    A + D = C + B := by
  have h' : ((A : Nat) : Fp) + ((D : Nat) : Fp) = ((C : Nat) : Fp) + ((B : Nat) : Fp) := by
    grind
  rw [cast_add_eq_of_lt h1, cast_add_eq_of_lt h2] at h'
  exact nat_inj_of_lt h1 h2 h'
theorem nat_eq_of_cast_sub_le {A B C D N : Nat}
    (hN : N < P) (h1 : A + D ≤ N) (h2 : C + B ≤ N)
    (h : ((A : Nat) : Fp) - ((B : Nat) : Fp) = ((C : Nat) : Fp) - ((D : Nat) : Fp)) :
    A + D = C + B :=
  nat_eq_of_cast_sub (by omega) (by omega) h

/-- A natural `n < p` casts back through `toNat`. -/
theorem toNat_cast_of_lt {n : Nat} (h : n < P) : (((n : Nat) : Fp)).toNat = n := by
  change (Fp.ofNat n).toNat = n
  rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt h]


/-- `tableAt` is the AIR's table on in-range indices. -/
theorem tableAt_eq (AP : AirP) {t : Nat} (ht : t < AP.tables.length) :
    tableAt AP t = AP.tables[t] := by
  unfold tableAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  rfl

theorem tableOf_toAir_eq (AP : AirP) {t : Nat} (ht : t < AP.tables.length) :
    ZkFormal.Udr.Np.tableOf AP.toAir t = AP.tables[t] := by
  unfold ZkFormal.Udr.Np.tableOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  rfl

/-- `busCount` over the translated AIR equals the sum of the per-table counts at `pv t`, because
public-value agreement makes the `pub` and `pv t` evaluations equal. -/
theorem busCount_eq_tables (AP : AirP) (tr : Trace Fp) (pv : Nat → List Fp) (pub : List Fp)
    (bc : Nat) (send : Bool) (m : List Fp)
    (hagree : ∀ t (ht : t < AP.tables.length), ∀ i, i < tablePubBound AP.tables[t] →
      (pv t).getD i 0 = pub.getD i 0) :
    busCount AP.toAir tr pub bc send m
      = ((List.range AP.tables.length).map fun t =>
          tableBusCount (tableAt AP t).interactions tr t (pv t) bc send m).sum := by
  rw [ZkFormal.Udr.Np.busCount_eq]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [List.mem_range] at ht
  rw [tableOf_toAir_eq AP ht, tableAt_eq AP ht]
  exact (tableBusCount_congr AP.tables[t] tr t (hagree t ht) bc send m).symm

theorem pubCount_le_pubBound (AP : AirP) (pub : List Fp) (hfit : pubFit AP pub = true)
    (hw : ∀ s ∈ AP.pubSegs, 1 ≤ s.width) (b : Nat) (send : Bool) (m : List Fp) :
    pubCount AP pub b send m ≤ AP.pubBound := by
  refine Nat.le_trans (List.length_filter_le _ _) ?_
  exact ZkFormal.V2.Np.pubMsgs_length_le (AP := AP) hfit hw

/-- `netF` is the difference of the two public casts. -/
theorem netF_eq (AP : AirP) (pub : List Fp) (bc : Nat) (m : List Fp) :
    netF AP pub bc m
      = ((pubCount AP pub bc true m : Nat) : Fp)
        - ((pubCount AP pub bc false m : Nat) : Fp) := rfl

/-- `HoldsP`'s two-sided balance, from the field equation with all four counts `< p`. -/
theorem eq_of_field {A B C D : Nat}
    (hac : A + C < P) (hbd : B + D < P)
    (h : ((A:Nat):Fp) - ((B:Nat):Fp) + (((C:Nat):Fp) - ((D:Nat):Fp)) = 0) :
    A + C = B + D := by
  have h' : ((A:Nat):Fp) + ((C:Nat):Fp) = ((B:Nat):Fp) + ((D:Nat):Fp) := by grind
  rw [cast_add_eq_of_lt hac, cast_add_eq_of_lt hbd] at h'
  exact nat_inj_of_lt hac hbd h'


/-- **The balance step**: the LogUp balance, TAPE's net multiplicities, the tables' side identity
and the bound `< p` on both sides give the classical two-sided balance. -/
theorem balance_step (off : Nat) (AP : AirP) (pub : List Fp) (pv : Nat → List Fp)
    (tr : Trace Fp) (tape : Tape) (bc : Nat) (m : List Fp)
    (hbound : ∀ send, busCount AP.toAir tr pub bc send m + pubCount AP pub bc send m < P)
    (hb : tablesSum off AP tr pv (off + bc) m + tapeSum tape (off + bc) m = 0)
    (hnet : tapeSum tape (off + bc) m = netF AP pub bc m)
    (hsides : tablesSum off AP tr pv (off + bc) m
      = ((busCount AP.toAir tr pub bc true m : Nat) : Fp)
        - ((busCount AP.toAir tr pub bc false m : Nat) : Fp)) :
    busCount AP.toAir tr pub bc true m + pubCount AP pub bc true m
      = busCount AP.toAir tr pub bc false m + pubCount AP pub bc false m := by
  have hzero : ((busCount AP.toAir tr pub bc true m : Nat) : Fp)
      - ((busCount AP.toAir tr pub bc false m : Nat) : Fp)
      + (((pubCount AP pub bc true m : Nat) : Fp) - ((pubCount AP pub bc false m : Nat) : Fp)) = 0 := by
    have e1 : ((busCount AP.toAir tr pub bc true m : Nat) : Fp)
        - ((busCount AP.toAir tr pub bc false m : Nat) : Fp) = tablesSum off AP tr pv (off + bc) m :=
      hsides.symm
    have e2 : (((pubCount AP pub bc true m : Nat) : Fp) - ((pubCount AP pub bc false m : Nat) : Fp))
        = tapeSum tape (off + bc) m := by
      rw [show ((pubCount AP pub bc true m : Nat) : Fp) - ((pubCount AP pub bc false m : Nat) : Fp)
          = netF AP pub bc m from (netF_eq AP pub bc m).symm, hnet]
    rw [e1, e2]
    exact hb
  exact eq_of_field (hbound true) (hbound false) hzero


/-- A side count is at most `multBoundP` when the heights respect the caps. -/
theorem busCount_le_multBoundP (AP : AirP) (tr : Trace Fp) (pub : List Fp)
    (hlog : ∀ t (ht : t < AP.tables.length), tr.log t ≤ AP.tables[t].maxLog)
    (bc : Nat) (send : Bool) (m : List Fp) :
    busCount AP.toAir tr pub bc send m ≤ AP.multBoundP :=
  Nat.le_trans (busCount_le_multBound AP.toAir tr pub hlog bc send m) AP.multBound_le

/-- **P1: the SWIRL relation implies `HoldsP`.**

Given the SWIRL PIOP relation (`SwirlRel`, assumption P5), the light verifier's checks
(`VdChecks`), the multiplicity bound `multBoundP AP < p`, and fitting public segments, the
classical `HoldsP AP pub tr` holds.  Every step is proved: the constraints and bits transfer
because they are the same expressions evaluated at agreeing public values; the balance transfers
because both sides are bounded by `multBoundP < p`, so the mod-p LogUp equality is an equality of
naturals.

The only hypothesis that is not a theorem is `SwirlRel` itself — that is SWIRL's soundness (P5),
shared with every PQ AIR and not formalised for any of them. -/
theorem holdsP_of_swirl (off : Nat) (AP : AirP) (pub : List Fp) (pv : Nat → List Fp)
    (tr : Trace Fp) (tape : Tape)
    (hmult : AP.multBoundP < P)
    (hs : SwirlRel off AP pv tr tape)
    (hv : VdChecks off AP pub pv tr tape)
    (hfitW : ∀ s ∈ AP.pubSegs, 1 ≤ s.width)
    (hlen25 : ∀ t (ht : t < AP.tables.length), ∀ i ∈ AP.tables[t].interactions,
      i.mult.length ≤ 25) :
    HoldsP AP pub tr := by
  have hagree : ∀ t (ht : t < AP.tables.length),
      ∀ i, i < tablePubBound AP.tables[t] → (pv t).getD i 0 = pub.getD i 0 :=
    fun t ht => hv.pvAgree t ht
  have hlog : ∀ t (ht : t < AP.tables.length), tr.log t ≤ AP.tables[t].maxLog :=
    fun t ht => hv.logCap t ht
  have hbitsP : ∀ t (ht : t < AP.tables.length), ∀ r, r < tr.height t →
      ∀ i ∈ (tableAt AP t).interactions, ∀ x ∈ i.mult,
        x.eval tr t r (pv t) = 0 ∨ x.eval tr t r (pv t) = 1 := by
    intro t ht r hr i hi x hx
    rw [tableAt_eq AP ht] at hi
    exact bits_of_swirl hs t ht r hr i hi x hx
  refine ⟨?_, ?_, ?_, hv.pubFit, ?_⟩
  · -- heights: `SwirlRel` gives `2 ≤ log`, `VdChecks` gives the cap
    intro t ht
    exact ⟨by have := (hs.logBound t ht).1; omega, hv.logCap t ht⟩
  · -- constraints: same expressions, agreeing public values
    intro t ht r hr e he
    rw [← eval_eq_of_agree e tr t r (pv := pv t) (fun i hi => hagree t ht i (by
      unfold tablePubBound
      exact Nat.lt_of_lt_of_le hi (ZkFormal.Udr.Np.le_foldr_max (List.mem_map_of_mem
        (List.mem_append_left _ he)))))]
    exact hs.constr t ht r hr e (List.mem_append_left _ he)
  · -- bits: booleanity constraints in `allConstraints`, evaluated at `pub`
    intro t ht r hr i hi b hb
    have hb0 := bits_of_swirl hs t ht r hr i hi b hb
    have hbpub := hb0
    have hag := eval_eq_of_agree b tr t r (pv := pv t) (pub := pub) (fun k hk => hagree t ht k (by
      unfold tablePubBound
      exact Nat.lt_of_lt_of_le hk (ZkFormal.Udr.Np.le_foldr_max (List.mem_map_of_mem
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, hi, List.mem_append_left _ hb⟩))))))
    rw [hag] at hbpub
    exact hbpub
  · -- balance: mod-p ⇒ ℕ
    intro b m
    have hb := hs.balance (off + b) m
    have hnet := hv.tape b m
    have hsides0 := tablesSum_eq_sides off AP tr pv b m hbitsP
      (fun t ht i hi => hlen25 t ht i (by rwa [tableAt_eq AP ht] at hi))
    -- the two `fsum` heads are casts of the AIR's `busCount` on each side
    have bcT := busCount_eq_tables AP tr pv pub b true m (fun t ht => hv.pvAgree t ht)
    have bcF := busCount_eq_tables AP tr pv pub b false m (fun t ht => hv.pvAgree t ht)
    have hT : fsum ((List.range AP.tables.length).map fun t =>
        ((tableBusCount (tableAt AP t).interactions tr t (pv t) b true m : Nat) : Fp))
        = ((busCount AP.toAir tr pub b true m : Nat) : Fp) := by
      rw [fsum_eq_natCast_sum]
      exact congrArg (fun n => ((n : Nat) : Fp)) bcT.symm
    have hF : fsum ((List.range AP.tables.length).map fun t =>
        ((tableBusCount (tableAt AP t).interactions tr t (pv t) b false m : Nat) : Fp))
        = ((busCount AP.toAir tr pub b false m : Nat) : Fp) := by
      rw [fsum_eq_natCast_sum]
      exact congrArg (fun n => ((n : Nat) : Fp)) bcF.symm
    have hsides : tablesSum off AP tr pv (off + b) m
        = ((busCount AP.toAir tr pub b true m : Nat) : Fp)
          - ((busCount AP.toAir tr pub b false m : Nat) : Fp) := by
      rw [hsides0, hT, hF]
    have hbound : ∀ send, busCount AP.toAir tr pub b send m + pubCount AP pub b send m < P := by
      intro send
      have h1 := busCount_le_multBound AP.toAir tr pub hlog b send m
      have h2 := pubCount_le_pubBound AP pub hv.pubFit hfitW b send m
      have h3 : AP.multBound + AP.pubBound < P := hmult
      unfold AirP.multBoundP at h3
      omega
    exact balance_step off AP pub pv tr tape b m hbound hb hnet hsides
end ZkFormal.PQ.StatePort
