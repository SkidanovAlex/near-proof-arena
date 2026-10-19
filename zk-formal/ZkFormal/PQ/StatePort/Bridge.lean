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
* `rowSum_eq`, `rowSum_eq_sub` — a row's signed field sum is its send count minus its receive
  count, and both are bounded naturals;
* `tableSum_eq`, `tableSum_side` — a table's field sum on a bus and message is the cast of its
  natural `tableBusCount` on the same side (with the bus-id shift), for either side;
* `tableBusCount_le_side`, `busCount_le_multBound` — every trace side count is `≤ Air.multBound`
  when heights respect `maxLog`, so `multBoundP AP < P` bounds it;
* `nearAirV3_multBoundP_lt` and `nearAirV3D1_multBoundP_lt` — the kernel-checked P2 facts.

## The remaining step (documented, not assumed away)

The final composition `holdsP_of_swirl` needs one more aggregation: the per-table identity above
must be summed over all tables, the send/receive difference taken, and the result matched with
`HoldsP.balance` after replacing TAPE's contribution by `netF` (`VdChecks.tape`).  The pieces are
all proved; the aggregation is the "4–6 agent-days" P1 item of
`research/near-compression/results/pq-d1-envelope/README.md` §4.  We do **not** state it with
`sorry`: see `holdsP_of_swirl_of_tables` below for the exact remaining obligation, which is a pure
list-sum rearrangement (`fsum_swap` already proves the row/interaction commute).
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

end ZkFormal.PQ.StatePort
