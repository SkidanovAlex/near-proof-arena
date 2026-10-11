import ZkFormal.NearV3.Tables.UnfoldA7
import ZkFormal.Near.Extract.Eval
import ZkFormal.Near.Extract.BusCount
import ZkFormal.NearV3.Rcpt.Extract.SizeProof

/-!
# ZkFormal.NearV3.Render.UnfoldA7Ext — renders of the A7 extension tables

The A7 tables (`Tables/UnfoldA7.lean`) extend `nodeV3`, `valV3`, `upsV3`, `sizeV3` by columns at
and above the base width.  An honest trace of an extension is the base trace with those
columns filled (`Trace.withCols`): every base expression reads only columns below the base
width (`Table.wf`), so the base constraints, multiplicity bits and traffic are unchanged
(`eval_withCols`, `tableBusCount_withCols`), and only the appended constraints/interactions
need the new cells.  This module proves that generically and fills the new columns of
`nodeA7` (`rpl` free per record, `ra` the prefix sum) and `valA7` (`rplv`, `rb`).
-/

namespace ZkFormal.NearV3.UnfoldA7

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl

/-- Table `t` of `tr` with the columns `≥ w` replaced by `f`. -/
def Trace.withCols (tr : Trace Fp) (t w : Nat) (f : Nat → Nat → Fp) : Trace Fp :=
  ⟨tr.log, fun t' r col => if t' = t ∧ w ≤ col then f r col else tr.cell t' r col⟩

theorem height_withCols (tr : Trace Fp) (t w : Nat) (f : Nat → Nat → Fp) (t' : Nat) :
    (Trace.withCols tr t w f).height t' = tr.height t' := rfl

theorem cell_withCols_lt {tr : Trace Fp} {t w : Nat} {f : Nat → Nat → Fp} {r col : Nat}
    (h : col < w) : (Trace.withCols tr t w f).cell t r col = tr.cell t r col := by
  simp [Trace.withCols]; omega

theorem cell_withCols_ge {tr : Trace Fp} {t w : Nat} {f : Nat → Nat → Fp} {r col : Nat}
    (h : w ≤ col) : (Trace.withCols tr t w f).cell t r col = f r col := by
  simp [Trace.withCols, h]

/-- An expression reading only columns below `w` does not see the new columns. -/
theorem eval_withCols (tr : Trace Fp) (t w : Nat) (f : Nat → Nat → Fp) (r : Nat) (pub : List Fp) :
    ∀ e : Expr, e.colBound ≤ w → e.eval (Trace.withCols tr t w f) t r pub = e.eval tr t r pub
  | .const _, _ => rfl
  | .pub _, _ => rfl
  | .isFirst, _ => rfl
  | .isLast, _ => rfl
  | .isTransition, _ => rfl
  | .col x nx, h => by
    simp only [Expr.colBound] at h
    show (Trace.withCols tr t w f).cell t _ x = tr.cell t _ x
    exact cell_withCols_lt (by omega)
  | .add a b, h => by
    simp only [Expr.colBound, Nat.max_le] at h
    rw [eval_add, eval_add, eval_withCols tr t w f r pub a h.1, eval_withCols tr t w f r pub b h.2]
  | .mul a b, h => by
    simp only [Expr.colBound, Nat.max_le] at h
    rw [eval_mul, eval_mul, eval_withCols tr t w f r pub a h.1, eval_withCols tr t w f r pub b h.2]
  | .neg a, h => by
    simp only [Expr.colBound] at h
    rw [eval_neg, eval_neg, eval_withCols tr t w f r pub a h]

/-- Interactions whose expressions read only columns below `w` have unchanged traffic. -/
theorem tableBusCount_withCols (tr : Trace Fp) (t w : Nat) (f : Nat → Nat → Fp) (pub : List Fp)
    (is : List Interaction) (hw : ∀ i ∈ is, ∀ e ∈ i.mult ++ i.msg, e.colBound ≤ w)
    (b : Nat) (s : Bool) (m : List Fp) :
    tableBusCount is (Trace.withCols tr t w f) t pub b s m = tableBusCount is tr t pub b s m := by
  have hmult : ∀ i ∈ is, ∀ r, i.multNat (Trace.withCols tr t w f) t r pub = i.multNat tr t r pub := by
    intro i hi r
    unfold Interaction.multNat
    have : ∀ (es : List Expr) (k : Nat), (∀ e ∈ es, e.colBound ≤ w) →
        Interaction.multNat.go (Trace.withCols tr t w f) t r pub es k =
          Interaction.multNat.go tr t r pub es k := by
      intro es
      induction es with
      | nil => intro _ _; rfl
      | cons e es ih =>
        intro k he
        simp only [Interaction.multNat.go]
        rw [eval_withCols tr t w f r pub e (he e (by simp)), ih (k + 1) (fun e' h' => he e' (by simp [h']))]
    exact this i.mult 0 (fun e he => hw i hi e (List.mem_append_left _ he))
  have hmsg : ∀ i ∈ is, ∀ r, i.msgVal (Trace.withCols tr t w f) t r pub = i.msgVal tr t r pub := by
    intro i hi r
    unfold Interaction.msgVal
    apply List.map_congr_left
    intro e he
    exact eval_withCols tr t w f r pub e (hw i hi e (List.mem_append_right _ he))
  have hrow : ∀ r, rowTraffic is (Trace.withCols tr t w f) t r pub b s = rowTraffic is tr t r pub b s := by
    intro r
    unfold rowTraffic
    clear hw
    induction is with
    | nil => rfl
    | cons i is ih =>
      simp only [List.flatMap_cons]
      rw [hmult i (by simp) r, hmsg i (by simp) r,
        ih (fun i' h' => hmult i' (by simp [h'])) (fun i' h' => hmsg i' (by simp [h']))]
  simp only [tableBusCount_eq, height_withCols, hrow]

/-- `T` with `cs` / `js` appended and width `w'`. -/
def extTable (T : Table) (w' : Nat) (cs : List Expr) (js : List Interaction) : Table :=
  { T with
    width := w'
    constraints := T.constraints ++ cs
    interactions := T.interactions ++ js }

/-- **Extension render.** The base table's local legality on `tr`, the base expressions reading
only columns below `w`, and the appended constraints / multiplicity bits on the filled trace
give the extension's local legality on the filled trace. -/
theorem tableLocal_withCols {T : Table} {cs : List Expr} {js : List Interaction} {w' : Nat}
    {tr : Trace Fp} {t : Nat} {pub : List Fp} {w : Nat} {f : Nat → Nat → Fp}
    (hL : TableLocal T tr t pub) (hw : ∀ e ∈ T.exprs, e.colBound ≤ w)
    (hc : ∀ r, r < tr.height t → ∀ e ∈ cs, e.eval (Trace.withCols tr t w f) t r pub = 0)
    (hb : ∀ r, r < tr.height t → ∀ i ∈ js, ∀ b ∈ i.mult,
      b.eval (Trace.withCols tr t w f) t r pub = 0 ∨ b.eval (Trace.withCols tr t w f) t r pub = 1) :
    TableLocal (extTable T w' cs js) (Trace.withCols tr t w f) t pub := by
  refine ⟨hL.log_ge, hL.log_le, ?_, ?_⟩
  · intro r hr e he
    rcases List.mem_append.1 he with he | he
    · rw [eval_withCols tr t w f r pub e (hw e (List.mem_append_left _ he))]
      exact hL.constr r hr e he
    · exact hc r hr e he
  · intro r hr i hi b hbm
    rcases List.mem_append.1 hi with hi | hi
    · have hb' : b.colBound ≤ w := hw b (List.mem_append_right _
        (List.mem_flatMap.2 ⟨i, hi, List.mem_append_left _ hbm⟩))
      rw [eval_withCols tr t w f r pub b hb']
      exact hL.bits r hr i hi b hbm
    · exact hb r hr i hi b hbm

end ZkFormal.NearV3.UnfoldA7

namespace ZkFormal.NearV3.UnfoldA7

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl

theorem nodeA7_eq : nodeA7 = extTable ZkFormal.NearV3.NodeV3.tableU Node.width Node.constraints
    Node.interactions := rfl
theorem valA7_eq : valA7 = extTable ZkFormal.NearV3.ValV3.table Val.width Val.constraints
    Val.interactions := rfl

/-- The base `nodeV3` expressions read only columns `< 186`. -/
theorem node_colBound : ∀ e ∈ ZkFormal.NearV3.NodeV3.tableU.exprs, e.colBound ≤ 186 := by
  have h : ZkFormal.NearV3.NodeV3.tableU.exprs.all (fun e => decide (e.colBound ≤ 186)) = true := by
    decide +kernel
  intro e he; simpa using List.all_eq_true.1 h e he

/-- The base `valV3` expressions read only columns `< 15`. -/
theorem val_colBound : ∀ e ∈ ZkFormal.NearV3.ValV3.table.exprs, e.colBound ≤ 15 := by
  have h : ZkFormal.NearV3.ValV3.table.exprs.all (fun e => decide (e.colBound ≤ 15)) = true := by
    decide +kernel
  intro e he; simpa using List.all_eq_true.1 h e he

/-- A prefix sum over rows. -/
def prefixF (g : Nat → Fp) : Nat → Fp
  | 0 => 0
  | r + 1 => prefixF g r + g r

/-! ## `nodeA7` -/

section Node
open ZkFormal.NearV3.NodeV3

/-- The replaced flag of row `r` for a choice `sel` (only on a record's first row). -/
def nodeRpl (tr : Trace Fp) (t : Nat) (sel : Nat → Bool) (r : Nat) : Fp :=
  if sel r = true ∧ tr.cell t r nf = 1 then 1 else 0

/-- The per-row increment of `ra`. -/
def nodeInc (tr : Trace Fp) (t : Nat) (sel : Nat → Bool) (r : Nat) : Fp :=
  2 * tr.cell t r act - tr.cell t r nf * nodeRpl tr t sel r * tr.cell t r len

/-- The honest new columns of `nodeA7`. -/
def nodeCols (tr : Trace Fp) (t : Nat) (sel : Nat → Bool) (r col : Nat) : Fp :=
  if col = Node.rpl then nodeRpl tr t sel r
  else if col = Node.ra then prefixF (nodeInc tr t sel) r else 0

/-- **`nodeA7` render**: any legal `nodeV3` table with the honest new columns (any choice of
replaced records) is a legal `nodeA7` table. -/
theorem nodeA7_local {tr : Trace Fp} {t : Nat} {pub : List Fp} (sel : Nat → Bool)
    (hL : TableLocal ZkFormal.NearV3.NodeV3.tableU tr t pub) :
    TableLocal nodeA7 (Trace.withCols tr t 186 (nodeCols tr t sel)) t pub := by
  rw [nodeA7_eq]
  have cR : ∀ r, (Trace.withCols tr t 186 (nodeCols tr t sel)).cell t r Node.rpl = nodeRpl tr t sel r :=
    fun r => by rw [cell_withCols_ge (by decide)]; simp [nodeCols]
  have cA : ∀ r, (Trace.withCols tr t 186 (nodeCols tr t sel)).cell t r Node.ra =
      prefixF (nodeInc tr t sel) r :=
    fun r => by rw [cell_withCols_ge (by decide)]; simp [nodeCols, Node.rpl, Node.ra]
  have cB : ∀ r x, x < 186 → (Trace.withCols tr t 186 (nodeCols tr t sel)).cell t r x = tr.cell t r x :=
    fun r x hx => cell_withCols_lt hx
  have rB : ∀ r, nodeRpl tr t sel r = 0 ∨ nodeRpl tr t sel r = 1 := by
    intro r; unfold nodeRpl; split <;> simp
  refine tableLocal_withCols hL node_colBound ?_ ?_
  · intro r hr e he
    simp only [Node.constraints, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · simp only [eval_bool, eval_c, cR]
      rcases rB r with h | h <;> rw [h] <;> grind
    · simp only [eval_mul, eval_c, eval_isFirst, cA]
      split
      · subst_vars; simp only [prefixF]; grind
      · grind
    · simp only [eval_mul, eval_sub, eval_add, eval_smul, eval_mul3, eval_c, eval_n, eval_isTransition,
        height_withCols, cA, cR, cB _ act (by decide), cB _ nf (by decide), cB _ len (by decide)]
      by_cases hx : r + 1 = tr.height t
      · simp only [hx, ite_true]; grind
      · simp only [hx, ite_false]
        rw [Nat.mod_eq_of_lt (by omega)]
        simp only [prefixF, nodeInc]
        grind
  · intro r hr i hi b hb
    simp only [Node.interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · simp only [Dsl.recv, List.mem_singleton] at hb
      subst hb
      simp only [eval_mul, eval_c, cR, cB _ nf (by decide)]
      unfold nodeRpl; split
      · rename_i h; rw [h.2]; grind
      · grind
    · simp only [Dsl.send, List.mem_singleton] at hb
      subst hb
      simp only [eval_c, cB _ sumr (by decide)]
      exact hL.bits r hr (send B_SIZE (c sumr) [k 0, c sz])
        (by simp [ZkFormal.NearV3.NodeV3.table, ZkFormal.NearV3.NodeV3.interactions]) (c sumr) (by simp [Dsl.send])
end Node

/-! ## `valA7` -/

section Val
open ZkFormal.NearV3.ValV3

def valRpl (tr : Trace Fp) (t : Nat) (sel : Nat → Bool) (r : Nat) : Fp :=
  if sel r = true ∧ tr.cell t r vf = 1 then 1 else 0

def valInc (tr : Trace Fp) (t : Nat) (sel : Nat → Bool) (r : Nat) : Fp :=
  2 * tr.cell t r gb - tr.cell t r vf * valRpl tr t sel r * tr.cell t r len

def valCols (tr : Trace Fp) (t : Nat) (sel : Nat → Bool) (r col : Nat) : Fp :=
  if col = Val.rplv then valRpl tr t sel r
  else if col = Val.rb then prefixF (valInc tr t sel) r else 0

/-- **`valA7` render**: any legal `valV3` table with the honest new columns. -/
theorem valA7_local {tr : Trace Fp} {t : Nat} {pub : List Fp} (sel : Nat → Bool)
    (hL : TableLocal ZkFormal.NearV3.ValV3.table tr t pub) :
    TableLocal valA7 (Trace.withCols tr t 15 (valCols tr t sel)) t pub := by
  rw [valA7_eq]
  have cR : ∀ r, (Trace.withCols tr t 15 (valCols tr t sel)).cell t r Val.rplv = valRpl tr t sel r :=
    fun r => by rw [cell_withCols_ge (by decide)]; simp [valCols]
  have cA : ∀ r, (Trace.withCols tr t 15 (valCols tr t sel)).cell t r Val.rb =
      prefixF (valInc tr t sel) r :=
    fun r => by rw [cell_withCols_ge (by decide)]; simp [valCols, Val.rplv, Val.rb]
  have cB : ∀ r x, x < 15 → (Trace.withCols tr t 15 (valCols tr t sel)).cell t r x = tr.cell t r x :=
    fun r x hx => cell_withCols_lt hx
  have rB : ∀ r, valRpl tr t sel r = 0 ∨ valRpl tr t sel r = 1 := by
    intro r; unfold valRpl; split <;> simp
  refine tableLocal_withCols hL val_colBound ?_ ?_
  · intro r hr e he
    simp only [Val.constraints, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · simp only [eval_bool, eval_c, cR]
      rcases rB r with h | h <;> rw [h] <;> grind
    · simp only [eval_mul, eval_c, eval_isFirst, cA]
      split
      · subst_vars; simp only [prefixF]; grind
      · grind
    · simp only [eval_mul, eval_sub, eval_add, eval_smul, eval_mul3, eval_c, eval_n, eval_isTransition,
        height_withCols, cA, cR, cB _ gb (by decide), cB _ vf (by decide), cB _ len (by decide)]
      by_cases hx : r + 1 = tr.height t
      · simp only [hx, ite_true]; grind
      · simp only [hx, ite_false]
        rw [Nat.mod_eq_of_lt (by omega)]
        simp only [prefixF, valInc]
        grind
  · intro r hr i hi b hb
    simp only [Val.interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · simp only [Dsl.recv, List.mem_singleton] at hb
      subst hb
      simp only [eval_mul, eval_c, cR, cB _ vf (by decide)]
      unfold valRpl; split
      · rename_i h; rw [h.2]; grind
      · grind
    · simp only [Dsl.send, List.mem_singleton] at hb
      subst hb
      simp only [eval_c, cB _ sumr (by decide)]
      exact hL.bits r hr (send B_SIZE (c sumr) [k 1, c sz])
        (by simp [ZkFormal.NearV3.ValV3.table, ZkFormal.NearV3.ValV3.interactions]) (c sumr) (by simp [Dsl.send])
end Val

/-! ## `upsA7` -/

section Ups
open ZkFormal.NearV3.UpsV3

theorem upsA7_eq : upsA7 = extTable ZkFormal.NearV3.UpsV3.table Ups.width Ups.constraints
    Ups.interactions := rfl

theorem ups_colBound : ∀ e ∈ ZkFormal.NearV3.UpsV3.table.exprs, e.colBound ≤ 200 := by
  have h : ZkFormal.NearV3.UpsV3.table.exprs.all (fun e => decide (e.colBound ≤ 200)) = true := by
    decide +kernel
  intro e he; simpa using List.all_eq_true.1 h e he

/-- The terminal record of the segment, as on its first row. -/
def upsND (tr : Trace Fp) (t r : Nat) : Fp :=
  tr.cell t r dd0 * tr.cell t r N0 + (tr.cell t r dd1 * tr.cell t r N1 + (tr.cell t r dd2 * tr.cell t r N2 + 0))

/-- The honest new columns of `upsA7`. -/
def upsCols (tr : Trace Fp) (t : Nat) (r col : Nat) : Fp :=
  if col = Ups.s then prefixF (fun q => tr.cell t q vb + tr.cell t q qb) r
  else if col = Ups.nD then upsND tr t r else 0

theorem ups_con {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL : TableLocal ZkFormal.NearV3.UpsV3.table tr t pub) {r : Nat} (hr : r < tr.height t)
    {e : Expr} (he : e ∈ ZkFormal.NearV3.UpsV3.constraints) : e.eval tr t r pub = 0 :=
  hL.constr r hr e he

/-- **`upsA7` render**: any legal `upsV3` table with the honest new columns. -/
theorem upsA7_local {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL : TableLocal ZkFormal.NearV3.UpsV3.table tr t pub) :
    TableLocal upsA7 (Trace.withCols tr t 200 (upsCols tr t)) t pub := by
  rw [upsA7_eq]
  have cS : ∀ r, (Trace.withCols tr t 200 (upsCols tr t)).cell t r Ups.s =
      prefixF (fun q => tr.cell t q vb + tr.cell t q qb) r :=
    fun r => by rw [cell_withCols_ge (by decide)]; simp [upsCols]
  have cD : ∀ r, (Trace.withCols tr t 200 (upsCols tr t)).cell t r Ups.nD = upsND tr t r :=
    fun r => by rw [cell_withCols_ge (by decide)]; simp [upsCols, Ups.s, Ups.nD]
  have cB : ∀ r x, x < 200 → (Trace.withCols tr t 200 (upsCols tr t)).cell t r x = tr.cell t r x :=
    fun r x hx => cell_withCols_lt hx
  -- base booleans
  have memC : ∀ e, e ∈ cBool → e ∈ ZkFormal.NearV3.UpsV3.constraints := fun e h => by
    unfold ZkFormal.NearV3.UpsV3.constraints; iterate 9 apply List.mem_append_left
    exact h
  have bR : ∀ r, r < tr.height t → ∀ x ∈ rowBools, tr.cell t r x = 0 ∨ tr.cell t r x = 1 := by
    intro r hr x hx
    have := ups_con hL hr (e := Dsl.bool (c x)) (memC _ (by
      unfold cBool; iterate 7 apply List.mem_append_left
      exact List.mem_map_of_mem hx))
    simp only [eval_bool, eval_c] at this
    exact bool_cases this
  have bS : ∀ r, r < tr.height t → ∀ x ∈ segBools,
      tr.cell t r sf * (tr.cell t r x * (tr.cell t r x - 1)) = 0 := by
    intro r hr x hx
    have := ups_con hL hr (e := Expr.mul (c sf) (Dsl.bool (c x))) (memC _ (by
      unfold cBool; iterate 6 apply List.mem_append_left
      exact List.mem_append_right _ (List.mem_map_of_mem (f := fun x => Expr.mul (c sf) (Dsl.bool (c x))) hx)))
    simpa only [eval_mul, eval_bool, eval_c] using this
  have bP : ∀ r, r < tr.height t → ∀ x ∈ partBools,
      tr.cell t r pf * (tr.cell t r x * (tr.cell t r x - 1)) = 0 := by
    intro r hr x hx
    have := ups_con hL hr (e := Expr.mul (c pf) (Dsl.bool (c x))) (memC _ (by
      unfold cBool; iterate 5 apply List.mem_append_left
      exact List.mem_append_right _ (List.mem_map_of_mem (f := fun x => Expr.mul (c pf) (Dsl.bool (c x))) hx)))
    simpa only [eval_mul, eval_bool, eval_c] using this
  have gate : ∀ a b : Fp, (a = 0 ∨ a = 1) → a * (b * (b - 1)) = 0 → a * b = 0 ∨ a * b = 1 := by
    intro a b ha h
    rcases ha with rfl | rfl
    · left; grind
    · have : b * (b - 1) = 0 := by grind
      rcases bool_cases this with hb | hb
      · left; rw [hb]; grind
      · right; rw [hb]; grind
  refine tableLocal_withCols hL ups_colBound ?_ ?_
  · intro r hr e he
    simp only [Ups.constraints, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · simp only [eval_mul, eval_c, eval_isFirst, cS]
      split
      · subst_vars; simp only [prefixF]; grind
      · grind
    · simp only [eval_mul, eval_sub, eval_add, eval_c, eval_n, eval_isTransition, height_withCols, cS,
        cB _ vb (by decide), cB _ qb (by decide)]
      by_cases hx : r + 1 = tr.height t
      · simp only [hx, ite_true]; grind
      · simp only [hx, ite_false]
        rw [Nat.mod_eq_of_lt (by omega)]
        simp only [prefixF]
        grind
    · simp only [eval_mul, eval_sub, eval_c, eval_sum_cons, eval_sum_nil, cD,
        cB _ sf (by decide), cB _ dd0 (by decide), cB _ dd1 (by decide), cB _ dd2 (by decide),
        cB _ N0 (by decide), cB _ N1 (by decide), cB _ N2 (by decide), upsND]
      grind
  · intro r hr i hi b hb
    simp only [Ups.interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · simp only [Dsl.send, List.mem_singleton] at hb; subst hb
      simp only [eval_mul, eval_c, cB _ pf (by decide), cB _ up (by decide)]
      exact gate _ _ (bR r hr pf (by decide)) (bP r hr up (by decide))
    · simp only [Dsl.send, List.mem_singleton] at hb; subst hb
      simp only [eval_c, cB _ sf (by decide)]
      exact bR r hr sf (by decide)
    · simp only [Dsl.send, List.mem_singleton] at hb; subst hb
      simp only [eval_mul, eval_c, cB _ sf (by decide), cB _ pres (by decide)]
      exact gate _ _ (bR r hr sf (by decide)) (bS r hr pres (by decide))
    · simp only [Dsl.send, List.mem_singleton] at hb; subst hb
      simp only [eval_isLast]
      split <;> simp

end Ups

/-! ## `sizeA7` -/

section Size
open ZkFormal.NearV3.SizeV3

theorem sizeA7_eq : sizeA7 = extTable { ZkFormal.NearV3.SizeV3.table with maxLog := 4 } Size.width
    Size.constraints Size.interactions := rfl

theorem size_colBound : ∀ e ∈ ({ ZkFormal.NearV3.SizeV3.table with maxLog := 4 } : Table).exprs,
    e.colBound ≤ 31 := by
  have h : ({ ZkFormal.NearV3.SizeV3.table with maxLog := 4 } : Table).exprs.all
      (fun e => decide (e.colBound ≤ 31)) = true := by decide +kernel
  intro e he; simpa using List.all_eq_true.1 h e he

theorem bitsVal_congr {v v' : Nat → Nat} {off : Nat} :
    ∀ len, (∀ b, b < len → v (off + b) = v' (off + b)) → bitsVal v off len = bitsVal v' off len
  | 0, _ => rfl
  | len + 1, h => by
    simp only [bitsVal]
    rw [bitsVal_congr len (fun b hb => h b (by omega)), h len (by omega)]

theorem bitsVal_mod (v : Nat) : ∀ len, bitsVal (fun b => v / 2 ^ b % 2) 0 len = v % 2 ^ len
  | 0 => by simp [bitsVal, Nat.mod_one]
  | len + 1 => by
    rw [bitsVal, bitsVal_mod v len, Nat.zero_add, Nat.pow_succ]
    rw [Nat.mod_mul, Nat.mul_comm (2 ^ len)]

/-- The running total of the received A7 tags. -/
def sizeU (yN : Nat → Nat) (r : Nat) : Nat := ((List.range (r + 1)).map yN).sum

/-- The honest new columns of `sizeA7`: `y` the received A7 total of the row, `u` the running
sum, `ub` the bits of `B0 − u`. -/
def sizeCols (yN : Nat → Nat) (r col : Nat) : Fp :=
  if col = Size.y then ((yN r : Nat) : Fp)
  else if col = Size.u then ((sizeU yN r : Nat) : Fp)
  else if Size.ub 0 ≤ col ∧ col < Size.ub 24 then (((B0 - sizeU yN r) / 2 ^ (col - 33) % 2 : Nat) : Fp)
  else 0

/-- **`sizeA7` render**: a legal `sizeV3` table (cap `2^4`) with the received A7 totals `yN`
whose running sum is `≤ B0` on the last active row. -/
theorem sizeA7_local {tr : Trace Fp} {t : Nat} {pub : List Fp} (yN : Nat → Nat)
    (hL : TableLocal { ZkFormal.NearV3.SizeV3.table with maxLog := 4 } tr t pub)
    (hB : ∀ r, r < tr.height t → tr.cell t r la = 1 → sizeU yN r ≤ B0) :
    TableLocal sizeA7 (Trace.withCols tr t 31 (sizeCols yN)) t pub := by
  rw [sizeA7_eq]
  have cY : ∀ r, (Trace.withCols tr t 31 (sizeCols yN)).cell t r Size.y = ((yN r : Nat) : Fp) :=
    fun r => by rw [cell_withCols_ge (by decide)]; simp [sizeCols]
  have cU : ∀ r, (Trace.withCols tr t 31 (sizeCols yN)).cell t r Size.u = ((sizeU yN r : Nat) : Fp) :=
    fun r => by rw [cell_withCols_ge (by decide)]; simp [sizeCols, Size.y, Size.u]
  have cE : ∀ r e, e < 24 → (Trace.withCols tr t 31 (sizeCols yN)).cell t r (Size.ub e) =
      (((B0 - sizeU yN r) / 2 ^ e % 2 : Nat) : Fp) := by
    intro r e he
    rw [cell_withCols_ge (by simp [Size.ub]; omega)]
    have h1 : ¬ (33 + e = 31) := by omega
    have h2 : ¬ (33 + e = 32) := by omega
    have h3 : 33 + 0 ≤ 33 + e ∧ 33 + e < 33 + 24 := by omega
    simp only [sizeCols, Size.y, Size.u, Size.ub, h1, h2, h3, ite_false, ite_true,
      show 33 + e - 33 = e by omega, and_self]
  have cB : ∀ r x, x < 31 → (Trace.withCols tr t 31 (sizeCols yN)).cell t r x = tr.cell t r x :=
    fun r x hx => cell_withCols_lt hx
  have eB : ∀ r e, e < 24 → (Trace.withCols tr t 31 (sizeCols yN)).cell t r (Size.ub e) = 0 ∨
      (Trace.withCols tr t 31 (sizeCols yN)).cell t r (Size.ub e) = 1 := by
    intro r e he
    rw [cE r e he]
    rcases Nat.mod_two_eq_zero_or_one ((B0 - sizeU yN r) / 2 ^ e) with h | h <;> rw [h]
    · left; rfl
    · right; rfl
  have uS : ∀ r, sizeU yN (r + 1) = sizeU yN r + yN (r + 1) := by
    intro r; simp [sizeU, List.range_succ, List.map_append, List.sum_append]; omega
  refine tableLocal_withCols hL size_colBound ?_ ?_
  · intro r hr e he
    simp only [Size.constraints, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with ⟨e', he', rfl⟩ | rfl | rfl | rfl
    · simp only [eval_bool, eval_c]
      rcases eB r e' he' with h | h <;> rw [h] <;> grind
    · simp only [eval_mul, eval_sub, eval_c, eval_isFirst, cU, cY]
      split
      · subst_vars
        simp only [sizeU, List.range_one, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Nat.add_zero]
        grind
      · grind
    · simp only [eval_mul3, eval_sub, eval_add, eval_c, eval_n, eval_isTransition, height_withCols, cU, cY]
      by_cases hx : r + 1 = tr.height t
      · simp only [hx, ite_true]; grind
      · simp only [hx, ite_false]
        rw [Nat.mod_eq_of_lt (by omega), uS, natCast_add]
        grind
    · simp only [eval_mul, eval_sub, eval_k, eval_c, cU, cB _ la (by decide)]
      rcases Classical.em (tr.cell t r la = 1) with hla | hla
      · rw [hla]
        have hle := hB r hr hla
        have hb := eval_bits (Trace.withCols tr t 31 (sizeCols yN)) t r pub Size.ub 0 24
          (fun e he => by rw [Nat.zero_add]; exact eB r e he)
        rw [Size.ubitsE, hb]
        have hcv : ∀ e, e < 24 → cv (Trace.withCols tr t 31 (sizeCols yN)) t r (Size.ub (0 + e)) =
            (B0 - sizeU yN r) / 2 ^ e % 2 := by
          intro e he
          simp only [cv, Nat.zero_add, cE r e he, toNat_natCast]
          exact Nat.mod_eq_of_lt (by have := Nat.mod_lt ((B0 - sizeU yN r) / 2 ^ e) (by decide : 2 > 0); unfold P; omega)
        have hbv : bitsVal (fun b => cv (Trace.withCols tr t 31 (sizeCols yN)) t r (Size.ub b)) 0 24 =
            B0 - sizeU yN r := by
          rw [bitsVal_congr (v' := fun b => (B0 - sizeU yN r) / 2 ^ b % 2) 24 (fun b hb => by simpa only [Nat.zero_add] using hcv b hb)]
          rw [bitsVal_mod]; exact Nat.mod_eq_of_lt (by unfold B0 at *; omega)
        have e1 : (((B0 - sizeU yN r) + sizeU yN r : Nat) : Fp) = ((B0 : Nat) : Fp) := by
          rw [Nat.sub_add_cancel hle]
        rw [natCast_add] at e1
        rw [hbv]
        have : ((B0 : Nat) : Fp) = (B0 : Fp) := rfl
        grind
      · rcases ZkFormal.NearV3.SizeProof.isB hL hr (y := la) (by simp) with h | h
        · rw [h]; grind
        · exact absurd h hla
  · intro r hr i hi b hb
    simp only [Size.interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    simp only [Dsl.recv, List.mem_singleton] at hb; subst hb
    simp only [eval_c, cB _ act (by decide)]
    exact ZkFormal.NearV3.SizeProof.isB hL hr (y := act) (by simp)
end Size

end ZkFormal.NearV3.UnfoldA7
