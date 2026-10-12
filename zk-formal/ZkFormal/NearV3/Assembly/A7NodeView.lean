import ZkFormal.NearV3.Extract.Node.Proof
import ZkFormal.NearV3.Tables.UnfoldA7

/-!
# ZkFormal.NearV3.Assembly.A7NodeView — the A7 view of `nodeA7` (soundness)

`nodeA7` appends to `nodeV3` a boolean record flag `rpl` (received `RPL (nid)` with multiplicity
`nf · rpl`) and the running sum `ra` (`ra_0 = 0`, `ra' = ra + 2·act − nf·rpl·len`), sent as
`SIZE (3, ra)` on the `SUM` row.  On the node view's segments (`NodeProof3.viewOf`):

* **`nodeA7_view`**: one segmentation gives the base view (`NodeWf3`, `nodeTraffic3`) and the
  A7 traffic `a7NodeTraffic vs S`: the `RPL` receives `[n]` for the records `n` with `S n`
  (`S n` = the record's `rpl` flag) and the single send `SIZE (3, nodeA7Sum vs S)`,
  `nodeA7Sum vs S = Σ_n (2 − [S n]) · |ser n|`.
-/

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- The A7 node total `Σ_n (2 − [S n]) · |ser n|`. -/
def nodeA7Sum (vs : List NodeS3) (S : Nat → Bool) : Nat :=
  ((List.range vs.length).map fun n => (if S n then 1 else 2) * ((vs.getD n default).v.ser false).length).sum

/-- The traffic of `nodeA7`'s appended interactions. -/
def a7NodeTraffic (vs : List NodeS3) (S : Nat → Bool) : Traffic :=
  ⟨fun b => if b = B_SIZE then [[3, nodeA7Sum vs S]] else [],
   fun b => if b = UnfoldA7.B_RPL then ((List.range vs.length).filter S).map fun n => [n] else []⟩

end ZkFormal.NearV3

namespace ZkFormal.NearV3.A7NodeProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3
  ZkFormal.NearV3.NodeProof3 ZkFormal.NearV3.UnfoldA7

theorem flatMap_single {α : Type} (x : List α) : ∀ (H E : Nat), E < H →
    (List.range H).flatMap (fun r => if r = E then x else []) = x
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | H + 1, E, h => by
    rw [List.range_succ, List.flatMap_append]
    by_cases hE : E = H
    · subst hE
      rw [List.flatMap_eq_nil_iff.2 (fun r hr => by
        have := List.mem_range.1 hr; rw [if_neg (by omega)])]
      simp
    · rw [flatMap_single x H E (by omega)]; simp [Ne.symm hE]

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.flatMap_cons]
    rw [h a (by simp), flatMap_congr_mem (fun x hx => h x (by simp [hx]))]

theorem flatMap_filter_single (S : Nat → Bool) (l : List Nat) :
    l.flatMap (fun n => if S n = true then [[((n : Nat) : Fp)]] else []) =
      ((l.filter S).map fun n => ([n] : Msg)).map Msg.toFp := by
  induction l with
  | nil => rfl
  | cons x l ih => cases h : S x <;> simp_all [Msg.toFp, natCast_eq]

variable {tr : Trace Fp} {pub : List Fp}

theorem rowA7 (q bb : Nat) (sd : Bool) :
    rowTraffic UnfoldA7.Node.interactions tr T_NODE q pub bb sd =
      (if bb = B_RPL ∧ sd = false ∧ tr.cell T_NODE q nf * tr.cell T_NODE q UnfoldA7.Node.rpl = 1 then
        [[tr.cell T_NODE q nid]] else []) ++
      (if bb = B_SIZE ∧ sd = true ∧ tr.cell T_NODE q sumr = 1 then
        [[((3 : Nat) : Fp), tr.cell T_NODE q UnfoldA7.Node.ra]] else []) := by
  simp only [rowTraffic, UnfoldA7.Node.interactions, List.flatMap_cons, List.flatMap_nil, Dsl.recv, Dsl.send,
    Interaction.multNat, multNat_one, Interaction.msgVal, List.map_cons, List.map_nil, eval_c, eval_mul,
    eval_k, List.append_nil]
  by_cases h1 : bb = B_RPL <;> by_cases h1' : bb = B_SIZE <;> by_cases h2 : sd = false <;>
    by_cases h3 : tr.cell T_NODE q nf * tr.cell T_NODE q UnfoldA7.Node.rpl = 1 <;>
    by_cases h4 : tr.cell T_NODE q sumr = 1 <;>
    simp_all [B_RPL, B_SIZE, eq_comm] <;> rfl

variable (hL : TableLocal nodeA7 tr T_NODE pub)
include hL

theorem baseL : TableLocal NodeV3.table tr T_NODE pub :=
  ⟨hL.log_ge, hL.log_le, fun r hr e he => hL.constr r hr e (List.mem_append_left _ he),
    fun r hr i hi b hb => hL.bits r hr i (List.mem_append_left _ hi) b hb⟩

theorem conA7 {r : Nat} (hr : r < tr.height T_NODE) {e : Expr} (he : e ∈ UnfoldA7.Node.constraints) :
    e.eval tr T_NODE r pub = 0 := hL.constr r hr e (List.mem_append_right _ he)

theorem rplB {r : Nat} (hr : r < tr.height T_NODE) :
    tr.cell T_NODE r UnfoldA7.Node.rpl = 0 ∨ tr.cell T_NODE r UnfoldA7.Node.rpl = 1 := by
  have := conA7 hL hr (e := Dsl.bool (c UnfoldA7.Node.rpl)) (by simp [UnfoldA7.Node.constraints])
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem ra0 (h0 : 0 < tr.height T_NODE) : tr.cell T_NODE 0 UnfoldA7.Node.ra = 0 := by
  have := conA7 hL h0 (e := .mul .isFirst (c UnfoldA7.Node.ra)) (by simp [UnfoldA7.Node.constraints])
  simp only [eval_mul, eval_c, eval_isFirst, if_pos rfl] at this
  grind

theorem raS {r : Nat} (hr : r + 1 < tr.height T_NODE) :
    tr.cell T_NODE (r + 1) UnfoldA7.Node.ra = tr.cell T_NODE r UnfoldA7.Node.ra + (2 * tr.cell T_NODE r act -
      tr.cell T_NODE r nf * tr.cell T_NODE r UnfoldA7.Node.rpl * tr.cell T_NODE r len) := by
  have := conA7 hL (r := r) (by omega) (e := .mul .isTransition
      (sub (n UnfoldA7.Node.ra) (.add (c UnfoldA7.Node.ra) (sub (smul 2 (c act)) (mul3 (c nf) (c UnfoldA7.Node.rpl) (c len))))))
    (by simp [UnfoldA7.Node.constraints])
  simp only [eval_mul, eval_c, eval_n, eval_sub, eval_add, eval_smul, eval_mul3, eval_isTransition,
    Nat.mod_eq_of_lt hr, if_neg (show ¬ r + 1 = tr.height T_NODE by omega)] at this
  grind

variable {segs : List (Nat × Nat)}

/-- `len` at a record's first row is its row count. -/
theorem lenStart (hS : NodeSegs tr segs) {n : Nat} (h : n < segs.length) :
    tr.cell T_NODE segs[n].1 len = ((segs[n].2 : Nat) : Fp) := by
  have hB := baseL hL
  have hs := hS.seg' hB h
  have hb := hS.bound' hB h
  have hp := hs.1
  have hl := hs.2.2.1; rw [one_iff] at hl
  have hpos := hS.posAt hB h (segs[n].2 - 1) (by omega)
  have e := con hB (r := segs[n].1 + (segs[n].2 - 1)) (by omega)
    (e := .mul (c nl) (sub (.add (c pos) (k 1)) (c len))) (by simp [NodeV3.constraints, NodeV3.cRows])
  rw [show segs[n].1 + segs[n].2 - 1 = segs[n].1 + (segs[n].2 - 1) by omega] at hl
  simp only [eval_mul, eval_c, eval_sub, eval_add, eval_k, hl, hpos] at e
  rw [← hS.const hB h (x := len) (by simp [nodeConst]) (d := segs[n].2 - 1) (by omega)]
  have : ((segs[n].2 : Nat) : Fp) = ((segs[n].2 - 1 : Nat) : Fp) + ((1 : Nat) : Fp) := by
    rw [← natCast_add, show segs[n].2 - 1 + 1 = segs[n].2 by omega]
  rw [this]; grind

/-- `nf` vanishes off record starts. -/
theorem nfZero (hS : NodeSegs tr segs) {r : Nat} (hr : r < tr.height T_NODE)
    (hns : ∀ n (h : n < segs.length), segs[n].1 ≠ r) : tr.cell T_NODE r nf = 0 := by
  have hB := baseL hL
  by_cases hin : r < segEnd 0 segs
  · -- inside some segment, not at its start
    have hm : r ∈ List.range' 0 (segEnd 0 segs - 0) := List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩
    rw [range'_segs segs 0 hS.consec] at hm
    obtain ⟨p, hp, hrp⟩ := List.mem_flatMap.1 hm
    rw [List.mem_range'_1] at hrp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    have hne := hns i hi
    exact zero_of hB hr (by simp [boolCols]) ((hS.seg' hB hi).2.2.2.2.1 r (by omega) (by omega))
  · have ha := zero_of hB hr (by simp [boolCols]) (hS.pad r (by omega) hr)
    have e := con hB hr (e := .mul (c nf) (Dsl.not (c act))) (by simp [NodeV3.constraints, NodeV3.cRows])
    simp only [eval_mul, eval_c, eval_not, ha] at e
    grind

end ZkFormal.NearV3.A7NodeProof

namespace ZkFormal.NearV3.A7NodeProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3
  ZkFormal.NearV3.NodeProof3 ZkFormal.NearV3.UnfoldA7

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal nodeA7 tr T_NODE pub)
include hL
variable {segs : List (Nat × Nat)}

/-- The record flag of record `n`. -/
def rplOf (tr : Trace Fp) (segs : List (Nat × Nat)) (n : Nat) : Bool :=
  decide (tr.cell T_NODE (segs.getD n default).1 UnfoldA7.Node.rpl = 1)

/-- The A7 weight of record `n`. -/
def wOf (tr : Trace Fp) (segs : List (Nat × Nat)) (n : Nat) : Nat :=
  (if rplOf tr segs n then 1 else 2) * (segs.getD n default).2

/-- `ra` across one record. -/
theorem raSeg (hS : NodeSegs tr segs) {n : Nat} (h : n < segs.length) :
    tr.cell T_NODE (segs[n].1 + segs[n].2) UnfoldA7.Node.ra =
      tr.cell T_NODE segs[n].1 UnfoldA7.Node.ra + ((wOf tr segs n : Nat) : Fp) := by
  have hB := baseL hL
  have hs := hS.seg' hB h
  have hb := hS.bound' hB h
  have hE := (hS.sumRow hB).1
  have hend : segs[n].1 + segs[n].2 ≤ segEnd 0 segs := hS.bound hB (List.getElem_mem h)
  have hp := hs.1
  have hlen := lenStart hL hS h
  have hnf0 : tr.cell T_NODE segs[n].1 nf = 1 := by have := hs.2.1; rwa [one_iff] at this
  have hg : segs.getD n default = segs[n] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rcases rplB hL (r := segs[n].1) (by omega) with hr | hr
  · -- not replaced: `+2` per row
    have step : ∀ d, d ≤ segs[n].2 → tr.cell T_NODE (segs[n].1 + d) UnfoldA7.Node.ra =
        tr.cell T_NODE segs[n].1 UnfoldA7.Node.ra + ((2 * d : Nat) : Fp) := by
      intro d; induction d with
      | zero => intro _; simp only [Nat.add_zero, Nat.mul_zero]; grind
      | succ d ih =>
        intro hd
        have ha := segAct hB (hS.ctx hB (List.getElem_mem h)).choose_spec (d := d) (by omega)
        rw [show segs[n].1 + (d + 1) = segs[n].1 + d + 1 by omega, raS hL (by omega), ih (by omega), ha]
        rcases Nat.eq_zero_or_pos d with h0 | h0
        · subst h0; simp only [Nat.add_zero] at *; rw [hnf0, hr]
          rw [show 2 * (0 + 1) = 2 * 0 + 2 by rfl, natCast_add]; grind
        · have hz : tr.cell T_NODE (segs[n].1 + d) nf = 0 :=
            zero_of hB (by omega) (by simp [boolCols]) (hs.2.2.2.2.1 _ (by omega) (by omega))
          rw [hz, show 2 * (d + 1) = 2 * d + 2 by omega, natCast_add]; grind
    rw [step _ (Nat.le_refl _)]
    unfold wOf rplOf; rw [hg, hr]; simp
  · -- replaced: `+2` per row, `− ℓ` on the first
    have step : ∀ d, 0 < d → d ≤ segs[n].2 → tr.cell T_NODE (segs[n].1 + d) UnfoldA7.Node.ra + ((segs[n].2 : Nat) : Fp) =
        tr.cell T_NODE segs[n].1 UnfoldA7.Node.ra + ((2 * d : Nat) : Fp) := by
      intro d; induction d with
      | zero => intro h0; omega
      | succ d ih =>
        intro _ hd
        have ha := segAct hB (hS.ctx hB (List.getElem_mem h)).choose_spec (d := d) (by omega)
        rw [show segs[n].1 + (d + 1) = segs[n].1 + d + 1 by omega, raS hL (by omega), ha]
        rcases Nat.eq_zero_or_pos d with h0 | h0
        · subst h0; simp only [Nat.add_zero] at *; rw [hnf0, hr, hlen]
          rw [show 2 * (0 + 1) = 2 * 0 + 2 by rfl, natCast_add]; grind
        · have hz : tr.cell T_NODE (segs[n].1 + d) nf = 0 :=
            zero_of hB (by omega) (by simp [boolCols]) (hs.2.2.2.2.1 _ (by omega) (by omega))
          have := ih h0 (by omega)
          rw [hz, show 2 * (d + 1) = 2 * d + 2 by omega, natCast_add]; grind
    have := step segs[n].2 hp (Nat.le_refl _)
    unfold wOf rplOf; rw [hg, hr]; simp only [decide_true, if_true, Nat.one_mul]
    rw [show 2 * segs[n].2 = segs[n].2 + segs[n].2 by omega, natCast_add] at this
    grind

/-- `ra` at the `SUM` row. -/
theorem raEnd (hS : NodeSegs tr segs) :
    tr.cell T_NODE (segEnd 0 segs) UnfoldA7.Node.ra =
      ((((List.range segs.length).map (wOf tr segs)).sum : Nat) : Fp) := by
  have hB := baseL hL
  have hH := height_ge hB
  obtain ⟨h0, hs0⟩ := hS.first hB
  let st : Nat → Nat := fun k =>
    if k = 0 then 0 else ((segs.getD (k - 1) default).1 + (segs.getD (k - 1) default).2)
  have hst : ∀ k (hk : k < segs.length), st k = segs[k].1 := by
    intro k hk
    cases k with
    | zero => simp [st, hs0]
    | succ j =>
      have := hS.next hB (n := j) hk
      simp only [st, if_neg (show j + 1 ≠ 0 by omega), Nat.add_sub_cancel, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show j < segs.length by omega), Option.getD_some]
      exact this.symm
  have gen : ∀ k, k ≤ segs.length → tr.cell T_NODE (st k) UnfoldA7.Node.ra =
      ((((List.range k).map (wOf tr segs)).sum : Nat) : Fp) := by
    intro k; induction k with
    | zero => intro _; simp only [st, if_pos rfl]; rw [ra0 hL (by omega)]; rfl
    | succ k ih =>
      intro hk
      have e1 : st (k + 1) = segs[k].1 + segs[k].2 := by
        simp [st, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < segs.length by omega)]
      rw [e1, raSeg hL hS (by omega), ← hst k (by omega), ih (by omega), List.range_succ, List.map_append,
        List.sum_append, natCast_add]
      simp
  have := gen segs.length (Nat.le_refl _)
  rw [show st segs.length = segEnd 0 segs by
    rw [hS.endEq hB h0]; simp [st, show segs.length ≠ 0 by omega, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show segs.length - 1 < segs.length by omega)]] at this
  exact this

end ZkFormal.NearV3.A7NodeProof

namespace ZkFormal.NearV3.A7NodeProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3
  ZkFormal.NearV3.NodeProof3 ZkFormal.NearV3.UnfoldA7

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal nodeA7 tr T_NODE pub)
include hL
variable {segs : List (Nat × Nat)}

theorem inSeg (hS : NodeSegs tr segs) {r : Nat} (hr : r < segEnd 0 segs) :
    ∃ i, ∃ hi : i < segs.length, segs[i].1 ≤ r ∧ r < segs[i].1 + segs[i].2 := by
  have hm : r ∈ List.range' 0 (segEnd 0 segs - 0) := List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩
  rw [range'_segs segs 0 hS.consec] at hm
  obtain ⟨p, hp, hrp⟩ := List.mem_flatMap.1 hm
  rw [List.mem_range'_1] at hrp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  exact ⟨i, hi, hrp.1, hrp.2⟩

theorem rpl_rows (hS : NodeSegs tr segs) :
    (List.range (tr.height T_NODE)).flatMap (fun r => rowTraffic UnfoldA7.Node.interactions tr T_NODE r pub B_RPL false) =
      (List.range segs.length).flatMap fun n => if rplOf tr segs n = true then [[((n : Nat) : Fp)]] else [] := by
  have hB := baseL hL
  have hE := (hS.sumRow hB).1
  have row : ∀ r, rowTraffic UnfoldA7.Node.interactions tr T_NODE r pub B_RPL false =
      if tr.cell T_NODE r nf * tr.cell T_NODE r UnfoldA7.Node.rpl = 1 then [[tr.cell T_NODE r nid]] else [] := by
    intro r; rw [rowA7]; simp [show B_RPL ≠ B_SIZE by decide]
  rw [flatMap_rows_segs _ segs _ hS.consec hS.endLe (fun r h1 h2 => by
    rw [row, nfZero hL hS h2 (fun n hn e => by have := hS.bound hB (List.getElem_mem hn); have := (hS.seg' hB hn).1; omega),
      if_neg (by grind)])]
  rw [flatMap_eq_range segs]
  apply flatMap_congr_mem; intro n hn; rw [List.mem_range] at hn
  have hg : segs.getD n default = segs[n] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
  rw [hg]
  have hs := hS.seg' hB hn
  have hb := hS.bound' hB hn
  have hp := hs.1
  have e : List.range' segs[n].1 segs[n].2 = segs[n].1 :: List.range' (segs[n].1 + 1) (segs[n].2 - 1) := by
    rw [show segs[n].2 = (segs[n].2 - 1) + 1 by omega, List.range'_succ]; simp
  have hrest : (List.range' (segs[n].1 + 1) (segs[n].2 - 1)).flatMap
      (fun r => rowTraffic UnfoldA7.Node.interactions tr T_NODE r pub B_RPL false) = [] := by
    refine List.flatMap_eq_nil_iff.2 (fun r hr => ?_)
    rw [List.mem_range'_1] at hr
    rw [row, zero_of hB (by omega) (by simp [boolCols]) (hs.2.2.2.2.1 r (by omega) (by omega)), if_neg (by grind)]
  rw [e, List.flatMap_cons, hrest, List.append_nil]
  have hnf0 : tr.cell T_NODE segs[n].1 nf = 1 := by have := hs.2.1; rwa [one_iff] at this
  simp only [row, hnf0, hS.nid hB n hn, rplOf, hg]
  rcases rplB hL (r := segs[n].1) (by omega) with h | h
  · rw [h, if_neg (by grind)]; simp
  · rw [h, if_pos (by grind)]; simp [natCast_eq]

theorem size_rows (hS : NodeSegs tr segs) :
    (List.range (tr.height T_NODE)).flatMap (fun r => rowTraffic UnfoldA7.Node.interactions tr T_NODE r pub B_SIZE true) =
      [[((3 : Nat) : Fp), ((((List.range segs.length).map (wOf tr segs)).sum : Nat) : Fp)]] := by
  have hB := baseL hL
  obtain ⟨hE, h1, h2⟩ := hS.sumRow hB
  have row : ∀ r, r < tr.height T_NODE → rowTraffic UnfoldA7.Node.interactions tr T_NODE r pub B_SIZE true =
      if r = segEnd 0 segs then [[((3 : Nat) : Fp), tr.cell T_NODE (segEnd 0 segs) UnfoldA7.Node.ra]] else [] := by
    intro r hr
    rw [rowA7]
    simp only [show B_SIZE ≠ B_RPL by decide, false_and, if_false, List.nil_append, true_and]
    by_cases he : r = segEnd 0 segs
    · subst he; simp [h1]
    · rw [if_neg he]
      have hz : tr.cell T_NODE r sumr = 0 := by
        rcases Nat.lt_or_gt_of_ne he with hlt | hgt
        · obtain ⟨i, hi, hl1, hl2⟩ := inSeg hL hS hlt
          obtain ⟨fl, hC⟩ := hS.ctx hB (List.getElem_mem hi)
          have ha := segAct hB hC (d := r - segs[i].1) (by omega)
          rw [show segs[i].1 + (r - segs[i].1) = r by omega] at ha
          have e := con hB hr (e := .mul (c act) (c sumr)) (by simp [NodeV3.constraints, NodeV3.cRows])
          simp only [eval_mul, eval_c, ha] at e; grind
        · exact h2 r hgt hr
      simp [hz, fp_zero_ne_one]
  rw [flatMap_congr_mem (fun r hr => row r (List.mem_range.1 hr)), flatMap_single _ _ _ hE, raEnd hL hS]

/-- Record ser lengths of the node view are the segment lengths. -/
theorem viewOf_ser (hS : NodeSegs tr segs) {n : Nat} (hn : n < segs.length) :
    (((viewOf tr pub segs).getD n default).v.ser false).length = segs[n].2 := by
  have hB := baseL hL
  obtain ⟨fl, hC⟩ := hS.ctx hB (List.getElem_mem hn)
  have : (viewOf tr pub segs).getD n default = nodeSOf tr pub segs[n].1 segs[n].2 := by
    simp [viewOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
  rw [this]
  show ((nodeVOf tr segs[n].1).ser false).length = _
  rw [← (nodeSer hB hC).1, rowsB_length]

theorem nodeA7Sum_eq (hS : NodeSegs tr segs) :
    nodeA7Sum (viewOf tr pub segs) (rplOf tr segs) = ((List.range segs.length).map (wOf tr segs)).sum := by
  unfold nodeA7Sum
  rw [show (viewOf tr pub segs).length = segs.length by simp [viewOf]]
  congr 1
  apply List.map_congr_left; intro n hn; rw [List.mem_range] at hn
  rw [viewOf_ser hL hS hn]
  simp [wOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]

theorem a7TrafficOf (hS : NodeSegs tr segs) :
    TableTraffic UnfoldA7.Node.interactions tr T_NODE pub (a7NodeTraffic (viewOf tr pub segs) (rplOf tr segs)) := by
  intro bb m
  rw [tableBusCount_eq, tableBusCount_eq]
  have hlen : (viewOf tr pub segs).length = segs.length := by simp [viewOf]
  constructor
  · by_cases hb : bb = B_SIZE
    · subst hb
      rw [size_rows hL hS]
      simp only [a7NodeTraffic, if_true, List.map_cons, List.map_nil, Msg.toFp, nodeA7Sum_eq hL hS]
      rfl
    · rw [List.flatMap_eq_nil_iff.2 (fun r _ => by rw [rowA7]; simp [hb])]
      simp [a7NodeTraffic, hb]
  · by_cases hb : bb = B_RPL
    · subst hb
      rw [rpl_rows hL hS]
      simp only [a7NodeTraffic, if_true, hlen]
      rw [flatMap_filter_single]
    · rw [List.flatMap_eq_nil_iff.2 (fun r _ => by rw [rowA7]; simp [hb])]
      simp [a7NodeTraffic, hb]

end ZkFormal.NearV3.A7NodeProof

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- **The `nodeA7` view**: one segmentation gives the base view and the A7 traffic. -/
theorem nodeA7_view (tr : Trace Fp) (pub : List Fp) (hL : TableLocal UnfoldA7.nodeA7 tr T_NODE pub) :
    ∃ vs S, NodeWf3 vs ∧ TableTraffic NodeV3.interactions tr T_NODE pub (nodeTraffic3 vs) ∧
      TableTraffic UnfoldA7.Node.interactions tr T_NODE pub (a7NodeTraffic vs S) := by
  have hB := A7NodeProof.baseL hL
  obtain ⟨segs, hS⟩ := NodeProof3.nodeSegs_exist hB
  exact ⟨_, _, NodeProof3.nodeWfOf hB hS, NodeProof3.nodeTrafficOf hB hS, A7NodeProof.a7TrafficOf hL hS⟩

end ZkFormal.NearV3
