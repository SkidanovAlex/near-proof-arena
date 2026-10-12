import ZkFormal.NearV3.Extract.Ups.Proof
import ZkFormal.NearV3.Assembly.A7NodeView

/-!
# ZkFormal.NearV3.Assembly.A7UpsView — the A7 view of `upsA7` (soundness)

`upsA7` appends to `upsV3`: sends `RPL (sN)` with multiplicity `pf · up` (first row of every
upper part), `RPL (nD)` with `sf` (the segment's first row, `nD = Σ dd_i · N_i`), `RPLV (vid)`
with `sf · pres`, and `SIZE (5, s)` on the last row, `s` the running sum of `vb + qb`.

On the ups view's segments (`UpsRows.viewOf`), **`upsA7_view`** gives the base view (`UpsWf`,
`upsTraffic`) together with

* `a7UpsTraffic v`: the `RPL`/`RPLV` sends of the segment rows (`UpsSeg.a7Rpl`, `a7Rplv`, in
  terms of the rows' cells) and the single `SIZE (5, Σ_s a7S s)` send, `a7S s` the number of
  value/node-part rows of `s`; nothing received;
* `UpsA7Wf v`: on the first row of every segment, `nD = Σ dd_i · N_i` (field).
-/

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl

/-- `RPL` sends of a row: `[sN]` on an upper part's first row, `[nD]` on a segment's first row. -/
def a7RplRow (C : URow) : List Msg :=
  (if C UpsV3.pf = 1 ∧ C UpsV3.up = 1 then [[C UpsV3.sN]] else []) ++
  (if C UpsV3.sf = 1 then [[C UnfoldA7.Ups.nD]] else [])

/-- `RPLV` sends of a row: `[vid]` on a segment's first row when the old value is present. -/
def a7RplvRow (C : URow) : List Msg :=
  if C UpsV3.sf = 1 ∧ C UpsV3.pres = 1 then [[C UpsV3.vid]] else []

def UpsSeg.a7Rpl (s : UpsSeg) : List Msg := (List.range s.rows.length).flatMap fun i => a7RplRow (s.row i)
def UpsSeg.a7Rplv (s : UpsSeg) : List Msg := (List.range s.rows.length).flatMap fun i => a7RplvRow (s.row i)
/-- The value/node-part rows of a segment. -/
def UpsSeg.a7S (s : UpsSeg) : Nat := ((List.range s.rows.length).map fun i => s.row i UpsV3.vb + s.row i UpsV3.qb).sum

/-- The traffic of `upsA7`'s appended interactions. -/
def a7UpsTraffic (v : List UpsSeg) : Traffic :=
  ⟨fun b => if b = UnfoldA7.B_RPL then v.flatMap UpsSeg.a7Rpl
      else if b = UnfoldA7.B_RPLV then v.flatMap UpsSeg.a7Rplv
      else if b = B_SIZE then [[5, (v.map UpsSeg.a7S).sum]] else [],
   fun _ => []⟩

/-- The appended constraint on the segments' first rows. -/
def UpsA7Wf (v : List UpsSeg) : Prop :=
  ∀ s ∈ v, ((s.row 0 UnfoldA7.Ups.nD : Nat) : Fp) =
    uev (s.row 0) (s.next 0) (sum [.mul (c UpsV3.dd0) (c UpsV3.N0), .mul (c UpsV3.dd1) (c UpsV3.N1),
      .mul (c UpsV3.dd2) (c UpsV3.N2)])

end ZkFormal.NearV3

namespace ZkFormal.NearV3.A7UpsProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
  ZkFormal.NearV3.UpsRows ZkFormal.NearV3.UnfoldA7
open ZkFormal.NearV3.A7NodeProof (flatMap_single flatMap_congr_mem)

variable {tr : Trace Fp} {pub : List Fp} {t : Nat}

theorem sumZ {α : Type} : ∀ (l : List α) (f : α → Nat), (∀ x ∈ l, f x = 0) → (l.map f).sum = 0
  | [], _, _ => rfl
  | a :: l, f, h => by
    simp only [List.map_cons, List.sum_cons, h a (by simp), sumZ l f (fun x hx => h x (by simp [hx]))]

theorem sumFM {α : Type} (f : Nat → Nat) (g : α → List Nat) : ∀ (l : List α),
    ((l.flatMap g).map f).sum = (l.map fun p => ((g p).map f).sum).sum
  | [] => rfl
  | p :: r => by simp [List.flatMap_cons, List.map_append, List.sum_append, sumFM f g r]

theorem multG (e : Expr) (r : Nat) :
    Interaction.multNat.go tr t r pub [e] 0 = if e.eval tr t r pub = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go]
  by_cases h : e.eval tr t r pub = 1 <;> simp [h]

theorem rowRpl (q : Nat) :
    rowTraffic UnfoldA7.Ups.interactions tr t q pub B_RPL true =
      (if tr.cell t q pf * tr.cell t q up = 1 then [[tr.cell t q sN]] else []) ++
      (if tr.cell t q sf = 1 then [[tr.cell t q UnfoldA7.Ups.nD]] else []) := by
  simp only [rowTraffic, UnfoldA7.Ups.interactions, List.flatMap_cons, List.flatMap_nil, Dsl.send,
    Interaction.multNat, multG, Interaction.msgVal, List.map_cons, List.map_nil, eval_c, eval_mul,
    eval_k, eval_isLast, List.append_nil]
  by_cases h3 : tr.cell t q pf * tr.cell t q up = 1 <;> by_cases h4 : tr.cell t q sf = 1 <;>
    simp [h3, h4, B_RPL, B_RPLV, B_SIZE]

theorem rowRplv (q : Nat) :
    rowTraffic UnfoldA7.Ups.interactions tr t q pub B_RPLV true =
      (if tr.cell t q sf * tr.cell t q pres = 1 then [[tr.cell t q vid]] else []) := by
  simp only [rowTraffic, UnfoldA7.Ups.interactions, List.flatMap_cons, List.flatMap_nil, Dsl.send,
    Interaction.multNat, multG, Interaction.msgVal, List.map_cons, List.map_nil, eval_c, eval_mul,
    eval_k, eval_isLast, List.append_nil]
  by_cases h5 : tr.cell t q sf * tr.cell t q pres = 1 <;> simp [h5, B_RPL, B_RPLV, B_SIZE]

theorem rowSize (q : Nat) :
    rowTraffic UnfoldA7.Ups.interactions tr t q pub B_SIZE true =
      (if q + 1 = tr.height t then [[((5 : Nat) : Fp), tr.cell t q UnfoldA7.Ups.s]] else []) := by
  simp only [rowTraffic, UnfoldA7.Ups.interactions, List.flatMap_cons, List.flatMap_nil, Dsl.send,
    Interaction.multNat, multG, Interaction.msgVal, List.map_cons, List.map_nil, eval_c, eval_mul,
    eval_k, eval_isLast, List.append_nil]
  by_cases h6 : q + 1 = tr.height t <;> simp [h6, B_RPL, B_RPLV, B_SIZE, fp_zero_ne_one]

theorem rowOther (q bb : Nat) (sd : Bool) (h : ¬ (sd = true ∧ (bb = B_RPL ∨ bb = B_RPLV ∨ bb = B_SIZE))) :
    rowTraffic UnfoldA7.Ups.interactions tr t q pub bb sd = [] := by
  simp only [rowTraffic, UnfoldA7.Ups.interactions, List.flatMap_cons, List.flatMap_nil, Dsl.send]
  simp only [not_and, not_or] at h
  cases sd <;> simp_all [eq_comm]

/-! ## Row facts (natural cells) -/

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC

theorem upB (hp : C pf = 1) : C up = 0 ∨ C up = 1 := by
  have h := fact ok (e := .mul (c pf) (Dsl.bool (c up))) (by simp [UpsV3.constraints, cBool, partBools])
  uev_simp
  try simp only [cast_ofNat] at *
  rw [hp] at h
  exact nat01 (hC up) (by simp only [cast_ofNat, cast1] at h ⊢; grind)

theorem presB (hs : C sf = 1) : C pres = 0 ∨ C pres = 1 := by
  have h := fact ok (e := .mul (c sf) (Dsl.bool (c pres))) (by simp [UpsV3.constraints, cBool, segBools])
  uev_simp
  try simp only [cast_ofNat] at *
  rw [hs] at h
  exact nat01 (hC pres) (by simp only [cast_ofNat, cast1] at h ⊢; grind)

include hD in
theorem inactive (ha : C act = 0) : C sf = 0 ∧ C pf = 0 ∧ C vb = 0 ∧ C qb = 0 := by
  obtain ⟨-, hact, hwk, -, -, -, -, -, -, -⟩ := kinds ok hC hD
  have h := fact ok (e := .mul (c pf) (not (.add (c vb) (c qb)))) (by cmem)
  uev_simp
  try simp only [cast_ofNat] at *
  have zv : C vb = 0 := by omega
  have zq : C qb = 0 := by omega
  rw [zv, zq] at h
  have bpf := rowBool ok hC (x := pf) (by simp [rowBools])
  refine ⟨by omega, ?_, zv, zq⟩
  rcases bpf with h0 | h1
  · exact h0
  · rw [h1] at h; exfalso; rw [cast0, cast1] at h; exact fp_zero_ne_one (by grind)

end

theorem prod01 {a b : Nat} (ha : a = 0 ∨ a = 1) (hb : a = 1 → b = 0 ∨ b = 1) :
    ((a : Nat) : Fp) * ((b : Nat) : Fp) = 1 ↔ a = 1 ∧ b = 1 := by
  rcases ha with rfl | rfl
  · constructor
    · intro h; exfalso; rw [cast0] at h; exact fp_zero_ne_one (by grind)
    · intro h; omega
  · rcases hb rfl with rfl | rfl
    · constructor
      · intro h; exfalso; rw [cast0, cast1] at h; exact fp_zero_ne_one (by grind)
      · intro h; omega
    · simp only [and_self, iff_true]; rw [cast1]; grind

section
variable (hB : TableLocal UpsV3.table tr t pub)
include hB

theorem rplRow {r : Nat} (hr : r < tr.height t) :
    rowTraffic UnfoldA7.Ups.interactions tr t r pub B_RPL true = (a7RplRow (rowC tr t r)).map Msg.toFp := by
  have ok := rowOk tr t pub hB hr
  have hC := rowC_lt tr t r
  rw [rowRpl]
  simp only [cell_eq_cast tr t r]
  have e1 : (((cv tr t r pf : Nat) : Fp) * ((cv tr t r up : Nat) : Fp) = 1) ↔
      (rowC tr t r pf = 1 ∧ rowC tr t r up = 1) :=
    prod01 (rowBool ok hC (x := pf) (by simp [rowBools])) (upB ok hC)
  have e2 : (((cv tr t r sf : Nat) : Fp) = 1) ↔ rowC tr t r sf = 1 := by
    rw [← cast1]; exact ⟨fun h => natv (hC sf) (by have := P_gt; omega) h, fun h => by rw [show cv tr t r sf = 1 from h]⟩
  unfold a7RplRow
  simp only [e1, e2]
  simp only [rowC]
  by_cases h1 : cv tr t r pf = 1 ∧ cv tr t r up = 1 <;> by_cases h2 : cv tr t r sf = 1 <;>
    simp [h1, h2, Msg.toFp, natCast_eq]

theorem rplvRow {r : Nat} (hr : r < tr.height t) :
    rowTraffic UnfoldA7.Ups.interactions tr t r pub B_RPLV true = (a7RplvRow (rowC tr t r)).map Msg.toFp := by
  have ok := rowOk tr t pub hB hr
  have hC := rowC_lt tr t r
  rw [rowRplv]
  simp only [cell_eq_cast tr t r]
  have e1 : (((cv tr t r sf : Nat) : Fp) * ((cv tr t r pres : Nat) : Fp) = 1) ↔
      (rowC tr t r sf = 1 ∧ rowC tr t r pres = 1) :=
    prod01 (rowBool ok hC (x := sf) (by simp [rowBools])) (presB ok hC)
  unfold a7RplvRow
  simp only [e1]
  simp only [rowC]
  by_cases h1 : cv tr t r sf = 1 ∧ cv tr t r pres = 1 <;> simp [h1, Msg.toFp, natCast_eq]

end

section
variable (hL : TableLocal upsA7 tr t pub)
include hL

theorem baseL : TableLocal UpsV3.table tr t pub :=
  ⟨hL.log_ge, hL.log_le, fun r hr e he => hL.constr r hr e (List.mem_append_left _ he),
    fun r hr i hi b hb => hL.bits r hr i (List.mem_append_left _ hi) b hb⟩

theorem conA7 {r : Nat} (hr : r < tr.height t) {e : Expr} (he : e ∈ UnfoldA7.Ups.constraints) :
    e.eval tr t r pub = 0 := hL.constr r hr e (List.mem_append_right _ he)

/-- The running sum `s`. -/
theorem sRun : ∀ r, r < tr.height t → tr.cell t r UnfoldA7.Ups.s =
    ((((List.range r).map fun q => cv tr t q vb + cv tr t q qb).sum : Nat) : Fp) := by
  intro r; induction r with
  | zero =>
    intro h0
    have := conA7 hL h0 (e := .mul .isFirst (c UnfoldA7.Ups.s)) (by simp [UnfoldA7.Ups.constraints])
    simp only [eval_mul, eval_c, eval_isFirst] at this
    simp only [List.range_zero, List.map_nil, List.sum_nil, cast0]; grind
  | succ r ih =>
    intro hr
    have := conA7 hL (r := r) (by omega) (e := .mul .isTransition (sub (n UnfoldA7.Ups.s)
      (.add (c UnfoldA7.Ups.s) (.add (c vb) (c qb))))) (by simp [UnfoldA7.Ups.constraints])
    simp only [eval_mul, eval_c, eval_n, eval_sub, eval_add, eval_isTransition, Nat.mod_eq_of_lt hr,
      if_neg (show ¬ r + 1 = tr.height t by omega)] at this
    rw [List.range_succ, List.map_append, List.sum_append, natCast_add, ← ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, natCast_add,
      ← cell_eq_cast]
    grind

variable {segs : List (Nat × Nat)} (hc : Consec 0 segs) (he : segEnd 0 segs ≤ tr.height t)
  (hs : ∀ p ∈ segs, IsSeg (actB tr t) (firstB tr t) (lastB tr t) p.1 p.2)
  (hpad : ∀ r, segEnd 0 segs ≤ r → r < tr.height t → actB tr t r = false)
include hc he hs hpad

theorem padQuiet {r : Nat} (h1 : segEnd 0 segs ≤ r) (h2 : r < tr.height t) :
    rowC tr t r sf = 0 ∧ rowC tr t r pf = 0 ∧ rowC tr t r vb = 0 ∧ rowC tr t r qb = 0 := by
  have hB := baseL hL
  have ha := hpad r h1 h2
  simp only [actB, decide_eq_false_iff_not] at ha
  have b0 := (kinds (rowOk tr t pub hB (r := r) h2) (rowC_lt tr t r) (rowC_lt tr t _)).1
  exact inactive (rowOk tr t pub hB h2) (rowC_lt tr t r) (rowC_lt tr t _) (by omega)

theorem endLt : segEnd 0 segs < tr.height t := by
  have hB := baseL hL
  have hH : 0 < tr.height t := by unfold Trace.height; exact Nat.two_pow_pos _
  rcases Nat.lt_or_ge (segEnd 0 segs) (tr.height t) with h | h
  · exact h
  · exfalso
    have hm : tr.height t - 1 ∈ List.range' 0 (segEnd 0 segs - 0) := List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩
    rw [range'_segs segs 0 hc] at hm
    obtain ⟨p, hp, hrp⟩ := List.mem_flatMap.1 hm
    rw [List.mem_range'_1] at hrp
    have := (hs p hp).2.2.2.1 (tr.height t - 1) hrp.1 hrp.2
    simp only [actB, decide_eq_true_eq] at this
    exact stopLast hB hH this

theorem a7S_sum : (((viewOf tr t segs).map UpsSeg.a7S).sum) =
    ((List.range (tr.height t - 1)).map fun q => cv tr t q vb + cv tr t q qb).sum := by
  have hE := endLt hL hc he hs hpad
  rw [show tr.height t - 1 = segEnd 0 segs + (tr.height t - 1 - segEnd 0 segs) by omega, List.range_add,
    List.map_append, List.sum_append]
  have hz : ((List.map (fun x => segEnd 0 segs + x) (List.range (tr.height t - 1 - segEnd 0 segs))).map
      fun q => cv tr t q vb + cv tr t q qb).sum = 0 := by
    rw [List.map_map]
    refine sumZ _ _ (fun q hq => ?_)
    have := List.mem_range.1 hq
    obtain ⟨-, -, h3, h4⟩ := padQuiet hL hc he hs hpad (r := segEnd 0 segs + q) (by omega) (by omega)
    simp only [Function.comp_apply, rowC] at h3 h4 ⊢; omega
  rw [hz, Nat.add_zero, List.range_eq_range', ← Nat.sub_zero (segEnd 0 segs), range'_segs segs 0 hc]
  rw [sumFM]
  simp only [viewOf, List.map_map]
  congr 1
  apply List.map_congr_left; intro p hp
  have hb : p.1 + p.2 ≤ tr.height t := by have := seg_le_end segs 0 hc p hp; omega
  simp only [Function.comp_apply, UpsSeg.a7S, segOf_len, List.range'_eq_map_range, List.map_map]
  congr 1
  apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi
  simp only [Function.comp_apply, segOf_row tr t p hi, rowC]

theorem segRows (bb : Nat) (F : URow → List Msg)
    (hrow : ∀ r, r < tr.height t → rowTraffic UnfoldA7.Ups.interactions tr t r pub bb true = (F (rowC tr t r)).map Msg.toFp)
    (hq : ∀ r, segEnd 0 segs ≤ r → r < tr.height t → F (rowC tr t r) = []) :
    (List.range (tr.height t)).flatMap (fun r => rowTraffic UnfoldA7.Ups.interactions tr t r pub bb true) =
      ((viewOf tr t segs).flatMap fun s => (List.range s.rows.length).flatMap fun i => F (s.row i)).map Msg.toFp := by
  rw [flatMap_congr' (fun r hr => hrow r (List.mem_range.1 hr)), ← List.map_flatMap]
  congr 1
  rw [flatMap_rows_segs (tr.height t) segs _ hc he hq]
  simp only [viewOf, List.flatMap_map]
  apply flatMap_congr'; intro p hp
  have hb : p.1 + p.2 ≤ tr.height t := by have := seg_le_end segs 0 hc p hp; omega
  rw [segOf_len, List.range'_eq_map_range, List.flatMap_map]
  apply flatMap_congr'; intro i hi; rw [List.mem_range] at hi
  rw [segOf_row tr t p hi]

theorem a7TrafficOfU : TableTraffic UnfoldA7.Ups.interactions tr t pub (a7UpsTraffic (viewOf tr t segs)) := by
  have hB := baseL hL
  have hE := endLt hL hc he hs hpad
  intro bb m
  rw [tableBusCount_eq, tableBusCount_eq]
  constructor
  · by_cases h1 : bb = B_RPL
    · subst h1
      rw [segRows hL hc he hs hpad B_RPL a7RplRow (fun r hr => rplRow hB hr) (fun r h1 h2 => by
        obtain ⟨z1, z2, -, -⟩ := padQuiet hL hc he hs hpad h1 h2
        simp [a7RplRow, z1, z2])]
      simp only [a7UpsTraffic, ite_true]; rfl
    · by_cases h2 : bb = B_RPLV
      · subst h2
        rw [segRows hL hc he hs hpad B_RPLV a7RplvRow (fun r hr => rplvRow hB hr) (fun r h1 h2 => by
          obtain ⟨z1, -, -, -⟩ := padQuiet hL hc he hs hpad h1 h2
          simp [a7RplvRow, z1])]
        simp only [a7UpsTraffic, ite_true, show B_RPLV ≠ B_RPL by decide, ite_false]; rfl
      · by_cases h3 : bb = B_SIZE
        · subst h3
          have hH : 0 < tr.height t := by omega
          rw [flatMap_congr' (fun r hr => rowSize (tr := tr) (t := t) (pub := pub) r)]
          have : (List.range (tr.height t)).flatMap (fun r => if r + 1 = tr.height t then
              [[((5 : Nat) : Fp), tr.cell t r UnfoldA7.Ups.s]] else []) =
              (List.range (tr.height t)).flatMap (fun r => if r = tr.height t - 1 then
              [[((5 : Nat) : Fp), tr.cell t (tr.height t - 1) UnfoldA7.Ups.s]] else []) := by
            apply flatMap_congr'; intro r hr; rw [List.mem_range] at hr
            by_cases h : r = tr.height t - 1
            · subst h; rw [if_pos (by omega), if_pos rfl]
            · rw [if_neg (by omega), if_neg h]
          rw [this, flatMap_single _ _ _ (by omega), sRun hL _ (by omega), ← a7S_sum hL hc he hs hpad]
          simp only [a7UpsTraffic, show B_SIZE ≠ B_RPL by decide, show B_SIZE ≠ B_RPLV by decide, ite_false,
            ite_true, List.map_cons, List.map_nil, Msg.toFp]
          rfl
        · rw [List.flatMap_eq_nil_iff.2 (fun r _ => rowOther r bb true (by simp [h1, h2, h3]))]
          simp [a7UpsTraffic, h1, h2, h3]
  · rw [List.flatMap_eq_nil_iff.2 (fun r _ => rowOther r bb false (by simp))]
    simp [a7UpsTraffic]

theorem a7WfOfU : UpsA7Wf (viewOf tr t segs) := by
  have hB := baseL hL
  intro S hS
  simp only [viewOf, List.mem_map] at hS
  obtain ⟨p, hp, rfl⟩ := hS
  have hb : p.1 + p.2 ≤ tr.height t := by have := seg_le_end segs 0 hc p hp; omega
  obtain ⟨h0, hf, -⟩ := hs p hp
  simp only [firstB, decide_eq_true_eq] at hf
  rw [segOf_row tr t p h0, segOf_next tr t p hb h0, Nat.add_zero]
  have e := conA7 hL (r := p.1) (by omega)
    (e := .mul (c sf) (sub (c UnfoldA7.Ups.nD) (sum [.mul (c dd0) (c N0), .mul (c dd1) (c N1), .mul (c dd2) (c N2)])))
    (by simp [UnfoldA7.Ups.constraints])
  rw [eval_pure tr t p.1 pub _ rfl] at e
  simp only [uev, Expr.evalWith, uEnv, Dsl.sub, Dsl.c, if_false, Bool.false_eq_true] at e ⊢
  rw [show rowC tr t p.1 sf = 1 from hf] at e
  simp only [cast_ofNat] at e ⊢
  rw [cast1] at e
  grind

end

end ZkFormal.NearV3.A7UpsProof

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- **The `upsA7` view**: one segmentation gives the base view, the A7 traffic and the `nD`
constraint. -/
theorem upsA7_view (tr : Trace Fp) (pub : List Fp) (t : Nat) (hL : TableLocal UnfoldA7.upsA7 tr t pub) :
    ∃ v, UpsWf v ∧ TableTraffic UpsV3.interactions tr t pub (upsTraffic v) ∧
      TableTraffic UnfoldA7.Ups.interactions tr t pub (a7UpsTraffic v) ∧ UpsA7Wf v := by
  have hB := A7UpsProof.baseL hL
  obtain ⟨segs, hc, he, hs, hpad⟩ := segments_of (UpsRows.segFacts hB)
    (by unfold Trace.height; exact Nat.two_pow_pos _)
  exact ⟨UpsRows.viewOf tr t segs, UpsRows.viewWf hB hc he hs, UpsRows.viewTraffic hB hc he hs hpad,
    A7UpsProof.a7TrafficOfU hL hc he hs hpad, A7UpsProof.a7WfOfU hL hc he hs hpad⟩

end ZkFormal.NearV3

