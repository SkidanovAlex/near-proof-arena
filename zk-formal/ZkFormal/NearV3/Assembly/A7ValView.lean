import ZkFormal.NearV3.Extract.ValProof
import ZkFormal.NearV3.Assembly.A7NodeView

/-!
# ZkFormal.NearV3.Assembly.A7ValView — the A7 view of `valA7` (soundness)

`valA7` appends to `valV3` a boolean record flag `rplv` (received `RPLV (vid)` with multiplicity
`vf · rplv`) and the running sum `rb` (`rb_0 = 0`, `rb' = rb + 2·gb − vf·rplv·len`), sent as
`SIZE (4, rb)` on the `SUM` row.  On the value view's segments (`ValProof.val_segs_exist`):

* **`valA7_view`**: one segmentation gives the base view (`ValWf`, `valTraffic`) and the A7
  traffic `a7ValTraffic es S`: the `RPLV` receives `[e.vid]` for the records with `S`, and the
  single send `SIZE (4, valA7Sum es S)`, `valA7Sum es S = Σ_t (2 − [S t]) · len_t`.
-/

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- The A7 value total `Σ_t (2 − [S t]) · len_t`. -/
def valA7Sum (es : List ValE) (S : Nat → Bool) : Nat :=
  ((List.range es.length).map fun t => (if S t then 1 else 2) * (es.getD t default).len).sum

/-- The traffic of `valA7`'s appended interactions. -/
def a7ValTraffic (es : List ValE) (S : Nat → Bool) : Traffic :=
  ⟨fun b => if b = B_SIZE then [[4, valA7Sum es S]] else [],
   fun b => if b = UnfoldA7.B_RPLV then ((List.range es.length).filter S).map fun t => [(es.getD t default).vid]
     else []⟩

end ZkFormal.NearV3

namespace ZkFormal.NearV3.A7ValProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.ValV3
  ZkFormal.NearV3.ValProof ZkFormal.NearV3.UnfoldA7
open ZkFormal.NearV3.A7NodeProof (flatMap_single flatMap_congr_mem)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem multG (e : Expr) (r : Nat) :
    Interaction.multNat.go tr tt r pub [e] 0 = if e.eval tr tt r pub = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go]
  by_cases h : e.eval tr tt r pub = 1 <;> simp [h]

theorem rowA7 (q bb : Nat) (sd : Bool) :
    rowTraffic UnfoldA7.Val.interactions tr tt q pub bb sd =
      (if bb = B_RPLV ∧ sd = false ∧ tr.cell tt q vf * tr.cell tt q UnfoldA7.Val.rplv = 1 then
        [[tr.cell tt q vid]] else []) ++
      (if bb = B_SIZE ∧ sd = true ∧ tr.cell tt q sumr = 1 then
        [[((4 : Nat) : Fp), tr.cell tt q UnfoldA7.Val.rb]] else []) := by
  simp only [rowTraffic, UnfoldA7.Val.interactions, List.flatMap_cons, List.flatMap_nil, Dsl.recv, Dsl.send,
    Interaction.multNat, multG, Interaction.msgVal, List.map_cons, List.map_nil, eval_c, eval_mul,
    eval_k, List.append_nil]
  by_cases h1 : bb = B_RPLV <;> by_cases h1' : bb = B_SIZE <;> by_cases h2 : sd = false <;>
    by_cases h3 : tr.cell tt q vf * tr.cell tt q UnfoldA7.Val.rplv = 1 <;>
    by_cases h4 : tr.cell tt q sumr = 1 <;>
    simp_all [B_RPLV, B_SIZE, eq_comm] <;> rfl

variable (hL : TableLocal valA7 tr tt pub)
include hL

theorem baseL : TableLocal ValV3.table tr tt pub :=
  ⟨hL.log_ge, hL.log_le, fun r hr e he => hL.constr r hr e (List.mem_append_left _ he),
    fun r hr i hi b hb => hL.bits r hr i (List.mem_append_left _ hi) b hb⟩

theorem conA7 {r : Nat} (hr : r < tr.height tt) {e : Expr} (he : e ∈ UnfoldA7.Val.constraints) :
    e.eval tr tt r pub = 0 := hL.constr r hr e (List.mem_append_right _ he)

theorem rplvB {r : Nat} (hr : r < tr.height tt) :
    tr.cell tt r UnfoldA7.Val.rplv = 0 ∨ tr.cell tt r UnfoldA7.Val.rplv = 1 := by
  have := conA7 hL hr (e := Dsl.bool (c UnfoldA7.Val.rplv)) (by simp [UnfoldA7.Val.constraints])
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem rb0 (h0 : 0 < tr.height tt) : tr.cell tt 0 UnfoldA7.Val.rb = 0 := by
  have := conA7 hL h0 (e := .mul .isFirst (c UnfoldA7.Val.rb)) (by simp [UnfoldA7.Val.constraints])
  simp only [eval_mul, eval_c, eval_isFirst] at this
  grind

theorem rbS {r : Nat} (hr : r + 1 < tr.height tt) :
    tr.cell tt (r + 1) UnfoldA7.Val.rb = tr.cell tt r UnfoldA7.Val.rb + (2 * tr.cell tt r gb -
      tr.cell tt r vf * tr.cell tt r UnfoldA7.Val.rplv * tr.cell tt r len) := by
  have := conA7 hL (r := r) (by omega) (e := .mul .isTransition
      (sub (n UnfoldA7.Val.rb) (.add (c UnfoldA7.Val.rb) (sub (smul 2 (c gb))
        (mul3 (c vf) (c UnfoldA7.Val.rplv) (c len))))))
    (by simp [UnfoldA7.Val.constraints])
  simp only [eval_mul, eval_c, eval_n, eval_sub, eval_add, eval_smul, eval_mul3, eval_isTransition,
    Nat.mod_eq_of_lt hr, if_neg (show ¬ r + 1 = tr.height tt by omega)] at this
  grind

variable {segs : List (Nat × Nat)} (hc : Consec 0 segs) (hend : segEnd 0 segs ≤ tr.height tt)
  (hall : ∀ p ∈ segs, IsSeg (isOne tr tt ValV3.act) (isOne tr tt ValV3.vf) (isOne tr tt ValV3.vl) p.1 p.2)
  (hpad : ∀ r, segEnd 0 segs ≤ r → r < tr.height tt → isOne tr tt ValV3.act r = false)
include hc hend hall hpad

/-- The `SUM` row is the row after the last record, the only row with `sumr`. -/
theorem sumRowV :
    segEnd 0 segs < tr.height tt ∧ tr.cell tt (segEnd 0 segs) sumr = 1 ∧
      ∀ r, r < tr.height tt → r ≠ segEnd 0 segs → tr.cell tt r sumr = 0 := by
  have hB := baseL hL
  have hpos : 0 < tr.height tt := by unfold Trace.height; exact Nat.two_pow_pos _
  have hH : ∀ p ∈ segs, p.1 + p.2 ≤ tr.height tt := fun p hp => by
    have := seg_le_end segs 0 hc p hp; omega
  have hinact : ∀ r, segEnd 0 segs ≤ r → r < tr.height tt → tr.cell tt r ValV3.act = 0 := fun r h1 h2 =>
    zero_of_not_one hB h2 (by simp [bools]) (hpad r h1 h2)
  obtain ⟨A, hA⟩ : ∃ A, A = segEnd 0 segs := ⟨_, rfl⟩
  have hlastSeg : segs ≠ [] → ∃ q ∈ segs, q.1 + q.2 = A := by
    intro hne
    obtain ⟨p, rest, rfl⟩ : ∃ p rest, segs = p :: rest := by
      cases segs with
      | nil => exact absurd rfl hne
      | cons p rest => exact ⟨p, rest, rfl⟩
    exact ⟨(p :: rest)[(p :: rest).length - 1]'(by simp), List.getElem_mem _,
      by rw [hA, segEnd_last (p :: rest) 0 hc (by simp)]⟩
  have hAlt : A < tr.height tt := by
    rcases Nat.lt_or_ge A (tr.height tt) with h | h
    · exact h
    · exfalso
      have hlast := lastRow hB hpos
      by_cases hne : segs = []
      · subst hne; simp [segEnd] at hA; omega
      · obtain ⟨q, hq, hqe⟩ := hlastSeg hne
        have hqa := (hall q hq).2.2.2.1 (q.1 + q.2 - 1) (by have := (hall q hq).1; omega)
          (by have := (hall q hq).1; omega)
        simp only [isOne, decide_eq_true_eq] at hqa
        have : q.1 + q.2 - 1 = tr.height tt - 1 := by have := hH q hq; have := (hall q hq).1; omega
        rw [this, hlast] at hqa; exact absurd hqa (by decide)
  have hsumA : tr.cell tt A ValV3.sumr = 1 := by
    have ha := hinact A (by omega) hAlt
    by_cases hne : segs = []
    · subst hne
      have h0 : A = 0 := by simp [segEnd] at hA; exact hA
      subst h0
      have := (row0 hB hpos).1
      rw [ha] at this; grind
    · obtain ⟨q, hq, hqe⟩ := hlastSeg hne
      have hvl : tr.cell tt (q.1 + q.2 - 1) ValV3.vl = 1 := by
        have := (hall q hq).2.2.1; simpa [isOne] using this
      have e : q.1 + q.2 - 1 + 1 = A := by have := (hall q hq).1; omega
      have := (afterSeg hB (r := q.1 + q.2 - 1) (by omega) hvl).1
      rw [e, ha] at this; grind
  have hsumAfter : ∀ r, A < r → r < tr.height tt → tr.cell tt r ValV3.sumr = 0 := by
    intro r h1 h2
    induction r with
    | zero => omega
    | succ r ih =>
      by_cases hr : r = A
      · subst hr; exact (padFacts hB h2 (hinact _ (by omega) (by omega))).2.2 hsumA
      · exact (padFacts hB h2 (hinact _ (by omega) (by omega))).2.1 (ih (by omega) (by omega))
  subst hA
  refine ⟨hAlt, hsumA, fun r hr hne => ?_⟩
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hm : r ∈ List.range' 0 (segEnd 0 segs - 0) := List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩
    rw [range'_segs segs 0 hc] at hm
    obtain ⟨p, hp, hrp⟩ := List.mem_flatMap.1 hm
    rw [List.mem_range'_1] at hrp
    have ha := (hall p hp).2.2.2.1 r hrp.1 hrp.2
    simp only [isOne, decide_eq_true_eq] at ha
    have := (rowFacts hB hr).2.2.2.1
    rw [ha] at this; grind
  · exact hsumAfter r hgt hr

/-- `rb` across one record. -/
theorem rbSeg {p : Nat × Nat} (hp : p ∈ segs) :
    tr.cell tt (p.1 + p.2) UnfoldA7.Val.rb = tr.cell tt p.1 UnfoldA7.Val.rb +
      ((((if decide (tr.cell tt p.1 UnfoldA7.Val.rplv = 1) then 1 else 2) * (valOf tr tt p).len : Nat)) : Fp) := by
  have hB := baseL hL
  have hH : p.1 + p.2 ≤ tr.height tt := by have := seg_le_end segs 0 hc p hp; omega
  have hE := (sumRowV hL hc hend hall hpad).1
  have hend' : p.1 + p.2 ≤ segEnd 0 segs := (seg_le_end segs 0 hc p hp).2
  obtain ⟨hrow, hz⟩ := segInfo hB (hall p hp) hH
  have hp0 := (hall p hp).1
  have hgb : ∀ j, j < p.2 → tr.cell tt (p.1 + j) gb = 1 - tr.cell tt p.1 vz := by
    intro j hj
    obtain ⟨ha, -, hk, -⟩ := hrow j hj
    rw [(rowFacts hB (by omega)).1, ha, hk vz (by simp [valConst])]; grind
  have hvf : ∀ j, j < p.2 → tr.cell tt (p.1 + j) vf = if j = 0 then 1 else 0 := fun j hj => (hrow j hj).2.2.2
  have hlenc : ∀ j, j < p.2 → tr.cell tt (p.1 + j) len = tr.cell tt p.1 len := fun j hj =>
    (hrow j hj).2.2.1 len (by simp [valConst])
  rcases hz with ⟨hvz, hl1, hlen0, -⟩ | ⟨hvz, hlen⟩
  · -- empty value: one row, nothing counted
    have e := rbS hL (r := p.1) (by omega)
    have g0 := hgb 0 (by omega); simp only [Nat.add_zero] at g0
    rw [g0, hvz, hlen0] at e
    have hl : (valOf tr tt p).len = 0 := by simp [valOf, hlen0, Fp.toNat_zero]
    rw [hl1, e, hl]; simp only [Nat.mul_zero]; grind
  · have hl : (valOf tr tt p).len = p.2 := by
      simp [valOf, hlen, toNat_natCast, Nat.mod_eq_of_lt (show p.2 < P by
        have := height_le hB; unfold P; omega)]
    rw [hl]
    have step : ∀ d, 0 < d → d ≤ p.2 → tr.cell tt (p.1 + d) UnfoldA7.Val.rb +
        tr.cell tt p.1 UnfoldA7.Val.rplv * ((p.2 : Nat) : Fp) =
        tr.cell tt p.1 UnfoldA7.Val.rb + ((2 * d : Nat) : Fp) := by
      intro d; induction d with
      | zero => intro h0; omega
      | succ d ih =>
        intro _ hd
        rw [show p.1 + (d + 1) = p.1 + d + 1 by omega, rbS hL (by omega), hgb d (by omega), hvz,
          hvf d (by omega), hlenc d (by omega), hlen]
        rcases Nat.eq_zero_or_pos d with h0 | h0
        · subst h0; try simp only [Nat.add_zero, ite_true] at *
          rw [show 2 * (0 + 1) = 2 * 0 + 2 by rfl, natCast_add]; grind
        · have := ih h0 (by omega)
          rw [if_neg (by omega), show 2 * (d + 1) = 2 * d + 2 by omega, natCast_add]
          grind
    have := step p.2 hp0 (Nat.le_refl _)
    rcases rplvB hL (r := p.1) (by omega) with hr | hr
    · rw [hr] at this ⊢; simp only [fp_zero_ne_one, decide_false, Bool.false_eq_true, ite_false]; grind
    · rw [hr] at this ⊢; simp only [decide_true, ite_true, Nat.one_mul]
      rw [show 2 * p.2 = p.2 + p.2 by omega, natCast_add] at this
      grind

end ZkFormal.NearV3.A7ValProof

namespace ZkFormal.NearV3.A7ValProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.ValV3
  ZkFormal.NearV3.ValProof ZkFormal.NearV3.UnfoldA7
open ZkFormal.NearV3.A7NodeProof (flatMap_single flatMap_congr_mem)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal valA7 tr tt pub)
include hL
variable {segs : List (Nat × Nat)} (hc : Consec 0 segs) (hend : segEnd 0 segs ≤ tr.height tt)
  (hall : ∀ p ∈ segs, IsSeg (isOne tr tt ValV3.act) (isOne tr tt ValV3.vf) (isOne tr tt ValV3.vl) p.1 p.2)
  (hpad : ∀ r, segEnd 0 segs ≤ r → r < tr.height tt → isOne tr tt ValV3.act r = false)
include hc hend hall hpad

/-- The record flag of value record `t`. -/
def rplvOf (tr : Trace Fp) (tt : Nat) (segs : List (Nat × Nat)) (t : Nat) : Bool :=
  decide (tr.cell tt (segs.getD t default).1 UnfoldA7.Val.rplv = 1)

/-- The A7 weight of value record `t`. -/
def wV (tr : Trace Fp) (tt : Nat) (segs : List (Nat × Nat)) (t : Nat) : Nat :=
  (if rplvOf tr tt segs t then 1 else 2) * (valOf tr tt (segs.getD t default)).len

theorem rbEnd :
    tr.cell tt (segEnd 0 segs) UnfoldA7.Val.rb =
      (((valA7Sum (segs.map (valOf tr tt)) (rplvOf tr tt segs)) : Nat) : Fp) := by
  have hpos : 0 < tr.height tt := by unfold Trace.height; exact Nat.two_pow_pos _
  have gen : ∀ (l : List (Nat × Nat)) (s0 k : Nat), Consec s0 l → (∀ p ∈ l, p ∈ segs) →
      (∀ j (hj : j < l.length), segs.getD (k + j) default = l[j]) →
      tr.cell tt (segEnd s0 l) UnfoldA7.Val.rb = tr.cell tt s0 UnfoldA7.Val.rb +
        ((((List.range l.length).map fun t => wV tr tt segs (k + t)).sum : Nat) : Fp) := by
    intro l; induction l with
    | nil =>
      intro s0 k _ _ _
      simp only [segEnd, List.length_nil, List.range_zero, List.map_nil, List.sum_nil]
      rw [natCast_eq, o0]; grind
    | cons p rest ih =>
      intro s0 k hcs hm hk
      obtain ⟨rfl, hcs'⟩ := hcs
      have e := ih (p.1 + p.2) (k + 1) hcs' (fun q hq => hm q (by simp [hq]))
        (fun j hj => by rw [show k + 1 + j = k + (j + 1) by omega, hk (j + 1) (by simp; omega)]; simp)
      simp only [segEnd] at e ⊢
      rw [e, rbSeg hL hc hend hall hpad (hm p (by simp))]
      have hk0 := hk 0 (by simp); simp only [Nat.add_zero, List.getElem_cons_zero] at hk0
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map, natCast_add]
      have hcm : List.map ((fun t => wV tr tt segs (k + t)) ∘ Nat.succ) (List.range rest.length) =
          List.map (fun t => wV tr tt segs (k + 1 + t)) (List.range rest.length) :=
        List.map_congr_left (fun t _ => by simp only [Function.comp_apply]; congr 1; omega)
      rw [hcm]
      have w0 : wV tr tt segs (k + 0) = (if decide (tr.cell tt p.1 UnfoldA7.Val.rplv = 1) then 1 else 2) *
          (valOf tr tt p).len := by simp only [wV, rplvOf, Nat.add_zero, hk0]
      rw [w0]; grind
  have := gen segs 0 0 hc (fun p hp => hp) (fun j hj => by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj])
  rw [this, rb0 hL hpos]
  unfold valA7Sum
  simp only [List.length_map, Nat.zero_add]
  rw [show (0 : Fp) = ((0 : Nat) : Fp) from rfl, ← natCast_add, Nat.zero_add]
  congr 2
  apply List.map_congr_left; intro t ht; rw [List.mem_range] at ht
  simp [wV, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]

theorem a7TrafficOfV :
    TableTraffic UnfoldA7.Val.interactions tr tt pub (a7ValTraffic (segs.map (valOf tr tt)) (rplvOf tr tt segs)) := by
  have hB := baseL hL
  obtain ⟨hE, h1, h2⟩ := sumRowV hL hc hend hall hpad
  have hH : ∀ p ∈ segs, p.1 + p.2 ≤ tr.height tt := fun p hp => by
    have := seg_le_end segs 0 hc p hp; omega
  intro bb m
  rw [tableBusCount_eq, tableBusCount_eq]
  constructor
  · by_cases hb : bb = B_SIZE
    · subst hb
      have row : ∀ r, r < tr.height tt → rowTraffic UnfoldA7.Val.interactions tr tt r pub B_SIZE true =
          if r = segEnd 0 segs then [[((4 : Nat) : Fp), tr.cell tt (segEnd 0 segs) UnfoldA7.Val.rb]] else [] := by
        intro r hr
        rw [rowA7]
        simp only [show B_SIZE ≠ B_RPLV by decide, false_and, ite_false, List.nil_append, true_and]
        by_cases he : r = segEnd 0 segs
        · subst he; simp [h1]
        · rw [if_neg he, h2 r hr he]; simp [fp_zero_ne_one]
      rw [flatMap_congr_mem (fun r hr => row r (List.mem_range.1 hr)), flatMap_single _ _ _ hE,
        rbEnd hL hc hend hall hpad]
      simp only [a7ValTraffic, ite_true, List.map_cons, List.map_nil, Msg.toFp]
      rfl
    · rw [List.flatMap_eq_nil_iff.2 (fun r _ => by rw [rowA7]; simp [hb])]
      simp [a7ValTraffic, hb]
  · by_cases hb : bb = B_RPLV
    · subst hb
      have row : ∀ r, rowTraffic UnfoldA7.Val.interactions tr tt r pub B_RPLV false =
          if tr.cell tt r vf * tr.cell tt r UnfoldA7.Val.rplv = 1 then [[tr.cell tt r vid]] else [] := by
        intro r; rw [rowA7]; simp [show B_RPLV ≠ B_SIZE by decide]
      rw [flatMap_rows_segs _ segs _ hc hend (fun r h1 h2 => by
        have ha := zero_of_not_one hB h2 (by simp [bools]) (hpad r h1 h2)
        rw [row, ((rowFacts hB h2).2.2.1 ha).2.2.1, if_neg (by grind)])]
      rw [flatMap_eq_range segs]
      simp only [a7ValTraffic, ite_true, List.length_map]
      have rhs : (((List.range segs.length).filter (rplvOf tr tt segs)).map fun t =>
          ([((segs.map (valOf tr tt)).getD t default).vid] : Msg)).map Msg.toFp =
          (List.range segs.length).flatMap fun t =>
            if rplvOf tr tt segs t = true then [[tr.cell tt (segs.getD t default).1 vid]] else [] := by
        rw [List.map_map]
        have gen : ∀ l : List Nat, (∀ t ∈ l, t < segs.length) →
            (l.filter (rplvOf tr tt segs)).map (Msg.toFp ∘ fun t => ([((segs.map (valOf tr tt)).getD t default).vid] : Msg)) =
            l.flatMap fun t => if rplvOf tr tt segs t = true then [[tr.cell tt (segs.getD t default).1 vid]] else [] := by
          intro l; induction l with
          | nil => intro _; rfl
          | cons x l ih =>
            intro hl
            have hx := hl x (by simp)
            have e : ((segs.map (valOf tr tt)).getD x default).vid = (tr.cell tt (segs.getD x default).1 vid).toNat := by
              simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx, valOf]
            have ih' := ih (fun t ht => hl t (by simp [ht]))
            cases h : rplvOf tr tt segs x
            · simp only [List.filter_cons, h, Bool.false_eq_true, ite_false, List.flatMap_cons, List.nil_append]
              exact ih'
            · simp only [List.filter_cons, h, ite_true, List.map_cons, List.flatMap_cons, List.cons_append,
                List.nil_append, Function.comp_def, e, Msg.toFp, List.map_cons, List.map_nil, Fp.ofNat_toNat]
              congr 1
        exact gen _ (fun t ht => List.mem_range.1 ht)
      rw [rhs]
      congr 1
      apply flatMap_congr_mem; intro t ht; rw [List.mem_range] at ht
      have hp : segs.getD t default ∈ segs := by
        rw [show segs.getD t default = segs[t] by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]]
        exact List.getElem_mem ht
      obtain ⟨hrow, -⟩ := segInfo hB (hall _ hp) (hH _ hp)
      have hp0 := (hall _ hp).1
      have e : List.range' (segs.getD t default).1 (segs.getD t default).2 =
          (segs.getD t default).1 :: List.range' ((segs.getD t default).1 + 1) ((segs.getD t default).2 - 1) := by
        rw [show (segs.getD t default).2 = ((segs.getD t default).2 - 1) + 1 by omega, List.range'_succ]; simp
      have hrest : (List.range' ((segs.getD t default).1 + 1) ((segs.getD t default).2 - 1)).flatMap
          (fun r => rowTraffic UnfoldA7.Val.interactions tr tt r pub B_RPLV false) = [] := by
        refine List.flatMap_eq_nil_iff.2 (fun r hr => ?_)
        rw [List.mem_range'_1] at hr
        have := (hrow (r - (segs.getD t default).1) (by omega)).2.2.2
        rw [show (segs.getD t default).1 + (r - (segs.getD t default).1) = r by omega,
          if_neg (by omega)] at this
        rw [row, this, if_neg (by grind)]
      rw [e, List.flatMap_cons, hrest, List.append_nil]
      have hvf0 := (hrow 0 hp0).2.2.2; simp only [Nat.add_zero, ite_true] at hvf0
      rw [row, hvf0]
      rcases rplvB hL (r := (segs.getD t default).1) (by have := hH _ hp; omega) with h | h
      · have hf : rplvOf tr tt segs t = false := by unfold rplvOf; rw [h]; simp [fp_zero_ne_one]
        rw [h, if_neg (by grind), hf]; rfl
      · have hf : rplvOf tr tt segs t = true := by unfold rplvOf; rw [h]; simp
        rw [h, if_pos (by grind), hf]; rfl
    · rw [List.flatMap_eq_nil_iff.2 (fun r _ => by rw [rowA7]; simp [hb])]
      simp [a7ValTraffic, hb]

end ZkFormal.NearV3.A7ValProof

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- **The `valA7` view**: one segmentation gives the base view and the A7 traffic. -/
theorem valA7_view (tr : Trace Fp) (pub : List Fp) (tt : Nat) (hL : TableLocal UnfoldA7.valA7 tr tt pub) :
    ∃ es S, ValWf es ∧ TableTraffic ValV3.interactions tr tt pub (valTraffic es) ∧
      TableTraffic UnfoldA7.Val.interactions tr tt pub (a7ValTraffic es S) := by
  have hB := A7ValProof.baseL hL
  obtain ⟨segs, hc, hend, hall, hpad⟩ := val_segs_exist hB
  obtain ⟨w, t⟩ := val_view_of_segs hB segs hc hend hall hpad
  exact ⟨_, _, w, t, A7ValProof.a7TrafficOfV hL hc hend hall hpad⟩

end ZkFormal.NearV3
