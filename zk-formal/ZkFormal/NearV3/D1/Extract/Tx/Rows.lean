import ZkFormal.Near.Extract.Segments
import ZkFormal.Near.Extract.BusCount
import ZkFormal.NearV3.D1.Tables.TxDefs

/-!
# `ZkFormal.NearV3.D1.Extract.Tx.Rows` — row structure of `txV3`

Lane `v3-d1-phase2` (milestone V2).  From `TableLocal TxV3.table`: the boolean columns, the
segment facts (active rows are a prefix of 16-row ops: `lf` on lane 0, `ll` on lane 15, `l1` on
lane 1, `lane` counts `0 … 15`, the op constants are constant over the op) — `segInfo`.
-/

namespace ZkFormal.NearV3.D1.TxProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.TxV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-! ## Constraint membership -/

theorem mem_shape {e : Expr} (h : e ∈ cShape) : e ∈ TxV3.table.constraints :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))
theorem mem_flags {e : Expr} (h : e ∈ cFlags) : e ∈ TxV3.table.constraints :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))
theorem mem_chains {e : Expr} (h : e ∈ cChains) : e ∈ TxV3.table.constraints :=
  List.mem_append_left _ (List.mem_append_right _ h)
theorem mem_verdict {e : Expr} (h : e ∈ cVerdict) : e ∈ TxV3.table.constraints :=
  List.mem_append_right _ h

theorem mem_shapeL {e : Expr} (h : e ∈ ([
    .mul (c lf) (not (c act)), .mul (c ll) (not (c act)), .mul (c l1) (not (c act)),
    .mul .isFirst (sub (c act) (c lf)),
    .mul .isLast (.mul (c act) (not (c ll))),
    inOpE (not (n act)), inOpE (n lf),
    mul3 (c ll) (n act) (not (n lf)),
    mul3 .isTransition (not (c act)) (n act),
    sub (c lane) laneE,
    first (c lane), inOpE (sub (n lane) (.add (c lane) (k 1))), lastE (sub (c lane) (k 15)),
    first (c l1), inOpE (sub (n l1) (c lf)),
    .mul (c act) (sub (c g) (.add (smul LANES (c op)) (c lane))) ] : List Expr)) :
    e ∈ TxV3.table.constraints :=
  mem_shape (List.mem_append_left _ (List.mem_append_right _ h))

theorem mem_bool {x : Nat} (h : x ∈ boolCols) : bool (c x) ∈ TxV3.table.constraints :=
  mem_shape (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map_of_mem (f := fun x => bool (c x)) h)))

theorem mem_const {x : Nat} (h : x ∈ opConst) : inOpE (sub (n x) (c x)) ∈ TxV3.table.constraints :=
  mem_shape (List.mem_append_right _ (List.mem_map_of_mem (f := fun x => inOpE (sub (n x) (c x))) h))

theorem nxt {r : Nat} (h : r + 1 < tr.height tt) : (r + 1) % tr.height tt = r + 1 := Nat.mod_eq_of_lt h

def isOne (tr : Trace Fp) (tt x : Nat) (r : Nat) : Bool := decide (tr.cell tt r x = 1)

theorem bool_act : act ∈ boolCols := by simp [boolCols]
theorem bool_lf : lf ∈ boolCols := by simp [boolCols]
theorem bool_ll : ll ∈ boolCols := by simp [boolCols]

section
variable (hL : TableLocal TxV3.table tr tt pub)
include hL

theorem con {r : Nat} (hr : r < tr.height tt) {e : Expr} (he : e ∈ TxV3.table.constraints) :
    e.eval tr tt r pub = 0 := hL.constr r hr e he

theorem isBool {r : Nat} (hr : r < tr.height tt) {x : Nat} (hx : x ∈ boolCols) :
    tr.cell tt r x = 0 ∨ tr.cell tt r x = 1 := by
  have := con hL hr (mem_bool hx)
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem zero_of_not_one {r : Nat} (hr : r < tr.height tt) {x : Nat} (hx : x ∈ boolCols)
    (h : isOne tr tt x r = false) : tr.cell tt r x = 0 := by
  rcases isBool hL hr hx with h' | h'
  · exact h'
  · simp [isOne, h'] at h

theorem rowFacts {r : Nat} (hr : r < tr.height tt) :
    (tr.cell tt r lf = 1 → tr.cell tt r act = 1 ∧ tr.cell tt r lane = 0 ∧ tr.cell tt r l1 = 0) ∧
    (tr.cell tt r ll = 1 → tr.cell tt r act = 1 ∧ tr.cell tt r lane = 15) ∧
    (tr.cell tt r l1 = 1 → tr.cell tt r act = 1) ∧
    (tr.cell tt r act = 0 → tr.cell tt r lf = 0 ∧ tr.cell tt r l1 = 0) := by
  have h1 := con hL hr (e := .mul (c lf) (not (c act))) (mem_shapeL (by simp))
  have h2 := con hL hr (e := .mul (c ll) (not (c act))) (mem_shapeL (by simp))
  have h3 := con hL hr (e := .mul (c l1) (not (c act))) (mem_shapeL (by simp))
  have h4 := con hL hr (e := first (c lane)) (mem_shapeL (by simp))
  have h5 := con hL hr (e := lastE (sub (c lane) (k 15))) (mem_shapeL (by simp))
  have h6 := con hL hr (e := first (c l1)) (mem_shapeL (by simp))
  simp only [first, lastE, eval_mul, eval_c, eval_not, eval_sub, eval_k] at h1 h2 h3 h4 h5 h6
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h] at h1 h4 h6; exact ⟨by grind, by grind, by grind⟩
  · rw [h] at h2 h5; exact ⟨by grind, by grind⟩
  · rw [h] at h3; grind
  · rw [h] at h1 h3; exact ⟨by grind, by grind⟩

/-- Inside an op (an active row that is not lane 15): the next row is the next lane of the
same op. -/
theorem within {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 1)
    (hl : tr.cell tt r ll = 0) :
    tr.cell tt (r + 1) act = 1 ∧ tr.cell tt (r + 1) lf = 0 ∧
    tr.cell tt (r + 1) lane = tr.cell tt r lane + 1 ∧ tr.cell tt (r + 1) l1 = tr.cell tt r lf ∧
    ∀ x ∈ opConst, tr.cell tt (r + 1) x = tr.cell tt r x := by
  have hr' : r < tr.height tt := by omega
  have h1 := con hL hr' (e := inOpE (not (n act))) (mem_shapeL (by simp))
  have h2 := con hL hr' (e := inOpE (n lf)) (mem_shapeL (by simp))
  have h3 := con hL hr' (e := inOpE (sub (n lane) (.add (c lane) (k 1)))) (mem_shapeL (by simp))
  have h4 := con hL hr' (e := inOpE (sub (n l1) (c lf))) (mem_shapeL (by simp))
  simp only [inOpE, inOp, eval_mul, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k,
    nxt hr] at h1 h2 h3 h4
  rw [ha, hl] at h1 h2 h3 h4
  refine ⟨by grind, by grind, by grind, by grind, fun x hx => ?_⟩
  have h5 := con hL hr' (mem_const hx)
  simp only [inOpE, inOp, eval_mul, eval_c, eval_not, eval_n, eval_sub, nxt hr] at h5
  rw [ha, hl] at h5; grind

theorem nextSeg {r : Nat} (hr : r + 1 < tr.height tt) (hl : tr.cell tt r ll = 1)
    (ha : tr.cell tt (r + 1) act = 1) : tr.cell tt (r + 1) lf = 1 := by
  have h1 := con hL (by omega : r < _) (e := mul3 (c ll) (n act) (not (n lf))) (mem_shapeL (by simp))
  simp only [eval_mul3, eval_c, eval_not, eval_n, nxt hr] at h1
  rw [ha, hl] at h1; grind

theorem pad {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 0) :
    tr.cell tt (r + 1) act = 0 := by
  have h1 := con hL (by omega : r < _) (e := mul3 .isTransition (not (c act)) (n act))
    (mem_shapeL (by simp))
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_isTransition, nxt hr,
    if_neg (show ¬ r + 1 = tr.height tt by omega)] at h1
  rw [ha] at h1; grind

theorem row0 (h0 : 0 < tr.height tt) : tr.cell tt 0 act = tr.cell tt 0 lf := by
  have h1 := con hL h0 (e := .mul .isFirst (sub (c act) (c lf))) (mem_shapeL (by simp))
  simp only [eval_mul, eval_c, eval_sub, eval_isFirst] at h1
  grind

theorem lastRow (h0 : 0 < tr.height tt) (ha : tr.cell tt (tr.height tt - 1) act = 1) :
    tr.cell tt (tr.height tt - 1) ll = 1 := by
  have h1 := con hL (by omega : tr.height tt - 1 < _)
    (e := .mul .isLast (.mul (c act) (not (c ll)))) (mem_shapeL (by simp))
  simp only [eval_mul, eval_c, eval_not, eval_isLast,
    if_pos (show tr.height tt - 1 + 1 = tr.height tt by omega)] at h1
  rw [ha] at h1; grind

theorem segFacts (h0act : tr.cell tt 0 act = 1) :
    SegFacts (tr.height tt) (isOne tr tt act) (isOne tr tt lf) (isOne tr tt ll) where
  first_act r hr h := by
    simp only [isOne, decide_eq_true_eq] at h ⊢; exact ((rowFacts hL hr).1 h).1
  last_act r hr h := by
    simp only [isOne, decide_eq_true_eq] at h ⊢; exact ((rowFacts hL hr).2.1 h).1
  cont r hr ha hl := by
    simp only [isOne, decide_eq_true_eq] at ha
    have := within hL hr ha (zero_of_not_one hL (by omega) bool_ll hl)
    simp [isOne, this.1, this.2.1]
  next r hr hl ha := by
    simp only [isOne, decide_eq_true_eq] at hl ha ⊢
    exact nextSeg hL hr hl ha
  pad r hr ha := by
    have := pad hL hr (zero_of_not_one hL (by omega) bool_act ha)
    simp [isOne, this]
  start h0 := by simp only [isOne, decide_eq_true_eq]; rw [← row0 hL h0, h0act]
  stop h0 ha := by
    simp only [isOne, decide_eq_true_eq] at ha ⊢; exact lastRow hL h0 ha

theorem height_le : tr.height tt ≤ 2 ^ 19 := by
  have := hL.log_le; unfold Trace.height; exact Nat.pow_le_pow_right (by omega) this

theorem height_lt_P : tr.height tt < P := by have := height_le hL; unfold P; omega

/-- **One op = 16 rows.** -/
theorem segInfo {s ℓ : Nat}
    (hseg : IsSeg (isOne tr tt act) (isOne tr tt lf) (isOne tr tt ll) s ℓ) (hH : s + ℓ ≤ tr.height tt) :
    ℓ = 16 ∧
    (∀ j, j < 16 → tr.cell tt (s + j) act = 1 ∧ tr.cell tt (s + j) lane = ((j : Nat) : Fp) ∧
      tr.cell tt (s + j) lf = (if j = 0 then 1 else 0) ∧
      tr.cell tt (s + j) l1 = (if j = 1 then 1 else 0) ∧
      tr.cell tt (s + j) ll = (if j = 15 then 1 else 0) ∧
      ∀ x ∈ opConst, tr.cell tt (s + j) x = tr.cell tt s x) := by
  obtain ⟨hpos, hfs, hle, hact, hfirst, hlast⟩ := hseg
  have hlf : tr.cell tt s lf = 1 := by simpa [isOne] using hfs
  have hll : tr.cell tt (s + ℓ - 1) ll = 1 := by simpa [isOne] using hle
  have hA : ∀ j, j < ℓ → tr.cell tt (s + j) act = 1 := fun j hj => by
    have := hact (s + j) (by omega) (by omega); simpa [isOne] using this
  have hW : ∀ j, j + 1 < ℓ → tr.cell tt (s + j) ll = 0 := fun j hj =>
    zero_of_not_one hL (by omega) bool_ll (hlast (s + j) (by omega) (by omega))
  have hw := fun j (hj : j + 1 < ℓ) => within hL (r := s + j) (by omega) (hA j (by omega)) (hW j hj)
  have hs := (rowFacts hL (by omega : s < _)).1 hlf
  have he := (rowFacts hL (by omega : s + ℓ - 1 < _)).2.1 hll
  have hi := counter_of (f := fun q => tr.cell tt q lane) (s := s) (ℓ := ℓ) (v0 := 0)
    hs.2.1 (fun q h1 h2 => by
      have := (hw (q - s) (by omega)).2.2.1; rwa [show s + (q - s) = q by omega] at this)
  have hP := height_lt_P hL
  have h16 : ℓ = 16 := by
    have e := hi (s + ℓ - 1) (by omega) (by omega)
    rw [he.2, show 0 + (s + ℓ - 1 - s) = ℓ - 1 by omega] at e
    have := ofNat_inj (a := 15) (b := ℓ - 1) (by unfold P; omega) (by omega) e
    omega
  subst h16
  have hlfz : ∀ j, 0 < j → j < 16 → tr.cell tt (s + j) lf = 0 := fun j h0 hj =>
    zero_of_not_one hL (by omega) bool_lf (hfirst (s + j) (by omega) (by omega))
  refine ⟨rfl, fun j hj => ⟨hA j hj, ?_, ?_, ?_, ?_, fun x hx => ?_⟩⟩
  · have := hi (s + j) (by omega) (by omega); rwa [show 0 + (s + j - s) = j by omega] at this
  · by_cases h0 : j = 0
    · subst h0; simpa using hlf
    · rw [if_neg h0]; exact hlfz j (by omega) hj
  · rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; simpa using hs.2.2
    · have := (hw (j - 1) (by omega)).2.2.2.1
      rw [show s + (j - 1) + 1 = s + j by omega] at this
      rw [this]
      by_cases h1 : j = 1
      · subst h1; simpa using hlf
      · rw [if_neg h1]; exact hlfz (j - 1) (by omega) (by omega)
  · by_cases h15 : j = 15
    · subst h15; simpa using hll
    · rw [if_neg h15]; exact hW j (by omega)
  · have := const_of (f := fun q => tr.cell tt q x) (s := s) (ℓ := 16) (fun q h1 h2 => by
      have := (hw (q - s) (by omega)).2.2.2.2 x hx; rwa [show s + (q - s) = q by omega] at this)
    exact this (s + j) (by omega) (by omega)

end

end ZkFormal.NearV3.D1.TxProof
