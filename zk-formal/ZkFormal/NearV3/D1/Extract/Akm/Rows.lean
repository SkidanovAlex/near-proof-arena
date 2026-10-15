import ZkFormal.Near.Extract.Segments
import ZkFormal.Near.Extract.BusCount
import ZkFormal.NearV3.D1.Tables.AkmDefs

/-!
# `ZkFormal.NearV3.D1.Extract.Akm.Rows` — row structure of `akmV3`

Lane `v3-d1-phase2` (milestone V3, part 1).  From `TableLocal AkmV3.table`: the boolean columns
and the segments (active rows are a prefix of value segments `af … al`; `pos` counts `0 … ℓ−1`;
`vid`, the tag bits, `tlast`, `U` are constant over a segment) — `segInfo`.
-/

namespace ZkFormal.NearV3.D1.AkmProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.AkmV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem mem_shape {e : Expr} (h : e ∈ cShape) : e ∈ AkmV3.table.constraints :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
theorem mem_fields {e : Expr} (h : e ∈ cFields) : e ∈ AkmV3.table.constraints :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
theorem mem_events {e : Expr} (h : e ∈ cEvents) : e ∈ AkmV3.table.constraints :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))
theorem mem_utf8 {e : Expr} (h : e ∈ cUtf8) : e ∈ AkmV3.table.constraints :=
  List.mem_append_left _ (List.mem_append_right _ h)
theorem mem_mem {e : Expr} (h : e ∈ cMem) : e ∈ AkmV3.table.constraints :=
  List.mem_append_right _ h

theorem mem_bool {x : Nat} (h : x ∈ boolCols) : bool (c x) ∈ AkmV3.table.constraints :=
  mem_shape (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map_of_mem (f := fun x => bool (c x)) h)))

theorem mem_const {x : Nat} (h : x ∈ segConst) :
    mul3 (c act) (not (c al)) (sub (n x) (c x)) ∈ AkmV3.table.constraints :=
  mem_shape (List.mem_append_right _ (List.mem_map_of_mem
    (f := fun x => mul3 (c act) (not (c al)) (sub (n x) (c x))) h))

theorem nxt {r : Nat} (h : r + 1 < tr.height tt) : (r + 1) % tr.height tt = r + 1 := Nat.mod_eq_of_lt h

def isOne (tr : Trace Fp) (tt x : Nat) (r : Nat) : Bool := decide (tr.cell tt r x = 1)

theorem bool_act : act ∈ boolCols := by simp [boolCols]
theorem bool_af : af ∈ boolCols := by simp [boolCols]
theorem bool_al : al ∈ boolCols := by simp [boolCols]

section
variable (hL : TableLocal AkmV3.table tr tt pub)
include hL

theorem con {r : Nat} (hr : r < tr.height tt) {e : Expr} (he : e ∈ AkmV3.table.constraints) :
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
    (tr.cell tt r af = 1 → tr.cell tt r act = 1 ∧ tr.cell tt r pos = 0) ∧
    (tr.cell tt r al = 1 → tr.cell tt r act = 1) ∧
    (tr.cell tt r act = 0 → tr.cell tt r af = 0 ∧ tr.cell tt r al = 0) := by
  have h1 := con hL hr (mem_shape (e := .mul (c af) (not (c act))) (by simp [cShape]))
  have h2 := con hL hr (mem_shape (e := .mul (c al) (not (c act))) (by simp [cShape]))
  have h3 := con hL hr (mem_shape (e := .mul (c af) (c pos)) (by simp [cShape]))
  simp only [eval_mul, eval_c, eval_not] at h1 h2 h3
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h] at h1 h3; exact ⟨by grind, by grind⟩
  · rw [h] at h2; grind
  · rw [h] at h1 h2; exact ⟨by grind, by grind⟩

theorem within {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 1)
    (hl : tr.cell tt r al = 0) :
    tr.cell tt (r + 1) act = 1 ∧ tr.cell tt (r + 1) af = 0 ∧
    tr.cell tt (r + 1) pos = tr.cell tt r pos + 1 ∧
    ∀ x ∈ segConst, tr.cell tt (r + 1) x = tr.cell tt r x := by
  have hr' : r < tr.height tt := by omega
  have h1 := con hL hr' (mem_shape (e := mul3 (c act) (not (c al)) (not (n act))) (by simp [cShape]))
  have h2 := con hL hr' (mem_shape (e := mul3 (c act) (not (c al)) (n af)) (by simp [cShape]))
  have h3 := con hL hr' (mem_shape (e := mul3 (c act) (not (c al)) (sub (n pos) (.add (c pos) (k 1))))
    (by simp [cShape]))
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k, nxt hr] at h1 h2 h3
  rw [ha, hl] at h1 h2 h3
  refine ⟨by grind, by grind, by grind, fun x hx => ?_⟩
  have h5 := con hL hr' (mem_const hx)
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, nxt hr] at h5
  rw [ha, hl] at h5; grind

theorem nextSeg {r : Nat} (hr : r + 1 < tr.height tt) (hl : tr.cell tt r al = 1)
    (ha : tr.cell tt (r + 1) act = 1) : tr.cell tt (r + 1) af = 1 := by
  have h1 := con hL (by omega : r < _) (mem_shape (e := mul3 (c al) (n act) (not (n af))) (by simp [cShape]))
  simp only [eval_mul3, eval_c, eval_not, eval_n, nxt hr] at h1
  rw [ha, hl] at h1; grind

theorem pad {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 0) :
    tr.cell tt (r + 1) act = 0 := by
  have h1 := con hL (by omega : r < _) (mem_shape (e := mul3 .isTransition (not (c act)) (n act))
    (by simp [cShape]))
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_isTransition, nxt hr,
    if_neg (show ¬ r + 1 = tr.height tt by omega)] at h1
  rw [ha] at h1; grind

theorem row0 (h0 : 0 < tr.height tt) : tr.cell tt 0 act = tr.cell tt 0 af := by
  have h1 := con hL h0 (mem_shape (e := .mul .isFirst (sub (c act) (c af))) (by simp [cShape]))
  simp only [eval_mul, eval_c, eval_sub, eval_isFirst] at h1
  grind

theorem lastRow (h0 : 0 < tr.height tt) (ha : tr.cell tt (tr.height tt - 1) act = 1) :
    tr.cell tt (tr.height tt - 1) al = 1 := by
  have h1 := con hL (by omega : tr.height tt - 1 < _)
    (mem_shape (e := .mul .isLast (.mul (c act) (not (c al)))) (by simp [cShape]))
  simp only [eval_mul, eval_c, eval_not, eval_isLast,
    if_pos (show tr.height tt - 1 + 1 = tr.height tt by omega)] at h1
  rw [ha] at h1; grind

theorem segFacts (h0act : tr.cell tt 0 act = 1) :
    SegFacts (tr.height tt) (isOne tr tt act) (isOne tr tt af) (isOne tr tt al) where
  first_act r hr h := by
    simp only [isOne, decide_eq_true_eq] at h ⊢; exact ((rowFacts hL hr).1 h).1
  last_act r hr h := by
    simp only [isOne, decide_eq_true_eq] at h ⊢; exact (rowFacts hL hr).2.1 h
  cont r hr ha hl := by
    simp only [isOne, decide_eq_true_eq] at ha
    have := within hL hr ha (zero_of_not_one hL (by omega) bool_al hl)
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

theorem height_le : tr.height tt ≤ 2 ^ 22 := by
  have := hL.log_le; unfold Trace.height; exact Nat.pow_le_pow_right (by omega) this

theorem height_lt_P : tr.height tt < P := by have := height_le hL; unfold P; omega

/-- A value segment of length `ℓ`: rows `s … s+ℓ−1`, `pos = j`, `af` exactly first, `al` exactly
last, segment constants. -/
structure SegAt (tr : Trace Fp) (tt s ℓ : Nat) : Prop where
  pos : 0 < ℓ
  h : s + ℓ ≤ tr.height tt
  act : ∀ j, j < ℓ → tr.cell tt (s + j) act = 1
  posv : ∀ j, j < ℓ → tr.cell tt (s + j) AkmV3.pos = ((j : Nat) : Fp)
  af : ∀ j, j < ℓ → tr.cell tt (s + j) af = (if j = 0 then 1 else 0)
  al : ∀ j, j < ℓ → tr.cell tt (s + j) al = (if j + 1 = ℓ then 1 else 0)
  const : ∀ j, j < ℓ → ∀ x ∈ segConst, tr.cell tt (s + j) x = tr.cell tt s x

theorem segInfo {s ℓ : Nat}
    (hseg : IsSeg (isOne tr tt act) (isOne tr tt af) (isOne tr tt al) s ℓ) (hH : s + ℓ ≤ tr.height tt) :
    SegAt tr tt s ℓ := by
  obtain ⟨hpos, hfs, hle, hact, hfirst, hlast⟩ := hseg
  have haf : tr.cell tt s af = 1 := by simpa [isOne] using hfs
  have hal : tr.cell tt (s + ℓ - 1) al = 1 := by simpa [isOne] using hle
  have hA : ∀ j, j < ℓ → tr.cell tt (s + j) act = 1 := fun j hj => by
    have := hact (s + j) (by omega) (by omega); simpa [isOne] using this
  have hW : ∀ j, j + 1 < ℓ → tr.cell tt (s + j) al = 0 := fun j hj =>
    zero_of_not_one hL (by omega) bool_al (hlast (s + j) (by omega) (by omega))
  have hw := fun j (hj : j + 1 < ℓ) => within hL (r := s + j) (by omega) (hA j (by omega)) (hW j hj)
  have hs := (rowFacts hL (by omega : s < _)).1 haf
  have hi := counter_of (f := fun q => tr.cell tt q AkmV3.pos) (s := s) (ℓ := ℓ) (v0 := 0)
    hs.2 (fun q h1 h2 => by
      have := (hw (q - s) (by omega)).2.2.1; rwa [show s + (q - s) = q by omega] at this)
  refine ⟨hpos, hH, hA, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj x hx => ?_⟩
  · have := hi (s + j) (by omega) (by omega); rwa [show 0 + (s + j - s) = j by omega] at this
  · by_cases h0 : j = 0
    · subst h0; simpa using haf
    · rw [if_neg h0]
      exact zero_of_not_one hL (by omega) bool_af (hfirst (s + j) (by omega) (by omega))
  · by_cases h1 : j + 1 = ℓ
    · rw [if_pos h1]; rwa [show s + ℓ - 1 = s + j by omega] at hal
    · rw [if_neg h1]; exact hW j (by omega)
  · exact const_of (f := fun q => tr.cell tt q x) (s := s) (ℓ := ℓ) (fun q h1 h2 => by
      have := (hw (q - s) (by omega)).2.2.2 x hx; rwa [show s + (q - s) = q by omega] at this)
      (s + j) (by omega) (by omega)

end

end ZkFormal.NearV3.D1.AkmProof
