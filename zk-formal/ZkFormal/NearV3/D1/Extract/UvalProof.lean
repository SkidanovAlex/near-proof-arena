import ZkFormal.NearV3.D1.Extract.KibProof
import ZkFormal.NearV3.D1.Tables.UvalDefs

/-!
# `ZkFormal.NearV3.D1.Extract.UvalProof` — the `uvalV3` view (`UvalViewStmt`, `uval_view`)

Lane `v3-d1-a7b` (plan §5 R-5 → (B)).  `uvalV3` (table 32) is a new `VBYTES` sender: one `UvalE`
per active row (in row order), the value-record byte `(vid, pos, b)` with `b < 256`.  Traffic:
sends `VBYTES (vid, pos, b)`; nothing else.
-/

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

structure UvalE where
  vid : Nat
  pos : Nat
  b : Nat
  deriving Repr, Inhabited

structure UvalWf (es : List UvalE) : Prop where
  byte : ∀ e ∈ es, e.b < 256
  canon : ∀ e ∈ es, e.vid < P ∧ e.pos < P
  rows : es.length ≤ 2 ^ UvalV3.maxLog

def uvalSends (es : List UvalE) (b : Nat) : List Msg :=
  if b = ZkFormal.NearV3.B_VBYTES then es.map fun e => [e.vid, e.pos, e.b] else []

def uvalTraffic (es : List UvalE) : Traffic := ⟨uvalSends es, fun _ => []⟩

/-- **The `uvalV3` view statement.** -/
def UvalViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal UvalV3.table tr t pub →
    ∃ es, UvalWf es ∧ TableTraffic UvalV3.interactions tr t pub (uvalTraffic es)

end ZkFormal.NearV3.D1

namespace ZkFormal.NearV3.D1.UvalProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.UvalV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

def rowOf (tr : Trace Fp) (tt q : Nat) : UvalE :=
  ⟨cv tr tt q vid, cv tr tt q pos, bitsVal (fun x => cv tr tt q (bb x)) 0 8⟩

def isA (tr : Trace Fp) (tt q : Nat) : Bool := decide (tr.cell tt q act = 1)

section
variable (hL : TableLocal UvalV3.table tr tt pub)
include hL

theorem bbBool {q : Nat} (hq : q < tr.height tt) (x : Nat) (hx : x < 8) :
    tr.cell tt q (bb x) = 0 ∨ tr.cell tt q (bb x) = 1 := by
  have := hL.constr q hq (bool (c (bb x))) (by
    unfold UvalV3.table UvalV3.constraints
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range]
    exact Or.inl (Or.inr ⟨x, hx, rfl⟩))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem actBool {q : Nat} (hq : q < tr.height tt) :
    tr.cell tt q act = 0 ∨ tr.cell tt q act = 1 := by
  have := hL.constr q hq (bool (c act)) (by
    unfold UvalV3.table UvalV3.constraints
    exact List.mem_append_left _ (List.mem_cons_self ..))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem b_eq {q : Nat} (hq : q < tr.height tt) (ha : tr.cell tt q act = 1) :
    tr.cell tt q b = ((rowOf tr tt q).b : Fp) := by
  have h := hL.constr q hq (.mul (c act) (sub (c b) (bits (fun j => c (bb j)) 0 8))) (by
    unfold UvalV3.table UvalV3.constraints; simp)
  rw [eval_mul, eval_c, eval_sub, eval_c,
    eval_bits tr tt q pub bb 0 8 (fun x hx => by simpa using bbBool hL hq x hx), ha] at h
  simp only [rowOf]
  grind

theorem b_lt {q : Nat} (hq : q < tr.height tt) : (rowOf tr tt q).b < 256 :=
  bitsVal_lt _ 0 8 (fun x hx => cv_bool (by simpa using bbBool hL hq x hx))

theorem rowT {q : Nat} (hq : q < tr.height tt) (bu : Nat) (sd : Bool) :
    rowTraffic UvalV3.interactions tr tt q pub bu sd =
      if isA tr tt q then (if sd then uvalSends [rowOf tr tt q] bu else []).map Msg.toFp else [] := by
  unfold rowTraffic UvalV3.interactions
  simp only [List.flatMap_cons, List.flatMap_nil, Dsl.send, Interaction.multNat,
    Interaction.multNat.go, Interaction.msgVal, List.map_cons, List.map_nil, List.append_nil]
  by_cases ha : tr.cell tt q act = 1
  · have hb := b_eq hL hq ha
    simp only [eval_c, ha, ite_true, isA, decide_true]
    cases sd <;> by_cases h1 : bu = ZkFormal.NearV3.B_VBYTES <;>
      simp_all [uvalSends, Msg.toFp, rowOf, cv, Fp.ofNat_toNat, natCast_eq]
    all_goals exact fun h => h1 h.symm
  · rcases actBool hL hq with h0 | h0
    · simp [eval_c, h0, isA]
    · exact absurd h0 ha

end

theorem uvalSends_flat (es : List UvalE) (bu : Nat) :
    uvalSends es bu = es.flatMap fun e => uvalSends [e] bu := by
  unfold uvalSends; split <;> simp [map_eq_flatMap]

end ZkFormal.NearV3.D1.UvalProof

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near UvalProof

/-- **The `uvalV3` view.** -/
theorem uval_view : UvalViewStmt := by
  intro tr pub tt hL
  let rows := (List.range (tr.height tt)).filter (isA tr tt)
  have hall : ∀ bu sd, (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic UvalV3.interactions tr tt q pub bu sd) =
      (if sd then uvalSends (rows.map (rowOf tr tt)) bu else []).map Msg.toFp := by
    intro bu sd
    rw [flatMap_congr' (G := fun q => if isA tr tt q then
        (if sd then uvalSends [rowOf tr tt q] bu else []).map Msg.toFp else [])
      (fun q hq => UvalProof.rowT hL (List.mem_range.1 hq) bu sd)]
    rw [KibProof.flatMap_if]
    cases sd
    · simp
    · simp only [ite_true]
      rw [uvalSends_flat, List.map_flatMap, List.flatMap_map]
  refine ⟨rows.map (rowOf tr tt), ⟨?_, ?_, ?_⟩, fun bu m => ⟨?_, ?_⟩⟩
  · intro e he
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 he
    exact b_lt hL (List.mem_range.1 (List.mem_filter.1 hq).1)
  · intro e he
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 he
    exact ⟨cv_lt _ _ _ _, cv_lt _ _ _ _⟩
  · rw [List.length_map]
    refine Nat.le_trans (List.length_filter_le _ _) ?_
    rw [List.length_range]
    unfold Trace.height
    exact Nat.pow_le_pow_right (by omega) hL.log_le
  · simp only [uvalTraffic]; rw [tableBusCount_eq, hall]; rfl
  · simp only [uvalTraffic]; rw [tableBusCount_eq, hall]; rfl

end ZkFormal.NearV3.D1
