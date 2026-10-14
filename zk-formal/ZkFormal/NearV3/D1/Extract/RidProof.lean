import ZkFormal.NearV3.D1.Extract.KibProof

/-!
# `ZkFormal.NearV3.D1.Extract.RidProof` — the `ridV3` view (`RidViewStmt`, `rid_view`)

Lane `v3-d1-phase2` (milestone V1).  One `RidE` per active row (in row order): the public
local-receipt-id byte `(j, b)`, the slot `l` and the byte index `i < 32` with `j ≡ 32·l + i`
in the field.  Traffic: receives `PRID (j, b)`, sends `RIDS (W_LOC + l, i, b)`.
-/

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

structure RidE where
  j : Nat
  l : Nat
  i : Nat
  b : Nat
  deriving Repr, Inhabited

structure RidWf (es : List RidE) : Prop where
  idx : ∀ e ∈ es, e.i < 32 ∧ Fp.ofNat e.j = Fp.ofNat (32 * e.l + e.i)
  canon : ∀ e ∈ es, e.j < P ∧ e.l < P ∧ e.b < P
  rows : es.length ≤ 2 ^ RidV3.maxLog

def ridSends (es : List RidE) (b : Nat) : List Msg :=
  if b = B_RIDS then es.map fun e => [W_LOC + e.l, e.i, e.b] else []

def ridRecvs (es : List RidE) (b : Nat) : List Msg :=
  if b = B_PRID then es.map fun e => [e.j, e.b] else []

def ridTraffic (es : List RidE) : Traffic := ⟨ridSends es, ridRecvs es⟩

/-- **The `ridV3` view statement.** -/
def RidViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal RidV3.table tr t pub →
    ∃ es, RidWf es ∧ TableTraffic RidV3.interactions tr t pub (ridTraffic es)

end ZkFormal.NearV3.D1

namespace ZkFormal.NearV3.D1.RidProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.RidV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

def rowOf (tr : Trace Fp) (tt q : Nat) : RidE :=
  ⟨cv tr tt q j, cv tr tt q l, bitsVal (fun x => cv tr tt q (ib x)) 0 5, cv tr tt q b⟩

def isA (tr : Trace Fp) (tt q : Nat) : Bool := decide (tr.cell tt q act = 1)

section
variable (hL : TableLocal RidV3.table tr tt pub)
include hL

theorem ibBool {q : Nat} (hq : q < tr.height tt) (x : Nat) (hx : x < 5) :
    tr.cell tt q (ib x) = 0 ∨ tr.cell tt q (ib x) = 1 := by
  have := hL.constr q hq (bool (c (ib x))) (by
    unfold RidV3.table RidV3.constraints
    simp only [List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl (Or.inr ⟨x, hx, rfl⟩))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem iE_eval {q : Nat} (hq : q < tr.height tt) :
    RidV3.iE.eval tr tt q pub = Fp.ofNat (rowOf tr tt q).i := by
  unfold RidV3.iE
  rw [eval_bits tr tt q pub ib 0 5 (fun x hx => by simpa using ibBool hL hq x hx)]
  rfl

theorem i_lt {q : Nat} (hq : q < tr.height tt) : (rowOf tr tt q).i < 32 :=
  bitsVal_lt _ 0 5 (fun x hx => cv_bool (by simpa using ibBool hL hq x hx))

theorem j_eq {q : Nat} (hq : q < tr.height tt) (ha : tr.cell tt q act = 1) :
    Fp.ofNat (rowOf tr tt q).j = Fp.ofNat (32 * (rowOf tr tt q).l + (rowOf tr tt q).i) := by
  have := hL.constr q hq (.mul (c act) (sub (c j) (.add (smul 32 (c l)) RidV3.iE))) (by
    unfold RidV3.table RidV3.constraints; simp)
  simp only [eval_mul, eval_c, eval_sub, eval_add, eval_smul, ha, iE_eval hL hq, natCast_eq] at this
  rw [← ofNat_add', ← ofNat_mul']
  simp only [rowOf, cv, Fp.ofNat_toNat] at this ⊢
  grind

theorem rowT {q : Nat} (hq : q < tr.height tt) (bb : Nat) (sd : Bool) :
    rowTraffic RidV3.interactions tr tt q pub bb sd =
      if isA tr tt q then
        (if sd then ridSends [rowOf tr tt q] bb else ridRecvs [rowOf tr tt q] bb).map Msg.toFp
      else [] := by
  unfold rowTraffic RidV3.interactions
  simp only [List.flatMap_cons, List.flatMap_nil, Dsl.send, Dsl.recv, Interaction.multNat,
    Interaction.multNat.go, Interaction.msgVal, List.map_cons, List.map_nil, List.append_nil]
  by_cases ha : tr.cell tt q act = 1
  · have hi := iE_eval hL hq
    simp only [eval_c, ha, ite_true, isA, decide_true]
    rcases (show bb = 69 ∨ bb = 8 ∨ (bb ≠ 69 ∧ bb ≠ 8) by omega) with
      rfl | rfl | ⟨h1, h2⟩ <;>
      (try have h1' : 69 ≠ bb := Ne.symm h1) <;> (try have h2' : 8 ≠ bb := Ne.symm h2) <;>
      cases sd <;>
      simp only [ridSends, ridRecvs, B_PRID, B_RIDS, List.map_cons, List.map_nil, Msg.toFp,
        eval_c, eval_k, eval_add, ite_true, ite_false, decide_true, Nat.reduceEqDiff, Nat.pow_zero,
        Nat.add_zero, List.replicate_one, and_true, and_false, true_and, false_and,
        Bool.true_eq_false, Bool.false_eq_true, rowOf, cv, Fp.ofNat_toNat, natCast_eq, ← ofNat_add', List.append_nil, List.nil_append, *]
  · simp [eval_c, ha, isA]

end

theorem ridSends_flat (es : List RidE) (b : Nat) :
    ridSends es b = es.flatMap fun e => ridSends [e] b := by
  unfold ridSends; split <;> simp [map_eq_flatMap]

theorem ridRecvs_flat (es : List RidE) (b : Nat) :
    ridRecvs es b = es.flatMap fun e => ridRecvs [e] b := by
  unfold ridRecvs; split <;> simp [map_eq_flatMap]

end ZkFormal.NearV3.D1.RidProof

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RidProof

/-- **The `ridV3` view.** -/
theorem rid_view : RidViewStmt := by
  intro tr pub tt hL
  let rows := (List.range (tr.height tt)).filter (isA tr tt)
  have hall : ∀ b sd, (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic RidV3.interactions tr tt q pub b sd) =
      (if sd then ridSends (rows.map (rowOf tr tt)) b
       else ridRecvs (rows.map (rowOf tr tt)) b).map Msg.toFp := by
    intro b sd
    rw [flatMap_congr' (G := fun q => if isA tr tt q then
        (if sd then ridSends [rowOf tr tt q] b else ridRecvs [rowOf tr tt q] b).map Msg.toFp
      else []) (fun q hq => rowT hL (List.mem_range.1 hq) b sd)]
    rw [KibProof.flatMap_if]
    cases sd
    · simp only [Bool.false_eq_true, ite_false]
      rw [ridRecvs_flat, List.map_flatMap, List.flatMap_map]
    · simp only [ite_true]
      rw [ridSends_flat, List.map_flatMap, List.flatMap_map]
  refine ⟨rows.map (rowOf tr tt), ⟨?_, ?_, ?_⟩, fun b m => ⟨?_, ?_⟩⟩
  · intro e he
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 he
    obtain ⟨hq, ha⟩ := List.mem_filter.1 hq
    have hq := List.mem_range.1 hq
    exact ⟨i_lt hL hq, j_eq hL hq (by simpa [isA] using ha)⟩
  · intro e he
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 he
    exact ⟨cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _⟩
  · rw [List.length_map]
    refine Nat.le_trans (List.length_filter_le _ _) ?_
    rw [List.length_range]
    unfold Trace.height
    exact Nat.pow_le_pow_right (by omega) hL.log_le
  · simp only [ridTraffic]; rw [tableBusCount_eq, hall]; rfl
  · simp only [ridTraffic]; rw [tableBusCount_eq, hall]; rfl

end ZkFormal.NearV3.D1
