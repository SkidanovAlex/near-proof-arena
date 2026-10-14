import ZkFormal.NearV3.D1.Extract.KibProof

/-!
# `ZkFormal.NearV3.D1.Extract.PlfProof` — the `plfV3` view (`PlfViewStmt`, `plf_view`)

Lane `v3-d1-phase2` (milestone V1).  One `PlfE` per active row (in row order): the public outcome
leaf `(pos, d[32])`.  Traffic: receives `PLEAF (pos, d)`, sends `MPOS (0, pos, PLF(pos), 68)` and
`DIGEST (PLF(pos), 68, d)` with `PLF(pos) = K_PLF + 16·pos` (as a natural).
-/

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

structure PlfE where
  pos : Nat
  d : List Nat
  deriving Repr, Inhabited

/-- The leaf message id `K_PLF + 16·pos`. -/
def PlfE.mid (e : PlfE) : Nat := K_PLF + 16 * e.pos

structure PlfWf (es : List PlfE) : Prop where
  len : ∀ e ∈ es, e.d.length = 32
  canon : ∀ e ∈ es, e.pos < P ∧ ∀ x ∈ e.d, x < P
  rows : es.length ≤ 2 ^ PlfV3.maxLog

def plfSends (es : List PlfE) (b : Nat) : List Msg :=
  if b = B_MPOS then es.map fun e => [0, e.pos, e.mid, 68]
  else if b = B_DIGEST then es.map fun e => [e.mid, 68] ++ e.d
  else []

def plfRecvs (es : List PlfE) (b : Nat) : List Msg :=
  if b = B_PLEAF then es.map fun e => e.pos :: e.d else []

def plfTraffic (es : List PlfE) : Traffic := ⟨plfSends es, plfRecvs es⟩

/-- **The `plfV3` view statement.** -/
def PlfViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal PlfV3.table tr t pub →
    ∃ es, PlfWf es ∧ TableTraffic PlfV3.interactions tr t pub (plfTraffic es)

end ZkFormal.NearV3.D1

namespace ZkFormal.NearV3.D1.PlfProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.PlfV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

def rowOf (tr : Trace Fp) (tt q : Nat) : PlfE :=
  ⟨cv tr tt q pos, (List.range 32).map fun i => cv tr tt q (d i)⟩

def isA (tr : Trace Fp) (tt q : Nat) : Bool := decide (tr.cell tt q act = 1)

theorem mid_toFp (q : Nat) :
    Fp.ofNat (rowOf tr tt q).mid = Fp.ofNat K_PLF + Fp.ofNat 16 * tr.cell tt q pos := by
  simp only [PlfE.mid, rowOf, cv]
  rw [← ofNat_add', ← ofNat_mul', Fp.ofNat_toNat]

theorem d_toFp (q : Nat) :
    ((rowOf tr tt q).d).map Fp.ofNat = (List.range 32).map fun i => tr.cell tt q (d i) := by
  simp only [rowOf, List.map_map, Function.comp_def, cv, Fp.ofNat_toNat]

theorem pos_toFp (q : Nat) : Fp.ofNat (rowOf tr tt q).pos = tr.cell tt q pos := by
  simp only [rowOf, cv, Fp.ofNat_toNat]

theorem rowT (q bb : Nat) (sd : Bool) :
    rowTraffic PlfV3.interactions tr tt q pub bb sd =
      if isA tr tt q then
        (if sd then plfSends [rowOf tr tt q] bb else plfRecvs [rowOf tr tt q] bb).map Msg.toFp
      else [] := by
  unfold rowTraffic PlfV3.interactions
  simp only [List.flatMap_cons, List.flatMap_nil, Dsl.send, Dsl.recv, Interaction.multNat,
    Interaction.multNat.go, Interaction.msgVal, List.map_cons, List.map_nil, List.append_nil]
  by_cases ha : tr.cell tt q act = 1
  · simp only [eval_c, ha, ite_true, isA, decide_true]
    rcases (show bb = 68 ∨ bb = 9 ∨ bb = 1 ∨ (bb ≠ 68 ∧ bb ≠ 9 ∧ bb ≠ 1) by omega) with
      rfl | rfl | rfl | ⟨h1, h2, h3⟩ <;>
      (try have h1' : 68 ≠ bb := Ne.symm h1) <;> (try have h2' : 9 ≠ bb := Ne.symm h2) <;>
      (try have h3' : 1 ≠ bb := Ne.symm h3) <;> cases sd <;>
      simp only [plfSends, plfRecvs, B_PLEAF, B_MPOS, B_DIGEST, List.map_cons,
        List.map_nil, Msg.toFp, List.cons_append, List.nil_append, mid_toFp,
        d_toFp, pos_toFp, eval_c, eval_k, eval_mid, PlfV3.idE, List.append_nil,
        and_true, and_false, true_and, false_and, Bool.true_eq_false,
        Bool.false_eq_true, ite_true, ite_false, List.replicate_one, decide_true,
        Nat.reduceEqDiff, Nat.pow_zero, Nat.add_zero, List.map_map,
        Function.comp_def, natCast_eq, *]
  · simp [eval_c, ha, isA]

theorem plfSends_flat (es : List PlfE) (b : Nat) :
    plfSends es b = es.flatMap fun e => plfSends [e] b := by
  unfold plfSends; repeat' split
  all_goals simp [map_eq_flatMap]

theorem plfRecvs_flat (es : List PlfE) (b : Nat) :
    plfRecvs es b = es.flatMap fun e => plfRecvs [e] b := by
  unfold plfRecvs; split <;> simp [map_eq_flatMap]

end ZkFormal.NearV3.D1.PlfProof

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near PlfProof

/-- **The `plfV3` view.** -/
theorem plf_view : PlfViewStmt := by
  intro tr pub tt hL
  let rows := (List.range (tr.height tt)).filter (isA tr tt)
  have hall : ∀ b sd, (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic PlfV3.interactions tr tt q pub b sd) =
      (if sd then plfSends (rows.map (rowOf tr tt)) b
       else plfRecvs (rows.map (rowOf tr tt)) b).map Msg.toFp := by
    intro b sd
    simp only [rowT]
    rw [KibProof.flatMap_if]
    cases sd
    · simp only [Bool.false_eq_true, ite_false]
      rw [plfRecvs_flat, List.map_flatMap, List.flatMap_map]
    · simp only [ite_true]
      rw [plfSends_flat, List.map_flatMap, List.flatMap_map]
  refine ⟨rows.map (rowOf tr tt), ⟨?_, ?_, ?_⟩, fun b m => ⟨?_, ?_⟩⟩
  · intro e he
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 he
    simp [rowOf]
  · intro e he
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 he
    refine ⟨cv_lt _ _ _ _, fun x hx => ?_⟩
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact cv_lt _ _ _ _
  · rw [List.length_map]
    refine Nat.le_trans (List.length_filter_le _ _) ?_
    rw [List.length_range]
    unfold Trace.height
    exact Nat.pow_le_pow_right (by omega) hL.log_le
  · simp only [plfTraffic]; rw [tableBusCount_eq, hall]; rfl
  · simp only [plfTraffic]; rw [tableBusCount_eq, hall]; rfl

end ZkFormal.NearV3.D1
