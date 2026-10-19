import WasmBase.Main.Rows
/-!
# WasmBase.Main.Exec — from `Holds` to the abstract execution theorem

Assembles the per-chip row facts (`ChipFacts`) into the hypotheses of `exec_of_rows`: the bus
messages of the whole trace decompose into the boundary's messages and those of the active
instruction rows; the STATE and CH buses are exact permutations (`msgs_perm`, bit counts); the
lookups hold (`looks_of`).
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

/-- The instruction table at index `t ∈ [1, 9]`. -/
def chipT : Nat → Table
  | 1 => Add.table | 2 => Bit.table | 3 => Mul.table | 4 => Shift.table | 5 => Cmp.table
  | 6 => Const.table | 7 => Stack.table | 8 => Ctrl.table | 9 => Local.table | _ => default

theorem chipT_eq (nloc ncode t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 9) :
    (wasmBaseAir nloc ncode).tables[t]'(by simp [air_len]; omega) = chipT t := by
  rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Decidable shape facts of every instruction chip: one STATE receive (`inters[0]`), one STATE
send (`inters[1]`) with the same count. -/
theorem chip_state (t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 9) :
    (chipT t).inters.filter (fun i => i.bus = busState ∧ i.send = false) = [(chipT t).inters.getD 0 default] ∧
    (chipT t).inters.filter (fun i => i.bus = busState ∧ i.send = true) = [(chipT t).inters.getD 1 default] ∧
    ((chipT t).inters.getD 1 default).count = ((chipT t).inters.getD 0 default).count := by
  rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- What each instruction chip provides (proven per chip in `WasmBase.Main.Row*`). -/
structure ChipFacts (X : Ctx) (nloc ncode : Nat) (pub : List F) (tr : Trace) : Prop where
  counts : ∀ t, 1 ≤ t → t ≤ 9 → ∀ r, r < tr.height t → ∀ i ∈ (chipT t).inters,
    (i.count.eval (tr.row pub t r)).toNat ≤ 1
  inactive : ∀ t, 1 ≤ t → t ≤ 9 → ∀ r, r < tr.height t → ¬ rowAct (chipT t) tr pub t r →
    ∀ i ∈ (chipT t).inters, (i.count.eval (tr.row pub t r)).toNat ≠ 1
  rows : Looks nloc ncode pub tr → PubOK X nloc ncode pub → ∀ t, 1 ≤ t → t ≤ 9 → ∀ r, r < tr.height t →
    rowAct (chipT t) tr pub t r →
    RowFacts X (rowIn (chipT t) tr pub t r) (rowOut (chipT t) tr pub t r) (rowCons (chipT t) tr pub t r)
      (rowProd (chipT t) tr pub t r)

/-! ## Count bits of the whole trace -/

theorem first_le (tr : Trace) (pub : List F) (t r : Nat) : (Expr.first.eval (tr.row pub t r)).toNat ≤ 1 := by
  simp only [Expr.eval, Trace.row]
  by_cases h : (r == 0) = true <;> simp only [h, ite_true, ite_false, Bool.false_eq_true] <;> decide

theorem occ_bits {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (hpub : PubOK X nloc ncode pub) (CF : ChipFacts X nloc ncode pub tr) :
    ∀ o ∈ occs (wasmBaseAir nloc ncode) tr pub, (o.2.1 = true ∨ o.1 = busState ∨ o.1 = busStk) → o.2.2.2 ≤ 1 := by
  intro o ho hk
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := occ_table ho
  simp only at hk ⊢
  rcases table_class nloc ncode t ht with ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨h1, h9, -⟩
  · rw [hT] at hi
    simp only [Boundary.table, Boundary.inters, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
      List.mem_flatMap, List.mem_map, List.mem_range] at hi
    rcases hi with ((rfl | rfl | rfl) | ⟨j, _, rfl | rfl⟩) | ⟨j, _, rfl⟩
    · exact first_le tr pub 0 r
    · exact first_le tr pub 0 r
    · -- the result receive: count `first · nres` with `nres = arity ≤ 1`
      have har := X.facts.results
      have hn := hpub.nres
      simp only [Boundary.pubNres] at hn
      simp only [stkRecv, chRecv, Expr.eval, pv, Trace.row, Boundary.pubNres, hn, X.facts.arity]
      by_cases h : (r == 0) = true
      · simp only [h, ite_true]
        rw [show (1 : F) * ((X.pf.type.results.size : Nat) : F) = ((X.pf.type.results.size : Nat) : F) by grind,
          Fp.toNat_cast_of_lt (by have := P_val; omega)]; omega
      · simp only [h, ite_false, Bool.false_eq_true]
        rw [show (0 : F) * ((X.pf.type.results.size : Nat) : F) = ((0 : Nat) : F) by grind]; decide
    · exact first_le tr pub 0 r
    · exact first_le tr pub 0 r
    · simp [busFetch, busState, busStk] at hk
  · rw [hT] at hi
    simp only [Range16.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
    subst hi; simp [busR16, busState, busStk] at hk
  · rw [hT] at hi
    simp only [Byte.table, Byte.inters, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> simp [busByte, busState, busStk] at hk
  · have := chipT_eq nloc ncode t h1 h9
    rw [this] at hi
    exact CF.counts t h1 h9 r hr i hi

/-! ## Bus messages of the trace, by row -/

instance (T : Table) (tr : Trace) (pub : List F) (t r : Nat) : Decidable (rowAct T tr pub t r) := by
  unfold rowAct; infer_instance

theorem flatMap_ite_single {α β : Type} (l : List α) (p : α → Prop) [DecidablePred p] (f : α → β) :
    (l.flatMap fun r => if p r then [f r] else []) = (l.filter fun r => decide (p r)).map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a
    · simp [h, ih]
    · simp [h, ih]

theorem air_flatMap {α : Type} (nloc ncode : Nat) (G : Table → Nat → List α) :
    ((wasmBaseAir nloc ncode).tables.zipIdx.flatMap fun x => G x.1 x.2) =
      G (Boundary.table nloc ncode) 0 ++ (G (chipT 1) 1 ++ (G (chipT 2) 2 ++ (G (chipT 3) 3 ++ (G (chipT 4) 4 ++
        (G (chipT 5) 5 ++ (G (chipT 6) 6 ++ (G (chipT 7) 7 ++ (G (chipT 8) 8 ++ (G (chipT 9) 9 ++
        (G Range16.table 10 ++ G Byte.table 11)))))))))) := by
  simp [wasmBaseAir, List.zipIdx_cons, chipT]

theorem chip_state_true {pub : List F} {tr : Trace} (t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 9)
    (r : Nat) : rowMsgs (chipT t) tr pub t r busState true =
      if rowAct (chipT t) tr pub t r then [rowOut (chipT t) tr pub t r] else [] := by
  rw [rowMsgs_eq, (chip_state t h1 h9).2.1]
  simp only [List.filterMap_cons, List.filterMap_nil]
  rw [(chip_state t h1 h9).2.2]
  unfold rowAct rowOut
  split <;> simp_all

theorem chip_state_false {pub : List F} {tr : Trace} (t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 9)
    (r : Nat) : rowMsgs (chipT t) tr pub t r busState false =
      if rowAct (chipT t) tr pub t r then [rowIn (chipT t) tr pub t r] else [] := by
  rw [rowMsgs_eq, (chip_state t h1 h9).1]
  simp only [List.filterMap_cons, List.filterMap_nil]
  unfold rowAct rowIn
  split <;> simp_all

theorem chip_ch_inactive {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (CF : ChipFacts X nloc ncode pub tr) (t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 9) (r : Nat) (hr : r < tr.height t)
    (hna : ¬ rowAct (chipT t) tr pub t r) (b : Nat) (s : Bool) : rowMsgs (chipT t) tr pub t r b s = [] := by
  rw [rowMsgs_eq, List.filterMap_eq_nil_iff]
  intro i hi
  rw [List.mem_filter] at hi
  simp [CF.inactive t h1 h9 r hr hna i hi.1]

/-! ## The boundary's messages -/

theorem flatMap_single {α β : Type} (f : α → β) (l : List α) : (l.flatMap fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem bnd_fetchPart (nloc ncode b : Nat) (s : Bool) (hb : b ≠ busFetch) :
    ((List.range ncode).map fun j => (⟨busFetch, false, .first * v (Boundary.mult nloc j),
      (List.range Boundary.recWidth).map fun k => pv (Boundary.pubRec nloc + Boundary.recWidth * j + k)⟩ : Inter)).filter
      (fun i => i.bus = b ∧ i.send = s) = [] := by
  rw [List.filter_eq_nil_iff]
  intro i hi
  simp only [List.mem_map] at hi
  obtain ⟨j, _, rfl⟩ := hi
  simp only [decide_eq_true_eq, not_and]
  intro h; exact absurd h.symm hb

theorem bnd_filters (nloc ncode : Nat) :
    (Boundary.inters nloc ncode).filter (fun i => i.bus = busState ∧ i.send = true) = [stateOut 0 1 0 0 .first] ∧
    (Boundary.inters nloc ncode).filter (fun i => i.bus = busState ∧ i.send = false) =
      [⟨busState, false, .first, [v Boundary.pcf, pv Boundary.pubN, pv Boundary.pubS, 1]⟩] ∧
    (Boundary.inters nloc ncode).filter (fun i => i.bus = busStk ∧ i.send = true) =
      (List.range nloc).map (fun j => chSend 1 (Expr.c j) (pv (Boundary.pubLoc + j)) zeros4 0 .first) ∧
    (Boundary.inters nloc ncode).filter (fun i => i.bus = busStk ∧ i.send = false) =
      stkRecv 0 (pv Boundary.pubTag) ((List.range 4).map fun i => pv (Boundary.pubR + i)) (v Boundary.tpr)
        (.first * pv Boundary.pubNres) ::
      (List.range nloc).map (fun j => chRecv 1 (Expr.c j) (v (Boundary.fin j))
        ((List.range 4).map fun i => v (Boundary.fin j + 1 + i)) (v (Boundary.fin j + 5)) .first) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> unfold Boundary.inters <;>
    rw [List.filter_append, List.filter_append, bnd_fetchPart nloc ncode _ _ (by decide), List.append_nil,
      List.filter_flatMap] <;>
    simp [stateOut, chSend, chRecv, stkRecv, busState, busStk, flatMap_single]

def initRaw (nloc : Nat) (pub : List F) : List (List F) :=
  (List.range nloc).map fun j => [((1 : Nat) : F), ((j : Nat) : F), pub.getD (Boundary.pubLoc + j) 0,
    ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F)]

def resRaw (pub : List F) (tr : Trace) : List F :=
  [((0 : Nat) : F), ((0 : Nat) : F), pub.getD Boundary.pubTag 0, pub.getD (Boundary.pubR + 0) 0,
    pub.getD (Boundary.pubR + 1) 0, pub.getD (Boundary.pubR + 2) 0, pub.getD (Boundary.pubR + 3) 0,
    tr.cell 0 0 Boundary.tpr]

def finRaw (nloc : Nat) (tr : Trace) : List (List F) :=
  (List.range nloc).map fun j => [((1 : Nat) : F), ((j : Nat) : F), tr.cell 0 0 (Boundary.fin j),
    tr.cell 0 0 (Boundary.fin j + 1 + 0), tr.cell 0 0 (Boundary.fin j + 1 + 1), tr.cell 0 0 (Boundary.fin j + 1 + 2),
    tr.cell 0 0 (Boundary.fin j + 1 + 3), tr.cell 0 0 (Boundary.fin j + 5)]

theorem first_eval (tr : Trace) (pub : List F) (t r : Nat) :
    (Expr.first.eval (tr.row pub t r)).toNat = 1 ↔ r = 0 := by
  simp only [Expr.eval, Trace.row]
  by_cases h : r = 0
  · subst h; simp; rfl
  · have : (r == 0) = false := by simp [h]
    simp only [this, Bool.false_eq_true, ite_false, h, iff_false]; decide

theorem filterMap_some_of {α β : Type} (g : α → Option β) (f : α → β) (l : List α)
    (h : ∀ x ∈ l, g x = some (f x)) : l.filterMap g = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filterMap_cons, h a List.mem_cons_self, List.map_cons, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem filterMap_none_of {α β : Type} (g : α → Option β) (l : List α)
    (h : ∀ x ∈ l, g x = none) : l.filterMap g = [] := by
  rw [List.filterMap_eq_nil_iff]; exact h

theorem bnd_msgs {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace} (hpub : PubOK X nloc ncode pub) (r : Nat) :
    rowMsgs (Boundary.table nloc ncode) tr pub 0 r busState true = (if r = 0 then [stMsg 0 1 0 0] else []) ∧
    rowMsgs (Boundary.table nloc ncode) tr pub 0 r busState false =
      (if r = 0 then [[tr.cell 0 0 Boundary.pcf, pub.getD Boundary.pubN 0, pub.getD Boundary.pubS 0, ((1 : Nat) : F)]]
       else []) ∧
    rowMsgs (Boundary.table nloc ncode) tr pub 0 r busStk true = (if r = 0 then initRaw nloc pub else []) ∧
    rowMsgs (Boundary.table nloc ncode) tr pub 0 r busStk false =
      (if r = 0 then (if X.ck.arity = 1 then [resRaw pub tr] else []) ++ finRaw nloc tr else []) := by
  obtain ⟨f1, f2, f3, f4⟩ := bnd_filters nloc ncode
  have hfe := first_eval tr pub 0 r
  have h0 : r = 0 → (Expr.first.eval (tr.row pub 0 r)).toNat = 1 := hfe.mpr
  have h1 : r ≠ 0 → ¬ (Expr.first.eval (tr.row pub 0 r)).toNat = 1 := fun h e => h (hfe.mp e)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [rowMsgs_eq] <;> simp only [Boundary.table]
  · rw [f1]; simp only [List.filterMap_cons, List.filterMap_nil, stateOut]
    by_cases h : r = 0
    · simp only [h0 h, ite_true, h]; rfl
    · simp only [h1 h, ite_false, h]
  · rw [f2]; simp only [List.filterMap_cons, List.filterMap_nil]
    by_cases h : r = 0
    · simp only [h0 h, ite_true, h]
      subst h; rfl
    · simp only [h1 h, ite_false, h]
  · rw [f3, List.filterMap_map]
    by_cases h : r = 0
    · simp only [h, ite_true, initRaw]
      apply filterMap_some_of
      intro j _
      subst h
      simp only [Function.comp, chSend, h0 rfl, ite_true]
      rfl
    · simp only [h, ite_false]
      apply filterMap_none_of
      intro j _
      simp only [Function.comp, chSend, h1 h, ite_false]
  · rw [f4, List.filterMap_cons, List.filterMap_map]
    have har := X.facts.results
    have harity := X.facts.arity
    by_cases h : r = 0
    · subst h
      have hres : ((Expr.first * pv Boundary.pubNres).eval (tr.row pub 0 0)).toNat = X.ck.arity := by
        simp only [Expr.eval_mul', Expr.eval_pub, pv, Trace.row]
        rw [show pub.getD Boundary.pubNres 0 = ((X.ck.arity : Nat) : F) from hpub.nres]
        simp only [Expr.eval, beq_self_eq_true, ite_true]
        rw [show (1 : F) * ((X.ck.arity : Nat) : F) = ((X.ck.arity : Nat) : F) by grind,
          Fp.toNat_cast_of_lt (by have := P_val; omega)]
      have hrest : (List.range nloc).filterMap (((fun i => if (i.count.eval (tr.row pub 0 0)).toNat = 1 then
          some (i.msg.map (·.eval (tr.row pub 0 0))) else none) ∘ fun j => chRecv 1 (Expr.c j) (v (Boundary.fin j))
          ((List.range 4).map fun i => v (Boundary.fin j + 1 + i)) (v (Boundary.fin j + 5)) .first)) = finRaw nloc tr := by
        apply filterMap_some_of
        intro j _
        simp only [Function.comp, chRecv, h0 rfl, ite_true]
        rfl
      rw [hrest]
      simp only [ite_true, stkRecv, chRecv, hres]
      by_cases ha : X.ck.arity = 1
      · simp only [ha, ite_true, List.cons_append, List.nil_append]; rfl
      · simp only [ha, ite_false, List.nil_append]
    · simp only [h, ite_false]
      have hres : ¬ ((Expr.first * pv Boundary.pubNres).eval (tr.row pub 0 r)).toNat = 1 := by
        simp only [Expr.eval_mul', Expr.eval]
        have : (r == 0) = false := by simp [h]
        simp only [Trace.row, this, Bool.false_eq_true, ite_false]
        have z : ∀ x : F, (0 : F) * x = ((0 : Nat) : F) := fun x => by grind
        rw [z]; decide
      simp only [stkRecv, chRecv, hres, ite_false]
      apply filterMap_none_of
      intro j _
      simp only [Function.comp, chRecv, h1 h, ite_false]

/-! ## The whole trace's STATE and CH messages -/

def actRows (tr : Trace) (pub : List F) (t : Nat) : List Nat :=
  (List.range (tr.height t)).filter fun r => decide (rowAct (chipT t) tr pub t r)

/-- The active instruction rows `(table, row)`. -/
def actList (tr : Trace) (pub : List F) : List (Nat × Nat) :=
  (List.range 9).flatMap fun k => (actRows tr pub (k + 1)).map fun r => (k + 1, r)

theorem flatMap_range_first {α : Type} (h : Nat) (hh : 1 ≤ h) (L : List α) :
    ((List.range h).flatMap fun r => if r = 0 then L else []) = L := by
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  simp

theorem flatMap_filter_of_nil {α β : Type} (l : List α) (p : α → Prop) [DecidablePred p] (f : α → List β)
    (h : ∀ x ∈ l, ¬ p x → f x = []) : l.flatMap f = (l.filter fun x => decide (p x)).flatMap f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    by_cases ha : p a
    · simp [ha, ih']
    · simp [ha, h a List.mem_cons_self ha, ih']

theorem fixed_nil (tr : Trace) (pub : List F) (t r : Nat) (b : Nat) (hb : b = busState ∨ b = busStk) (s : Bool) :
    rowMsgs Range16.table tr pub t r b s = [] ∧ rowMsgs Byte.table tr pub t r b s = [] := by
  constructor <;> rw [rowMsgs_eq] <;> rcases hb with rfl | rfl <;> cases s <;>
    simp [Range16.table, Byte.table, Byte.inters, busState, busStk, busR16, busByte]

theorem chip_part_true {pub : List F} {tr : Trace} (t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 9) :
    ((List.range (tr.height t)).flatMap fun r => rowMsgs (chipT t) tr pub t r busState true) =
      (actRows tr pub t).map (rowOut (chipT t) tr pub t) := by
  rw [show (fun r => rowMsgs (chipT t) tr pub t r busState true) =
    (fun r => if rowAct (chipT t) tr pub t r then [rowOut (chipT t) tr pub t r] else []) from
    funext (chip_state_true t h1 h9), flatMap_ite_single]
  rfl

theorem chip_part_false {pub : List F} {tr : Trace} (t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 9) :
    ((List.range (tr.height t)).flatMap fun r => rowMsgs (chipT t) tr pub t r busState false) =
      (actRows tr pub t).map (rowIn (chipT t) tr pub t) := by
  rw [show (fun r => rowMsgs (chipT t) tr pub t r busState false) =
    (fun r => if rowAct (chipT t) tr pub t r then [rowIn (chipT t) tr pub t r] else []) from
    funext (chip_state_false t h1 h9), flatMap_ite_single]
  rfl

theorem chip_part_ch {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace} (CF : ChipFacts X nloc ncode pub tr)
    (t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 9) (s : Bool) :
    ((List.range (tr.height t)).flatMap fun r => rowMsgs (chipT t) tr pub t r busStk s) =
      (actRows tr pub t).flatMap fun r => rowMsgs (chipT t) tr pub t r busStk s := by
  rw [actRows, ← flatMap_filter_of_nil]
  intro r hr hna
  exact chip_ch_inactive CF t h1 h9 r (List.mem_range.mp hr) hna busStk s

theorem actList_flatMap {β : Type} (tr : Trace) (pub : List F) (f : Nat × Nat → List β) :
    (actList tr pub).flatMap f =
      (actRows tr pub 1).flatMap (fun r => f (1, r)) ++ ((actRows tr pub 2).flatMap (fun r => f (2, r)) ++
      ((actRows tr pub 3).flatMap (fun r => f (3, r)) ++ ((actRows tr pub 4).flatMap (fun r => f (4, r)) ++
      ((actRows tr pub 5).flatMap (fun r => f (5, r)) ++ ((actRows tr pub 6).flatMap (fun r => f (6, r)) ++
      ((actRows tr pub 7).flatMap (fun r => f (7, r)) ++ ((actRows tr pub 8).flatMap (fun r => f (8, r)) ++
      (actRows tr pub 9).flatMap (fun r => f (9, r))))))))) := by
  simp [actList, List.flatMap_assoc, List.range, List.range.loop, List.flatMap_map]

theorem actList_map {β : Type} (tr : Trace) (pub : List F) (f : Nat × Nat → β) :
    (actList tr pub).map f =
      (actRows tr pub 1).map (fun r => f (1, r)) ++ ((actRows tr pub 2).map (fun r => f (2, r)) ++
      ((actRows tr pub 3).map (fun r => f (3, r)) ++ ((actRows tr pub 4).map (fun r => f (4, r)) ++
      ((actRows tr pub 5).map (fun r => f (5, r)) ++ ((actRows tr pub 6).map (fun r => f (6, r)) ++
      ((actRows tr pub 7).map (fun r => f (7, r)) ++ ((actRows tr pub 8).map (fun r => f (8, r)) ++
      (actRows tr pub 9).map (fun r => f (9, r))))))))) := by
  simp only [actList, List.map_flatMap, List.range, List.range.loop, List.map_map, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, Nat.reduceAdd, Nat.zero_add]
  simp only [List.map_append, List.map_map]; rfl

def part (T : Table) (tr : Trace) (pub : List F) (t b : Nat) (s : Bool) : List (List F) :=
  (List.range (tr.height t)).flatMap fun r => rowMsgs T tr pub t r b s

theorem msgs_air (nloc ncode : Nat) (tr : Trace) (pub : List F) (b : Nat) (s : Bool) :
    msgs (wasmBaseAir nloc ncode) tr pub b s =
      part (Boundary.table nloc ncode) tr pub 0 b s ++ (part (chipT 1) tr pub 1 b s ++ (part (chipT 2) tr pub 2 b s ++
      (part (chipT 3) tr pub 3 b s ++ (part (chipT 4) tr pub 4 b s ++ (part (chipT 5) tr pub 5 b s ++
      (part (chipT 6) tr pub 6 b s ++ (part (chipT 7) tr pub 7 b s ++ (part (chipT 8) tr pub 8 b s ++
      (part (chipT 9) tr pub 9 b s ++ (part Range16.table tr pub 10 b s ++ part Byte.table tr pub 11 b s)))))))))) := by
  rw [msgs_flatMap]
  simp only [wasmBaseAir, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Nat.reduceAdd]
  rfl

theorem part_fixed (tr : Trace) (pub : List F) (b : Nat) (hb : b = busState ∨ b = busStk) (s : Bool) :
    part Range16.table tr pub 10 b s = [] ∧ part Byte.table tr pub 11 b s = [] := by
  constructor <;> (unfold part; rw [List.flatMap_eq_nil_iff]; intro r _)
  · exact (fixed_nil tr pub 10 r b hb s).1
  · exact (fixed_nil tr pub 11 r b hb s).2

theorem msgs_state {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (hpub : PubOK X nloc ncode pub) :
    msgs (wasmBaseAir nloc ncode) tr pub busState true =
      stMsg 0 1 0 0 :: (actList tr pub).map (fun ρ => rowOut (chipT ρ.1) tr pub ρ.1 ρ.2) ∧
    msgs (wasmBaseAir nloc ncode) tr pub busState false =
      [tr.cell 0 0 Boundary.pcf, pub.getD Boundary.pubN 0, pub.getD Boundary.pubS 0, ((1 : Nat) : F)] ::
        (actList tr pub).map (fun ρ => rowIn (chipT ρ.1) tr pub ρ.1 ρ.2) := by
  have h0 : 1 ≤ tr.height 0 := by have := H.heightPos 0 (by simp [air_len]); omega
  obtain ⟨n1, n2⟩ := part_fixed tr pub busState (Or.inl rfl) true
  obtain ⟨n3, n4⟩ := part_fixed tr pub busState (Or.inl rfl) false
  constructor
  · rw [msgs_air, n1, n2, actList_map]
    have hb : part (Boundary.table nloc ncode) tr pub 0 busState true = [stMsg 0 1 0 0] := by
      unfold part
      rw [show (fun r => rowMsgs (Boundary.table nloc ncode) tr pub 0 r busState true) =
        (fun r => if r = 0 then [stMsg 0 1 0 0] else []) from funext fun r => (bnd_msgs hpub r).1]
      exact flatMap_range_first _ h0 _
    rw [hb]
    simp only [part, chip_part_true 1 (by omega) (by omega), chip_part_true 2 (by omega) (by omega),
      chip_part_true 3 (by omega) (by omega), chip_part_true 4 (by omega) (by omega),
      chip_part_true 5 (by omega) (by omega), chip_part_true 6 (by omega) (by omega),
      chip_part_true 7 (by omega) (by omega), chip_part_true 8 (by omega) (by omega),
      chip_part_true 9 (by omega) (by omega), List.append_nil, List.cons_append, List.nil_append]
  · rw [msgs_air, n3, n4, actList_map]
    have hb : part (Boundary.table nloc ncode) tr pub 0 busState false =
        [[tr.cell 0 0 Boundary.pcf, pub.getD Boundary.pubN 0, pub.getD Boundary.pubS 0, ((1 : Nat) : F)]] := by
      unfold part
      rw [show (fun r => rowMsgs (Boundary.table nloc ncode) tr pub 0 r busState false) =
        (fun r => if r = 0 then [[tr.cell 0 0 Boundary.pcf, pub.getD Boundary.pubN 0, pub.getD Boundary.pubS 0,
          ((1 : Nat) : F)]] else []) from funext fun r => (bnd_msgs hpub r).2.1]
      exact flatMap_range_first _ h0 _
    rw [hb]
    simp only [part, chip_part_false 1 (by omega) (by omega), chip_part_false 2 (by omega) (by omega),
      chip_part_false 3 (by omega) (by omega), chip_part_false 4 (by omega) (by omega),
      chip_part_false 5 (by omega) (by omega), chip_part_false 6 (by omega) (by omega),
      chip_part_false 7 (by omega) (by omega), chip_part_false 8 (by omega) (by omega),
      chip_part_false 9 (by omega) (by omega), List.append_nil, List.cons_append, List.nil_append]

theorem msgs_ch {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (hpub : PubOK X nloc ncode pub) (CF : ChipFacts X nloc ncode pub tr) :
    msgs (wasmBaseAir nloc ncode) tr pub busStk true =
      initRaw nloc pub ++ (actList tr pub).flatMap (fun ρ => rowMsgs (chipT ρ.1) tr pub ρ.1 ρ.2 busStk true) ∧
    msgs (wasmBaseAir nloc ncode) tr pub busStk false =
      ((if X.ck.arity = 1 then [resRaw pub tr] else []) ++ finRaw nloc tr) ++
        (actList tr pub).flatMap (fun ρ => rowMsgs (chipT ρ.1) tr pub ρ.1 ρ.2 busStk false) := by
  have h0 : 1 ≤ tr.height 0 := by have := H.heightPos 0 (by simp [air_len]); omega
  obtain ⟨n1, n2⟩ := part_fixed tr pub busStk (Or.inr rfl) true
  obtain ⟨n3, n4⟩ := part_fixed tr pub busStk (Or.inr rfl) false
  constructor
  · rw [msgs_air, n1, n2, actList_flatMap]
    have hb : part (Boundary.table nloc ncode) tr pub 0 busStk true = initRaw nloc pub := by
      unfold part
      rw [show (fun r => rowMsgs (Boundary.table nloc ncode) tr pub 0 r busStk true) =
        (fun r => if r = 0 then initRaw nloc pub else []) from funext fun r => (bnd_msgs hpub r).2.2.1]
      exact flatMap_range_first _ h0 _
    rw [hb]
    simp only [part, chip_part_ch CF 1 (by omega) (by omega), chip_part_ch CF 2 (by omega) (by omega),
      chip_part_ch CF 3 (by omega) (by omega), chip_part_ch CF 4 (by omega) (by omega),
      chip_part_ch CF 5 (by omega) (by omega), chip_part_ch CF 6 (by omega) (by omega),
      chip_part_ch CF 7 (by omega) (by omega), chip_part_ch CF 8 (by omega) (by omega),
      chip_part_ch CF 9 (by omega) (by omega), List.append_nil]
  · rw [msgs_air, n3, n4, actList_flatMap]
    have hb : part (Boundary.table nloc ncode) tr pub 0 busStk false =
        (if X.ck.arity = 1 then [resRaw pub tr] else []) ++ finRaw nloc tr := by
      unfold part
      rw [show (fun r => rowMsgs (Boundary.table nloc ncode) tr pub 0 r busStk false) =
        (fun r => if r = 0 then (if X.ck.arity = 1 then [resRaw pub tr] else []) ++ finRaw nloc tr else []) from
        funext fun r => (bnd_msgs hpub r).2.2.2]
      exact flatMap_range_first _ h0 _
    rw [hb]
    simp only [part, chip_part_ch CF 1 (by omega) (by omega), chip_part_ch CF 2 (by omega) (by omega),
      chip_part_ch CF 3 (by omega) (by omega), chip_part_ch CF 4 (by omega) (by omega),
      chip_part_ch CF 5 (by omega) (by omega), chip_part_ch CF 6 (by omega) (by omega),
      chip_part_ch CF 7 (by omega) (by omega), chip_part_ch CF 8 (by omega) (by omega),
      chip_part_ch CF 9 (by omega) (by omega), List.append_nil]

end WasmBase
