import WasmBase.Extract.Row
/-!
# WasmBase.Extract.Occ — bus messages of a trace, row by row
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
set_option linter.unusedSimpArgs false

/-- The occurrences of one row of table `T` (index `t`). -/
def rowOccs (T : Table) (tr : Trace) (pub : List F) (t r : Nat) : List Occ :=
  T.inters.map fun i => (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)), (i.count.eval (tr.row pub t r)).toNat)

/-- The count-1 messages of one row on bus `b` in direction `s`. -/
def rowMsgs (T : Table) (tr : Trace) (pub : List F) (t r b : Nat) (s : Bool) : List (List F) :=
  ((rowOccs T tr pub t r).filter fun o => o.1 = b ∧ o.2.1 = s ∧ o.2.2.2 = 1).map (·.2.2.1)

theorem msgs_flatMap (A : Air) (tr : Trace) (pub : List F) (b : Nat) (s : Bool) :
    msgs A tr pub b s = (A.tables.zipIdx).flatMap fun (T, t) =>
      (List.range (tr.height t)).flatMap fun r => rowMsgs T tr pub t r b s := by
  unfold msgs occs rowMsgs rowOccs
  rw [List.filter_flatMap, List.map_flatMap]
  congr 1; funext x; obtain ⟨T, t⟩ := x
  simp only
  rw [List.filter_flatMap, List.map_flatMap]

/-- A row's messages when exactly one interaction of the row is on `(b, s)`. -/
theorem rowMsgs_single (T : Table) (tr : Trace) (pub : List F) (t r b : Nat) (s : Bool) (i : Inter)
    (hi : T.inters.filter (fun j => j.bus = b ∧ j.send = s) = [i]) :
    rowMsgs T tr pub t r b s =
      if (i.count.eval (tr.row pub t r)).toNat = 1 then [i.msg.map (·.eval (tr.row pub t r))] else [] := by
  unfold rowMsgs rowOccs
  rw [List.filter_map]
  have : (T.inters.filter ((fun o : Occ => decide (o.1 = b ∧ o.2.1 = s ∧ o.2.2.2 = 1)) ∘
      fun i => (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)), (i.count.eval (tr.row pub t r)).toNat))) =
      (T.inters.filter (fun j => j.bus = b ∧ j.send = s)).filter
        (fun j => (j.count.eval (tr.row pub t r)).toNat = 1) := by
    rw [List.filter_filter]; congr 1; funext j; simp only [Function.comp]; by_cases h1 : j.bus = b <;> by_cases h2 : j.send = s <;> simp [h1, h2]
  rw [this, hi]
  by_cases h : (i.count.eval (tr.row pub t r)).toNat = 1 <;> simp [h]

theorem rowMsgs_none (T : Table) (tr : Trace) (pub : List F) (t r b : Nat) (s : Bool)
    (hi : T.inters.filter (fun j => j.bus = b ∧ j.send = s) = []) :
    rowMsgs T tr pub t r b s = [] := by
  unfold rowMsgs rowOccs
  rw [List.filter_map]
  have : (T.inters.filter ((fun o : Occ => decide (o.1 = b ∧ o.2.1 = s ∧ o.2.2.2 = 1)) ∘
      fun i => (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)), (i.count.eval (tr.row pub t r)).toNat))) =
      (T.inters.filter (fun j => j.bus = b ∧ j.send = s)).filter
        (fun j => (j.count.eval (tr.row pub t r)).toNat = 1) := by
    rw [List.filter_filter]; congr 1; funext j; simp only [Function.comp]; by_cases h1 : j.bus = b <;> by_cases h2 : j.send = s <;> simp [h1, h2]
  rw [this, hi]; rfl

end WasmBase
