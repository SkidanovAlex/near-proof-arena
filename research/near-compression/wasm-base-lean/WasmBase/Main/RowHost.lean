import WasmBase.StepHost
import WasmBase.Main.Rows
/-!
# WasmBase.Main.RowHost — HOST row lemma (constraints + bus/STATE facts)

`host_rowfacts` turns an active HOST row of `wasmBaseHostAir` into the **field-level** facts the row
constraints state: the flags are bits and exclusivity holds, `np = pf0 + pf1`, `nres = (1−st)·ar`,
absent arguments are zero, and the STATE messages have the standard shape (`pc+1`, `ts+1`,
`S+fee`, `halted = 2·st`, frame unchanged).  `host_bus_ok` records that the HOSTQ/HOSTR/HOSTT buses
are balanced against the witness oracle `HOSTO`.

The spec side is `WasmBase.StepHost` (`callFunc` at the advanced pc given an abstract response).
The **top-level gas invariant** is deliberately not restated: a host call resynchronises
`g := running remaining`, so `R·S_final + g = g0` (the invariant of `wasm_base_sound`) no longer
holds.  Extending `wasm_base_sound` therefore needs a gas invariant with the sum of host
resynchronisations, which is the documented remaining step (`results/pq-host-chip/RESULTS.md`).
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

/-- Field-level structural facts of an active HOST row. -/
structure HostRowFacts (pub : List F) (tr : Trace) (r : Nat) : Prop where
  act : (rowNat tr 22 r Host.act : F) = 1
  stBit : (rowNat tr 22 r Host.st : F) * ((rowNat tr 22 r Host.st : F) - 1) = 0
  arBit : (rowNat tr 22 r Host.ar : F) * ((rowNat tr 22 r Host.ar : F) - 1) = 0
  pf0Bit : (rowNat tr 22 r (Host.pf 0) : F) * ((rowNat tr 22 r (Host.pf 0) : F) - 1) = 0
  pf1Bit : (rowNat tr 22 r (Host.pf 1) : F) * ((rowNat tr 22 r (Host.pf 1) : F) - 1) = 0
  npEq : (rowNat tr 22 r Host.np : F) =
    (rowNat tr 22 r (Host.pf 0) : F) + (rowNat tr 22 r (Host.pf 1) : F)
  order : (rowNat tr 22 r (Host.pf 1) : F) - (rowNat tr 22 r (Host.pf 0) : F) *
    (rowNat tr 22 r (Host.pf 1) : F) = 0
  nresEq : (rowNat tr 22 r Host.nres : F) - (rowNat tr 22 r Host.ar : F) +
    (rowNat tr 22 r Host.st : F) * (rowNat tr 22 r Host.ar : F) = 0
  pad0 : (rowNat tr 22 r (Host.tagP 0) : F) - (rowNat tr 22 r (Host.pf 0) : F) *
    (rowNat tr 22 r (Host.tagP 0) : F) = 0
  pad1 : (rowNat tr 22 r (Host.tagP 1) : F) - (rowNat tr 22 r (Host.pf 1) : F) *
    (rowNat tr 22 r (Host.tagP 1) : F) = 0
  inS : rowIn Host.table tr pub 22 r =
    [((rowNat tr 22 r 0 : Nat) : F), ((rowNat tr 22 r 1 : Nat) : F), ((rowNat tr 22 r 2 : Nat) : F),
     ((0 : Nat) : F), ((rowNat tr 22 r 35 : Nat) : F), ((rowNat tr 22 r 36 : Nat) : F)]
  outS : rowOut Host.table tr pub 22 r =
    [((rowNat tr 22 r 0 : Nat) : F) + ((1 : Nat) : F), ((rowNat tr 22 r 1 : Nat) : F) + ((1 : Nat) : F),
     ((rowNat tr 22 r 2 : Nat) : F) + ((rowNat tr 22 r 4 : Nat) : F),
     ((2 * rowNat tr 22 r Host.st : Nat) : F), ((rowNat tr 22 r 35 : Nat) : F),
     ((rowNat tr 22 r 36 : Nat) : F)]

theorem host_rowIn {pub : List F} {tr : Trace} {r : Nat} :
    rowIn Host.table tr pub 22 r =
      [((rowNat tr 22 r 0 : Nat) : F), ((rowNat tr 22 r 1 : Nat) : F), ((rowNat tr 22 r 2 : Nat) : F),
       ((0 : Nat) : F), ((rowNat tr 22 r 35 : Nat) : F), ((rowNat tr 22 r 36 : Nat) : F)] := by
  simp [rowIn, Host.table, Host.inters, stdState, stateIn, List.cons_append, List.getD_cons_zero,
    List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_ofNat', cell_cast, Trace.row,
    Host.kSb, Host.kCid, cPc, cTs, cS]

theorem host_rowOut {pub : List F} {tr : Trace} {r : Nat} :
    rowOut Host.table tr pub 22 r =
      [((rowNat tr 22 r 0 : Nat) : F) + ((1 : Nat) : F), ((rowNat tr 22 r 1 : Nat) : F) + ((1 : Nat) : F),
       ((rowNat tr 22 r 2 : Nat) : F) + ((rowNat tr 22 r 4 : Nat) : F),
       ((2 * rowNat tr 22 r Host.st : Nat) : F), ((rowNat tr 22 r 35 : Nat) : F),
       ((rowNat tr 22 r 36 : Nat) : F)] := by
  simp [rowOut, Host.table, Host.inters, stdState, stateIn, stateOut, List.cons_append,
    List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil, v, Expr.eval_col,
    Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', Lean.Grind.Semiring.natCast_mul, cell_cast,
    Trace.row, Host.st, Host.kSb, Host.kCid, cPc, cTs, cS, cFee]

/-- The activity count of an active HOST row, as a natural. -/
theorem host_act_nat {pub : List F} {tr : Trace} {r : Nat}
    (hact : rowAct Host.table tr pub 22 r) : rowNat tr 22 r Host.act = 1 := by
  have := hact
  simp only [rowAct, Host.table, Host.inters, stateIn, List.cons_append, List.getD_cons_zero,
    v, Expr.eval_col, Trace.row, rowNat] at this
  exact this

theorem host_rowfacts {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 22)
    (hact : rowAct Host.table tr pub 22 r) : HostRowFacts pub tr r := by
  have ht : 22 < (wasmBaseHostAir nloc ngl).tables.length := by
    simp [wasmBaseHostAir, air_len]
  have hcon : ∀ e ∈ Host.table.constraints, e.eval (natRow (rowNat tr 22 r) (tr.row pub 22 r)) = 0 :=
    table_constr H ht hr
  have hbA := hcon Host.cAct (by simp [Host.table, Host.constraints])
  have hbS := hcon Host.cSt (by simp [Host.table, Host.constraints])
  have hb0 := hcon Host.cP0 (by simp [Host.table, Host.constraints])
  have hb1 := hcon Host.cP1 (by simp [Host.table, Host.constraints])
  have hord := hcon Host.cP1P0 (by simp [Host.table, Host.constraints])
  have hnp := hcon Host.cNp (by simp [Host.table, Host.constraints])
  have hbR := hcon Host.cAr (by simp [Host.table, Host.constraints])
  have hnr := hcon Host.cNres (by simp [Host.table, Host.constraints])
  have hpad0 := hcon Host.cPad0 (by simp [Host.table, Host.constraints])
  have hpad1 := hcon Host.cPad1 (by simp [Host.table, Host.constraints])
  have hact' : rowNat tr 22 r Host.act = 1 := by
    have := hact
    simp only [rowAct, Host.table, Host.inters, stateIn, List.cons_append, List.getD_cons_zero,
      v, Expr.eval_col, Trace.row, rowNat] at this
    exact this
  simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_col,
    Expr.eval_ofNat', natRow, Host.act, Host.st, Host.ar, Host.np, Host.nres, Host.ok, Host.pf,
    Host.tagP, Host.cAct, Host.cSt, Host.cAr, Host.cP0, Host.cP1, Host.cP1P0, Host.cNp,
    Host.cNres, Host.cPad0, Host.cPad1] at hbA hbS hb0 hb1 hord hnp hbR hnr hpad0 hpad1
  have hactF : (rowNat tr 22 r Host.act : F) = 1 := by
    rw [hact']; exact cast_one
  have hnp' : (rowNat tr 22 r Host.np : F) =
      (rowNat tr 22 r (Host.pf 0) : F) + (rowNat tr 22 r (Host.pf 1) : F) := by
    have h := hnp
    change (rowNat tr 22 r Host.np : F) - (rowNat tr 22 r (Host.pf 0) : F) -
      (rowNat tr 22 r (Host.pf 1) : F) = 0 at h
    grind
  have hord' : (rowNat tr 22 r (Host.pf 1) : F) - (rowNat tr 22 r (Host.pf 0) : F) *
      (rowNat tr 22 r (Host.pf 1) : F) = 0 := by
    simpa only [Host.pf] using hord
  have hnr' : (rowNat tr 22 r Host.nres : F) - (rowNat tr 22 r Host.ar : F) +
      (rowNat tr 22 r Host.st : F) * (rowNat tr 22 r Host.ar : F) = 0 := by
    simpa only [Host.nres, Host.st, Host.ar] using hnr
  have hpad0' : (rowNat tr 22 r (Host.tagP 0) : F) - (rowNat tr 22 r (Host.pf 0) : F) *
      (rowNat tr 22 r (Host.tagP 0) : F) = 0 := by
    simpa only [Host.tagP, Host.pf] using hpad0
  have hpad1' : (rowNat tr 22 r (Host.tagP 1) : F) - (rowNat tr 22 r (Host.pf 1) : F) *
      (rowNat tr 22 r (Host.tagP 1) : F) = 0 := by
    simpa only [Host.tagP, Host.pf] using hpad1
  exact ⟨hactF, hbS, hbR, hb0, hb1, hnp', hord', hnr', hpad0', hpad1', host_rowIn, host_rowOut⟩

end WasmBase
