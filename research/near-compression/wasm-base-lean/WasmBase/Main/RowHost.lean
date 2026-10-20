import WasmBase.StepHost
import WasmBase.Main.Rows
import WasmBase.Local.Call
/-!
# WasmBase.Main.RowHost — HOST row lemma (constraints + bus/STATE facts)

`host_rowfacts` turns an active HOST row of `wasmBaseHostAir` into the **field-level** facts the row
constraints state: the flags are bits and prefix-closed, `np = Σ_j pf j`, `nres = (1−st)·ar`,
absent arguments are zero, and the STATE messages have the standard shape (`pc+1`, `ts+1`,
`S+fee`, `halted = 2·st`, frame unchanged).  `host_bus_ok` records that the HOSTQ/HOSTR/HOSTT buses
are balanced against the witness oracle `HOSTO`.

The window is `Host.nArgs = 9` arguments; every statement below is stated over `Host.argRange`, so
the proofs are the `n`-ary form of the former two-argument ones (`pf 1 · (1 − pf 0) = 0` becomes
`∀ j, j+1 < nArgs → pf (j+1) · (1 − pf j) = 0`, `np = pf0 + pf1` becomes `np = Σ_j pf j`).

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
  /-- every argument-present flag is a bit -/
  pfBit : ∀ j, j < Host.nArgs →
    (rowNat tr 22 r (Host.pf j) : F) * ((rowNat tr 22 r (Host.pf j) : F) - 1) = 0
  /-- `np` is the number of present arguments -/
  npEq : (rowNat tr 22 r Host.np : F) =
    ((cellSum (rowNat tr 22 r) Host.pf Host.argRange : Nat) : F)
  /-- the flags are prefix-closed: an argument is present only if all earlier ones are -/
  order : ∀ j, j + 1 < Host.nArgs → (rowNat tr 22 r (Host.pf (j + 1)) : F) -
    (rowNat tr 22 r (Host.pf j) : F) * (rowNat tr 22 r (Host.pf (j + 1)) : F) = 0
  nresEq : (rowNat tr 22 r Host.nres : F) - (rowNat tr 22 r Host.ar : F) +
    (rowNat tr 22 r Host.st : F) * (rowNat tr 22 r Host.ar : F) = 0
  /-- an absent argument has a zero tag -/
  pad : ∀ j, j < Host.nArgs → (rowNat tr 22 r (Host.tagP j) : F) -
    (rowNat tr 22 r (Host.pf j) : F) * (rowNat tr 22 r (Host.tagP j) : F) = 0
  inS : rowIn Host.table tr pub 22 r =
    [((rowNat tr 22 r 0 : Nat) : F), ((rowNat tr 22 r 1 : Nat) : F), ((rowNat tr 22 r 2 : Nat) : F),
     ((0 : Nat) : F), ((rowNat tr 22 r Host.kSb : Nat) : F), ((rowNat tr 22 r Host.kCid : Nat) : F)]
  outS : rowOut Host.table tr pub 22 r =
    [((rowNat tr 22 r 0 : Nat) : F) + ((1 : Nat) : F), ((rowNat tr 22 r 1 : Nat) : F) + ((1 : Nat) : F),
     ((rowNat tr 22 r 2 : Nat) : F) + ((rowNat tr 22 r 4 : Nat) : F),
     ((2 * rowNat tr 22 r Host.st : Nat) : F), ((rowNat tr 22 r Host.kSb : Nat) : F),
     ((rowNat tr 22 r Host.kCid : Nat) : F)]

theorem host_rowIn {pub : List F} {tr : Trace} {r : Nat} :
    rowIn Host.table tr pub 22 r =
      [((rowNat tr 22 r 0 : Nat) : F), ((rowNat tr 22 r 1 : Nat) : F), ((rowNat tr 22 r 2 : Nat) : F),
       ((0 : Nat) : F), ((rowNat tr 22 r Host.kSb : Nat) : F), ((rowNat tr 22 r Host.kCid : Nat) : F)] := by
  simp [rowIn, Host.table, Host.inters, stdState, stateIn, List.cons_append, List.getD_cons_zero,
    List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_ofNat', cell_cast, Trace.row,
    Host.kSb, Host.kCid, cPc, cTs, cS]

theorem host_rowOut {pub : List F} {tr : Trace} {r : Nat} :
    rowOut Host.table tr pub 22 r =
      [((rowNat tr 22 r 0 : Nat) : F) + ((1 : Nat) : F), ((rowNat tr 22 r 1 : Nat) : F) + ((1 : Nat) : F),
       ((rowNat tr 22 r 2 : Nat) : F) + ((rowNat tr 22 r 4 : Nat) : F),
       ((2 * rowNat tr 22 r Host.st : Nat) : F), ((rowNat tr 22 r Host.kSb : Nat) : F),
       ((rowNat tr 22 r Host.kCid : Nat) : F)] := by
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

/-- The `Nat` sum of a fold of `Expr`s over `Host.argRange` at a row, as `cellSum`. -/
theorem eval_pfSum (c : Nat → Nat) (rw : Row) :
    Host.pfSum.eval (natRow c rw) = ((cellSum c Host.pf Host.argRange : Nat) : F) := by
  unfold Host.pfSum Host.sumE
  rw [eval_sumE]
  show ((0 : Nat) : F) + _ = _
  grind

/-- Membership of the named HOST constraints. -/
theorem argRange_mem (j : Nat) (hj : j < Host.nArgs) : j ∈ Host.argRange := by
  have hn : Host.nArgs = 9 := rfl
  rw [hn] at hj
  simp [Host.argRange]; omega

/-- The five groups of `Host.constraints`, right-associated (so membership is a chain of
`List.mem_append_left` / `List.mem_append_right`). -/
theorem constraints_groups :
    Host.constraints =
      Host.cBase ++ (Host.cFlags ++ (Host.cOrder ++ (Host.cPads ++ (Host.cGates ++ [Host.cActNres])))) := by
  simp [Host.constraints, List.append_assoc]

theorem host_cP_mem (j : Nat) (hj : j < Host.nArgs) : Host.cP j ∈ Host.constraints := by
  rw [constraints_groups]
  exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem (argRange_mem j hj)))

theorem host_cPOrder_mem (j : Nat) (hj : j + 1 < Host.nArgs) : Host.cPOrder j ∈ Host.constraints := by
  have h : Host.cPOrder j ∈ Host.cOrder := by
    simp only [Host.cOrder, List.mem_filterMap]
    exact ⟨j, argRange_mem j (by omega), by rw [ite_eq_left hj]⟩
  rw [constraints_groups]
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ h))

theorem host_cPad_mem (j : Nat) (hj : j < Host.nArgs) : Host.cPad j ∈ Host.constraints := by
  have h : Host.cPad j ∈ Host.cPads := by
    simp only [Host.cPads, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨j, argRange_mem j hj, List.mem_append_left _ List.mem_cons_self⟩
  rw [constraints_groups]
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_left _ h)))

theorem host_cActPf_mem (j : Nat) (hj : j < Host.nArgs) : Host.cActPf j ∈ Host.constraints := by
  rw [constraints_groups]
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem (argRange_mem j hj))))))

theorem host_cAct_mem : Host.cAct ∈ Host.constraints := by
  rw [constraints_groups]
  exact List.mem_append_left _ (by simp [Host.cBase])

theorem host_cSt_mem : Host.cSt ∈ Host.constraints := by
  rw [constraints_groups]
  exact List.mem_append_left _ (by simp [Host.cBase])

theorem host_cAr_mem : Host.cAr ∈ Host.constraints := by
  rw [constraints_groups]
  exact List.mem_append_left _ (by simp [Host.cBase])

theorem host_cNres_mem : Host.cNres ∈ Host.constraints := by
  rw [constraints_groups]
  exact List.mem_append_left _ (by simp [Host.cBase])

theorem host_cNp_mem : Host.cNp ∈ Host.constraints := by
  rw [constraints_groups]
  exact List.mem_append_left _ (by simp [Host.cBase])

theorem host_cActNres_mem : Host.cActNres ∈ Host.constraints := by
  rw [constraints_groups]
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_self)))))

theorem host_rowfacts {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 22)
    (hact : rowAct Host.table tr pub 22 r) : HostRowFacts pub tr r := by
  have ht : 22 < (wasmBaseHostAir nloc ngl).tables.length := by
    simp [wasmBaseHostAir, air_len]
  have hcon : ∀ e ∈ Host.table.constraints, e.eval (natRow (rowNat tr 22 r) (tr.row pub 22 r)) = 0 :=
    table_constr H ht hr
  have hact' : rowNat tr 22 r Host.act = 1 := host_act_nat hact
  have hactF : (rowNat tr 22 r Host.act : F) = 1 := by
    rw [hact']; exact cast_one
  have hbS : (rowNat tr 22 r Host.st : F) * ((rowNat tr 22 r Host.st : F) - 1) = 0 := by
    have h := hcon Host.cSt host_cSt_mem
    simpa only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat',
      natRow_cur, cast_one, Host.cSt, Host.st] using h
  have hbR : (rowNat tr 22 r Host.ar : F) * ((rowNat tr 22 r Host.ar : F) - 1) = 0 := by
    have h := hcon Host.cAr host_cAr_mem
    simpa only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat',
      natRow_cur, cast_one, Host.cAr, Host.ar] using h
  have hpfBit : ∀ j, j < Host.nArgs →
      (rowNat tr 22 r (Host.pf j) : F) * ((rowNat tr 22 r (Host.pf j) : F) - 1) = 0 := by
    intro j hj
    have h := hcon (Host.cP j) (host_cP_mem j hj)
    simpa only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat',
      natRow_cur, cast_one, Host.cP] using h
  have hnp' : (rowNat tr 22 r Host.np : F) =
      ((cellSum (rowNat tr 22 r) Host.pf Host.argRange : Nat) : F) := by
    have h := hcon Host.cNp host_cNp_mem
    simp only [v, Expr.eval_sub', Expr.eval_col, natRow_cur, Host.cNp] at h
    rw [eval_pfSum] at h
    have : (rowNat tr 22 r Host.np : F) - ((cellSum (rowNat tr 22 r) Host.pf Host.argRange : Nat) : F) = 0 := h
    grind
  have hord' : ∀ j, j + 1 < Host.nArgs → (rowNat tr 22 r (Host.pf (j + 1)) : F) -
      (rowNat tr 22 r (Host.pf j) : F) * (rowNat tr 22 r (Host.pf (j + 1)) : F) = 0 := by
    intro j hj
    have h := hcon (Host.cPOrder j) (host_cPOrder_mem j hj)
    simpa only [v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, natRow_cur, Host.cPOrder] using h
  have hnr' : (rowNat tr 22 r Host.nres : F) - (rowNat tr 22 r Host.ar : F) +
      (rowNat tr 22 r Host.st : F) * (rowNat tr 22 r Host.ar : F) = 0 := by
    have h := hcon Host.cNres host_cNres_mem
    simpa only [v, Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_col, natRow_cur,
      Host.cNres, Host.nres, Host.st, Host.ar] using h
  have hpad : ∀ j, j < Host.nArgs → (rowNat tr 22 r (Host.tagP j) : F) -
      (rowNat tr 22 r (Host.pf j) : F) * (rowNat tr 22 r (Host.tagP j) : F) = 0 := by
    intro j hj
    have h := hcon (Host.cPad j) (host_cPad_mem j hj)
    simpa only [v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, natRow_cur, Host.cPad] using h
  exact ⟨hactF, hbS, hbR, hpfBit, hnp', hord', hnr', hpad, host_rowIn, host_rowOut⟩

end WasmBase
