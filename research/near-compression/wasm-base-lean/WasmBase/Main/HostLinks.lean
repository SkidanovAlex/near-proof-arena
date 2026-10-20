import WasmBase.Main.Host
import WasmBase.Main.Lookups
/-!
# WasmBase.Main.HostLinks — `wasmBaseHostAir` and the R16 lookup on its HOST rows

`wasmBaseHostAir nloc ngl = wasmBaseAir nloc ngl ++ [HOST, HOSTO, HOSTT]`, so tables `0..21` are
the proved base tables (index for index) and tables `22..24` are the new ones.  This file records
that decomposition (`host_air_*`), the R16 receive-side classification for the extended AIR
(`host_recv_only_range16`), and the resulting **R16 soundness** on host traces
(`host_r16_sound`): every R16 query with count 1 is a value `< 2^16`.  `Main/RowHostSpec` uses it to
turn the HOST row's `rb`/`ga` limbs into 16-bit facts, which is what makes the row's `stkSend`
message the encoding of the response's result word.

The bus decomposition of `Exec.lean` for the extended AIR (piece 2) is stated in
`Main/ExecHost.lean`.
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## Table decomposition -/

theorem host_air_len (nloc ngl : Nat) : (wasmBaseHostAir nloc ngl).tables.length = 26 := rfl

theorem host_air_append (nloc ngl : Nat) :
    (wasmBaseHostAir nloc ngl).tables =
      (wasmBaseAir nloc ngl).tables ++ [Host.table, HostO.table, HostTab.table, HostB.table] := rfl

theorem host_air_get (nloc ngl t : Nat) (ht : t < 22) :
    (wasmBaseHostAir nloc ngl).tables[t]'(by rw [host_air_len]; omega) =
      (wasmBaseAir nloc ngl).tables[t]'(by simp [air_len]; exact ht) := by
  simp only [wasmBaseHostAir]
  exact List.getElem_append_left (by simp [air_len]; exact ht)

theorem host_air_22 (nloc ngl : Nat) :
    (wasmBaseHostAir nloc ngl).tables[22]'(by rw [host_air_len]; decide) = Host.table := rfl
theorem host_air_23 (nloc ngl : Nat) :
    (wasmBaseHostAir nloc ngl).tables[23]'(by rw [host_air_len]; decide) = HostO.table := rfl
theorem host_air_24 (nloc ngl : Nat) :
    (wasmBaseHostAir nloc ngl).tables[24]'(by rw [host_air_len]; decide) = HostTab.table := rfl
theorem host_air_25 (nloc ngl : Nat) :
    (wasmBaseHostAir nloc ngl).tables[25]'(by rw [host_air_len]; decide) = HostB.table := rfl

theorem host_numPub (nloc ngl : Nat) :
    (wasmBaseHostAir nloc ngl).numPub = (wasmBaseAir nloc ngl).numPub := rfl

/-- The occurrence list splits by table index (extended AIR). -/
theorem host_occ_table {nloc ngl : Nat} {tr : Trace} {pub : List F} {o : Occ}
    (ho : o ∈ occs (wasmBaseHostAir nloc ngl) tr pub) :
    ∃ t, ∃ _ht : t < 26, ∃ r, r < tr.height t ∧
      ∃ i ∈ ((wasmBaseHostAir nloc ngl).tables[t]'(by rw [host_air_len]; exact _ht)).inters,
        o = (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)), (i.count.eval (tr.row pub t r)).toNat) := by
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  have h26 : t < 26 := by simpa [host_air_len] using ht
  exact ⟨t, h26, r, hr, i, by simpa using hi, rfl⟩

/-- An occurrence of the base AIR is an occurrence of the extended AIR. -/
theorem occs_mono_host {nloc ngl : Nat} {tr : Trace} {pub : List F} {o : Occ}
    (ho : o ∈ occs (wasmBaseAir nloc ngl) tr pub) : o ∈ occs (wasmBaseHostAir nloc ngl) tr pub := by
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  have h22 : t < 22 := by simpa [air_len] using ht
  rw [mem_occs]
  refine ⟨t, by rw [host_air_len]; omega, r, hr, i, ?_, rfl⟩
  rw [host_air_get nloc ngl t h22]
  simpa using hi

/-- An occurrence of the HOST table is an occurrence of the extended AIR. -/
theorem occs_host_of {nloc ngl : Nat} {tr : Trace} {pub : List F} {o : Occ} {r : Nat}
    (hr : r < tr.height 22) {i : Inter} (hi : i ∈ Host.inters)
    (ho : o = (i.bus, i.send, i.msg.map (·.eval (tr.row pub 22 r)), (i.count.eval (tr.row pub 22 r)).toNat)) :
    o ∈ occs (wasmBaseHostAir nloc ngl) tr pub := by
  rw [mem_occs]
  refine ⟨22, by rw [host_air_len]; decide, r, hr, i, ?_, ho⟩
  rw [host_air_22]; exact hi

/-! ## Which tables answer (rather than query) R16 -/

theorem host_table_r16 : Host.inters.all (fun i => i.bus != busR16 || i.send) = true := by decide
theorem hostO_table_r16 : HostO.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by decide
theorem hostTab_table_r16 : HostTab.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by
  decide
theorem hostB_table_r16 : HostB.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by
  decide

theorem bnd_r16 (nloc ngl : Nat) :
    ∀ i ∈ (Boundary.table nloc ngl).inters, i.bus = busR16 → i.send = true :=
  fun i hi hb => absurd hb (boundary_lookups nloc ngl i hi).1

theorem table_r16_of_all {T : Table}
    (h : T.inters.all (fun i => i.bus != busR16 || i.send) = true) :
    ∀ i ∈ T.inters, i.bus = busR16 → i.send = true :=
  recv_only_gen (L := [T]) (by simpa using h) T (by simp)
theorem code_table_r16 : Code.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by decide
theorem drain_table_r16 : Drain.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by decide
theorem byte_table_r16 : Byte.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by decide
theorem meminit_table_r16 : MemInit.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by
  decide
theorem data_table_r16 : Data.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by decide
theorem func_table_r16 : Func.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by decide

theorem instr_tables_r16 : instrTables.all (fun T => T.inters.all (fun i => i.bus != busR16 || i.send)) = true := by
  simp only [instrTables, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.true_and]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

/-- The tables of the base AIR other than RANGE16 answer (do not query) R16. -/
theorem base_recv_only_r16 (nloc ngl : Nat) :
    ∀ T ∈ (wasmBaseAir nloc ngl).tables, T ≠ Range16.table → ∀ i ∈ T.inters, i.bus = busR16 → i.send = true := by
  intro T hT hne i hi hb
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hT
  have h22 : t < 22 := by simpa [air_len] using ht
  rcases table_class nloc ngl t h22 with ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ |
    ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨_, _, hT⟩
  · exact bnd_r16 nloc ngl i hi hb
  · exact table_r16_of_all code_table_r16 i (hT ▸ hi) hb
  · exact table_r16_of_all drain_table_r16 i (hT ▸ hi) hb
  · exact absurd hT hne
  · exact table_r16_of_all byte_table_r16 i (hT ▸ hi) hb
  · exact table_r16_of_all meminit_table_r16 i (hT ▸ hi) hb
  · exact table_r16_of_all data_table_r16 i (hT ▸ hi) hb
  · exact table_r16_of_all func_table_r16 i (hT ▸ hi) hb
  · exact recv_only_gen instr_tables_r16 _ hT i hi hb

/-- Every table of `wasmBaseHostAir` other than RANGE16 **answers** R16 queries. -/
theorem host_recv_only_range16 (nloc ngl : Nat) :
    ∀ T ∈ (wasmBaseHostAir nloc ngl).tables, T ≠ Range16.table → ∀ i ∈ T.inters, i.bus = busR16 → i.send = true := by
  intro T hT hne i hi hb
  rw [host_air_append, List.mem_append] at hT
  rcases hT with h | h
  · exact base_recv_only_r16 nloc ngl T h hne i hi hb
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact table_r16_of_all host_table_r16 i hi hb
    · exact table_r16_of_all hostO_table_r16 i hi hb
    · exact table_r16_of_all hostTab_table_r16 i hi hb
    · exact table_r16_of_all hostB_table_r16 i hi hb

/-! ## R16 soundness on host traces -/

/-- The messages of a row of the RANGE16 table lie in `0 .. 2^16 − 1`. -/
theorem host_range16_values {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) :
    tr.height 15 = 65536 ∧ ∀ r, r < tr.height 15 → rowNat tr 15 r Range16.val = r := by
  have ht : 15 < (wasmBaseHostAir nloc ngl).tables.length := by rw [host_air_len]; decide
  have hT : (wasmBaseHostAir nloc ngl).tables[15]'ht = Range16.table := by
    rw [host_air_get nloc ngl 15 (by decide)]
    rfl
  exact range16_values H ht hT

theorem bnd_name (nloc ngl : Nat) : (Boundary.table nloc ngl).name = "BOUNDARY" := rfl

theorem air_tables_eq (nloc ngl : Nat) : (wasmBaseAir nloc ngl).tables =
    [Boundary.table nloc ngl, Add.table, Bit.table, Mul.table, Shift.table, Cmp.table, Const.table,
     Stack.table, Ctrl.table, Local.table, Div.table, Load.table, Store.table, Call.table, Ret.table,
     Range16.table, Byte.table, Code.table, Drain.table, MemInit.table, Data.table, Func.table] := rfl

/-- In the base AIR, RANGE16 sits at index 15 only. -/
theorem air_neq_range16 {nloc ngl t : Nat} (h : t < 22)
    (ht : (wasmBaseAir nloc ngl).tables[t]'(by simp [air_len]; exact h) = Range16.table) : t = 15 := by
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨
    t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 19 ∨ t = 20 ∨ t = 21 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | (exfalso
       have hn : (Boundary.table nloc ngl).name = Range16.table.name := congrArg Table.name ht
       rw [bnd_name] at hn
       simp [Range16.table] at hn)
    | (exfalso
       first
       | (have hn : Add.table.name = Range16.table.name := congrArg Table.name ht; revert hn; decide)
       | (have hn : Bit.table.name = Range16.table.name := congrArg Table.name ht; revert hn; decide)
       | (have hn : Mul.table.name = Range16.table.name := congrArg Table.name ht; revert hn; decide)
       | (have hn : Shift.table.name = Range16.table.name := congrArg Table.name ht; revert hn; decide)
       | (have hn : Cmp.table.name = Range16.table.name := congrArg Table.name ht; revert hn; decide)
       | (have hn : Const.table.name = Range16.table.name := congrArg Table.name ht; revert hn; decide)
       | (have hn : Stack.table.name = Range16.table.name := congrArg Table.name ht; revert hn; decide)
       | (have hn : Ctrl.table.name = Range16.table.name := congrArg Table.name ht; revert hn; decide)
       | (have hn : Local.table.name = Range16.table.name := congrArg Table.name ht; revert hn; decide)
       | (have hn : Div.table.name = Range16.table.name := congrArg Table.name ht; revert hn; decide)
       | (have hn : Load.table.name = Range16.table.name := congrArg Table.name ht; revert hn; decide)
       | (have hn : Store.table.name = Range16.table.name := congrArg Table.name ht; revert hn; decide)
       | (have hn : Call.table.name = Range16.table.name := congrArg Table.name ht; revert hn; decide)
       | (have hn : Ret.table.name = Range16.table.name := congrArg Table.name ht; revert hn; decide)
       | (have hn : Byte.table.name = Range16.table.name := congrArg Table.name ht; revert hn; decide)
       | (have hn : Code.table.name = Range16.table.name := congrArg Table.name ht; revert hn; decide)
       | (have hn : Drain.table.name = Range16.table.name := congrArg Table.name ht; revert hn; decide)
       | (have hn : MemInit.table.name = Range16.table.name := congrArg Table.name ht; revert hn; decide)
       | (have hn : Data.table.name = Range16.table.name := congrArg Table.name ht; revert hn; decide)
       | (have hn : Func.table.name = Range16.table.name := congrArg Table.name ht; revert hn; decide))

/-- The messages of the RANGE16 table, row by row. -/
theorem host_range16_row {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 15) {i : Inter}
    (hi : i ∈ Range16.table.inters) :
    i.msg.map (·.eval (tr.row pub 15 r)) = [((r : Nat) : F)] := by
  obtain ⟨hh, hv⟩ := host_range16_values H
  have hr' : r < 65536 := by omega
  simp only [Range16.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
  subst hi
  simp only [List.map_cons, List.map_nil]
  rw [row_eq_natRow]
  simp only [v, Expr.eval_col, natRow, Range16.val]
  have e : rowNat tr 15 r Range16.val = r := hv r hr
  simp only [Range16.val] at e
  simpa using congrArg (fun n => ((n : Nat) : F)) e

/-- **R16 soundness for `wasmBaseHostAir`**: every R16 query with count 1 is a single value
`< 2^16`. -/
theorem host_r16_sound {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr)
    (hsend : ∀ o ∈ occs (wasmBaseHostAir nloc ngl) tr pub, o.2.1 = true → o.2.2.2 ≤ 1)
    {o : Occ} (ho : o ∈ occs (wasmBaseHostAir nloc ngl) tr pub) (hb : o.1 = busR16)
    (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ x : F, o.2.2.1 = [x] ∧ x.toNat < 65536 := by
  refine lookup_sound H busR16 (fun m => ∃ x : F, m = [x] ∧ x.toNat < 65536) ?_
    (fun o' ho' _ hs' => hsend o' ho' hs') ho hb hs hc
  intro o' ho' hb' hs' _
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := host_occ_table ho'
  simp only at hb' hs' ⊢
  rcases (show t < 22 ∨ t = 22 ∨ t = 23 ∨ t = 24 ∨ t = 25 by omega) with h | rfl | rfl | rfl | rfl
  · rw [host_air_get nloc ngl t h] at hi
    rcases (show t = 15 ∨ t ≠ 15 by omega) with rfl | h15
    · obtain ⟨hh, -⟩ := host_range16_values H
      show ∃ x : F, List.map (fun x => Expr.eval (tr.row pub 15 r) x) i.msg = [x] ∧ x.toNat < 65536
      refine ⟨((r : Nat) : F), host_range16_row H hr hi, ?_⟩
      rw [Fp.toNat_cast_of_lt (by rw [P_val]; omega)]
      omega
    · have hne : (wasmBaseAir nloc ngl).tables[t]'h ≠ Range16.table := by
        intro he
        exact h15 (air_neq_range16 h he)
      exact absurd (base_recv_only_r16 nloc ngl _ (List.getElem_mem _) hne i hi hb') (by simp [hs'])
  · rw [host_air_22] at hi
    exact absurd (table_r16_of_all host_table_r16 i hi hb') (by simp [hs'])
  · rw [host_air_23] at hi
    exact absurd (table_r16_of_all hostO_table_r16 i hi hb') (by simp [hs'])
  · rw [host_air_24] at hi
    exact absurd (table_r16_of_all hostTab_table_r16 i hi hb') (by simp [hs'])
  · rw [host_air_25] at hi
    exact absurd (table_r16_of_all hostB_table_r16 i hi hb') (by simp [hs'])

/-- The HOST row's `rb` limbs are 16-bit (each is queried on R16 with count `act`). -/
theorem host_rb_limb {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr)
    (hsend : ∀ o ∈ occs (wasmBaseHostAir nloc ngl) tr pub, o.2.1 = true → o.2.2.2 ≤ 1)
    {r : Nat} (hr : r < tr.height 22) (hact : rowAct Host.table tr pub 22 r) :
    ∀ i, i < 4 → rowNat tr 22 r (Host.rb + i) < 65536 := by
  intro i hi
  have hcnt : rowNat tr 22 r Host.act = 1 := host_act_nat hact
  have hmem : r16 (v (Host.rb + i)) (v Host.act) ∈ Host.inters := by
    simp only [Host.table, Host.inters, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
      List.mem_flatMap, List.mem_map, List.mem_range]
    grind
  have hocc : (busR16, true, [((rowNat tr 22 r (Host.rb + i) : Nat) : F)], rowNat tr 22 r Host.act) ∈
      occs (wasmBaseHostAir nloc ngl) tr pub := by
    refine occs_host_of hr hmem ?_
    simp only [r16, List.map_cons, List.map_nil, v, Expr.eval_col, Trace.row, cell_cast]
    rw [Fp.toNat_cast_of_lt (rowNat_lt tr 22 r Host.act)]
  obtain ⟨x, hx, hxl⟩ := host_r16_sound H hsend hocc (by rfl) (by simp) (by simp [hcnt])
  simp only [List.cons.injEq, and_true] at hx
  subst hx
  rwa [Fp.toNat_cast_of_lt (rowNat_lt tr 22 r (Host.rb + i))] at hxl

end WasmBase
