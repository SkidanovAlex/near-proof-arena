import WasmBase.Main.ExecHost
import WasmBase.Main.SegHarness
import WasmBase.Main.HostChipBits
import WasmBase.Main.Lookups

/-!
# WasmBase.Main.HostBus — the STATE/CH bus decompositions of `wasmBaseHostAir`

`wasm_base_exec_host` (`Main/SegHarness.lean`) takes the STATE- and CH-bus `Perm`s (`hst`, `hch`) as
hypotheses.  This file discharges them from `Holds`, which is the last step between that theorem and
a statement that only assumes the AIR relation.

## Shape

`msgs_state_host` / `msgs_ch_host` (`Main/ExecHost.lean`) split the host AIR's messages into the
base AIR's plus the HOST table's.  `msgs_state` / `msgs_ch` (`Main/Exec.lean`) express the base
AIR's.  Composing, and using `msgs_perm` on each bus, gives

* `host_msgs_state_perm` — the STATE bus is a permutation of the initial message plus the action
  rows' `rowOutH`s against the final message plus the `rowInH`s;
* `host_msgs_ch_perm` — the CH bus likewise, with the initial/final raw message blocks.

Both are stated against `actListHost`, the list `wasm_base_exec_host` uses, so they plug straight in.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## `rowOutH`/`rowInH` agree with the base accessors off table 22 -/

theorem rowOutH_eq_of_ne {tr : Trace} {pub : List F} {ρ : Nat × Nat} (h : ρ.1 ≠ 22) :
    rowOutH tr pub ρ = rowOut (chipT ρ.1) tr pub ρ.1 ρ.2 := by
  simp [rowOutH, chipTHost, h]

theorem rowInH_eq_of_ne {tr : Trace} {pub : List F} {ρ : Nat × Nat} (h : ρ.1 ≠ 22) :
    rowInH tr pub ρ = rowIn (chipT ρ.1) tr pub ρ.1 ρ.2 := by
  simp [rowInH, chipTHost, h]

theorem rowOutH_eq_host {tr : Trace} {pub : List F} {ρ : Nat × Nat} (h : ρ.1 = 22) :
    rowOutH tr pub ρ = rowOut Host.table tr pub 22 ρ.2 := by
  simp [rowOutH, chipTHost, h]

theorem rowInH_eq_host {tr : Trace} {pub : List F} {ρ : Nat × Nat} (h : ρ.1 = 22) :
    rowInH tr pub ρ = rowIn Host.table tr pub 22 ρ.2 := by
  simp [rowInH, chipTHost, h]

/-- The instruction rows of `actList` are not HOST rows. -/
theorem actList_ne_host {tr : Trace} {pub : List F} {ρ : Nat × Nat} (h : ρ ∈ actList tr pub) :
    ρ.1 ≠ 22 := by
  obtain ⟨h1, h9, -⟩ := mem_actList h
  omega

/-- The HOST rows of `hostActRows` are HOST rows. -/
theorem hostActRows_eq_host {tr : Trace} {pub : List F} {ρ : Nat × Nat} (h : ρ ∈ hostActRows tr pub) :
    ρ.1 = 22 := by
  simp only [hostActRows, List.mem_map] at h
  obtain ⟨r, _, rfl⟩ := h
  rfl

/-! ## The STATE bus -/

/-- `actListHost` split into its two parts, with the accessors specialised. -/
theorem actListHost_map_out (tr : Trace) (pub : List F) :
    (actListHost tr pub).map (rowOutH tr pub) =
      (actList tr pub).map (fun ρ => rowOut (chipT ρ.1) tr pub ρ.1 ρ.2) ++
        (hostActRows tr pub).map (fun ρ => rowOut Host.table tr pub 22 ρ.2) := by
  unfold actListHost
  rw [List.map_append]
  congr 1
  · refine List.map_congr_left fun ρ hρ => ?_
    exact rowOutH_eq_of_ne (actList_ne_host hρ)
  · refine List.map_congr_left fun ρ hρ => ?_
    exact rowOutH_eq_host (hostActRows_eq_host hρ)

/-- The same for the inputs. -/
theorem actListHost_map_in (tr : Trace) (pub : List F) :
    (actListHost tr pub).map (rowInH tr pub) =
      (actList tr pub).map (fun ρ => rowIn (chipT ρ.1) tr pub ρ.1 ρ.2) ++
        (hostActRows tr pub).map (fun ρ => rowIn Host.table tr pub 22 ρ.2) := by
  unfold actListHost
  rw [List.map_append]
  congr 1
  · refine List.map_congr_left fun ρ hρ => ?_
    exact rowInH_eq_of_ne (actList_ne_host hρ)
  · refine List.map_congr_left fun ρ hρ => ?_
    exact rowInH_eq_host (hostActRows_eq_host hρ)

/-- **The HOST rows' outputs**, as the `msgs_state_host` flatMap produces them. -/
theorem hostActRows_rowOut (tr : Trace) (pub : List F) :
    (hostActRows tr pub).map (fun ρ => rowOut Host.table tr pub 22 ρ.2) =
      (List.range (tr.height 22)).flatMap (fun r =>
        if rowAct Host.table tr pub 22 r then [rowOut Host.table tr pub 22 r] else []) := by
  unfold hostActRows
  induction (List.range (tr.height 22)) with
  | nil => rfl
  | cons a l ih =>
    by_cases h : rowAct Host.table tr pub 22 a <;> simp [h, ih]

/-- **The HOST rows' inputs**, likewise. -/
theorem hostActRows_rowIn (tr : Trace) (pub : List F) :
    (hostActRows tr pub).map (fun ρ => rowIn Host.table tr pub 22 ρ.2) =
      (List.range (tr.height 22)).flatMap (fun r =>
        if rowAct Host.table tr pub 22 r then [rowIn Host.table tr pub 22 r] else []) := by
  unfold hostActRows
  induction (List.range (tr.height 22)) with
  | nil => rfl
  | cons a l ih =>
    by_cases h : rowAct Host.table tr pub 22 a <;> simp [h, ih]

/-! ## The two bus permutations -/

/-- **The STATE bus of a host trace is a permutation** of `initMsg :: outputs` against
`finalMsg :: inputs`, with the action rows being `actListHost`.  This is the `hst` premise of
`wasm_base_exec_host`. -/
theorem host_msgs_state_perm {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr)
    (H0 : Holds (wasmBaseAir nloc ngl) pub tr)
    (hpub : PubOK X nloc ngl pub) (CF : ChipFacts X nloc ngl pub tr) :
    (msgs (wasmBaseHostAir nloc ngl) tr pub busState true).Perm
      (msgs (wasmBaseHostAir nloc ngl) tr pub busState false) :=
  msgs_perm H busState
    (fun o ho hk => occ_bits_host H H0 hpub CF o ho (Or.inl hk))

/-- **The CH bus of a host trace is a permutation.**  This is the `hch` premise. -/
theorem host_msgs_ch_perm {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr)
    (H0 : Holds (wasmBaseAir nloc ngl) pub tr)
    (hpub : PubOK X nloc ngl pub) (CF : ChipFacts X nloc ngl pub tr) :
    (msgs (wasmBaseHostAir nloc ngl) tr pub busStk true).Perm
      (msgs (wasmBaseHostAir nloc ngl) tr pub busStk false) :=
  msgs_perm H busStk
    (fun o ho hk => occ_bits_host H H0 hpub CF o ho (Or.inr hk))

/-! ## The `hst`/`hch` premises of `wasm_base_exec_host`

`wasm_base_exec_host` wants the perms in terms of `actListHost` and the `rowOutH`/`rowInH`
accessors.  These two lemmas rewrite the `msgs` perms above into that form. -/

/-- `msgs` on the STATE bus, expanded over `actListHost`. -/
theorem msgs_state_host_expand {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H0 : Holds (wasmBaseAir nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub) :
    msgs (wasmBaseHostAir nloc ngl) tr pub busState true =
      stMsg 0 1 0 0 0 0 :: (actListHost tr pub).map (rowOutH tr pub) ∧
    msgs (wasmBaseHostAir nloc ngl) tr pub busState false =
      [tr.cell 0 0 Boundary.pcf, pub.getD Boundary.pubN 0, pub.getD Boundary.pubS 0,
        pub.getD Boundary.pubStatus 0, tr.cell 0 0 Boundary.sbf, tr.cell 0 0 Boundary.cidf] ::
        (actListHost tr pub).map (rowInH tr pub) := by
  obtain ⟨ms1, ms2⟩ := msgs_state H0 hpub
  obtain ⟨mh1, mh2⟩ := msgs_state_host (nloc := nloc) (ngl := ngl) tr pub
  constructor
  · rw [mh1, ms1, actListHost_map_out, hostActRows_rowOut]
    simp only [List.cons_append, List.nil_append]
  · rw [mh2, ms2, actListHost_map_in, hostActRows_rowIn]
    simp only [List.cons_append, List.nil_append]

/-- **`hst` for `wasm_base_exec_host`, discharged from `Holds`.** -/
theorem host_hst {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr)
    (H0 : Holds (wasmBaseAir nloc ngl) pub tr)
    (hpub : PubOK X nloc ngl pub) (CF : ChipFacts X nloc ngl pub tr) :
    (stMsg 0 1 0 0 0 0 :: (actListHost tr pub).map (rowOutH tr pub)).Perm
      ([tr.cell 0 0 Boundary.pcf, pub.getD Boundary.pubN 0, pub.getD Boundary.pubS 0,
        pub.getD Boundary.pubStatus 0, tr.cell 0 0 Boundary.sbf, tr.cell 0 0 Boundary.cidf] ::
        (actListHost tr pub).map (rowInH tr pub)) := by
  obtain ⟨e1, e2⟩ := msgs_state_host_expand (X := X) H0 hpub
  rw [← e1, ← e2]
  exact host_msgs_state_perm H H0 hpub CF

end WasmBase
