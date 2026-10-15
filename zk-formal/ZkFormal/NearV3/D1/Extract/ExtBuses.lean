import ZkFormal.NearV3.D1.Extract.ViewsD1

/-!
# `ZkFormal.NearV3.D1.Extract.ExtBuses` — the extended `nodeD1` / `uniqD1`: base views and new buses

Lane `v3-d1-a7b` (plan §5 R-5 → (B)).  Tables 2 and 6 of `nearAirV3D1` extend `nodeA7` and
`uniqV3` append-only (`D1/Tables/NodeStubDefs`, `D1/Tables/UniqGapDefs`).  So:
* their base views apply unchanged (`ViewsD1.nodeA7LocalD1`, `nodeLocalD1`, `uniqLocalD1`:
  `TableLocal` of the base table from `HoldsP nearAirV3D1`);
* their traffic on every bus other than the new ones (`SEDGE`, `NMQ` for `nodeD1`; `GB` for
  `uniqD1`) is exactly the base table's (`nodeD1_count_base`, `uniqD1_count_base`): the D0a
  record traffic (`nodeTraffic3` + the A7 part, `uniqTraffic`) stays the whole traffic of these
  tables on every D0a / phase-1 bus;
* the extension interactions are silent on every other bus (`nodeStub_count_off`,
  `uniqGap_count_off`; their raw counts are the extra terms of `Link.balSumBaseD1`).
-/

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}

theorem tableBusCount_off {is : List Interaction} {t b : Nat} (h : ∀ i ∈ is, i.bus ≠ b) (s : Bool)
    (m : List Fp) : tableBusCount is tr t pub b s m = 0 := by
  rw [tableBusCount_eq]
  have : (List.range (tr.height t)).flatMap (fun r => rowTraffic is tr t r pub b s) = [] :=
    List.flatMap_eq_nil_iff.2 fun r _ => by
      unfold rowTraffic
      exact List.flatMap_eq_nil_iff.2 fun i hi => by simp [h i hi]
  rw [this]; rfl

theorem nodeStub_buses : ∀ i ∈ NodeStub.interactions, i.bus = B_SEDGE ∨ i.bus = B_NMQ := by
  intro i hi
  simp only [NodeStub.interactions, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> simp [ZkFormal.Near.Dsl.send, ZkFormal.Near.Dsl.recv]

theorem uniqGap_buses : ∀ i ∈ UniqGap.interactions, i.bus = B_GB := by
  intro i hi
  simp only [UniqGap.interactions, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl <;> simp [ZkFormal.Near.Dsl.send, ZkFormal.Near.Dsl.recv]

theorem nodeStub_count_off {t b : Nat} (h1 : b ≠ B_SEDGE) (h2 : b ≠ B_NMQ) (s : Bool) (m : List Fp) :
    tableBusCount NodeStub.interactions tr t pub b s m = 0 :=
  tableBusCount_off (fun i hi he => by rcases nodeStub_buses i hi with h | h <;> simp_all) s m

theorem uniqGap_count_off {t b : Nat} (h1 : b ≠ B_GB) (s : Bool) (m : List Fp) :
    tableBusCount UniqGap.interactions tr t pub b s m = 0 :=
  tableBusCount_off (fun i hi he => by have := uniqGap_buses i hi; simp_all) s m

/-- **`nodeD1` off `SEDGE` / `NMQ` is `nodeA7`.** -/
theorem nodeD1_count_base {t b : Nat} (h1 : b ≠ B_SEDGE) (h2 : b ≠ B_NMQ) (s : Bool) (m : List Fp) :
    tableBusCount nodeD1.interactions tr t pub b s m =
      tableBusCount ZkFormal.NearV3.UnfoldA7.nodeA7.interactions tr t pub b s m := by
  rw [show nodeD1.interactions = ZkFormal.NearV3.UnfoldA7.nodeA7.interactions ++ NodeStub.interactions
    from rfl, ZkFormal.NearV3.Assembly.tableBusCount_append, nodeStub_count_off h1 h2, Nat.add_zero]

/-- **`uniqD1` off `GB` is `uniqV3`.** -/
theorem uniqD1_count_base {t b : Nat} (h1 : b ≠ B_GB) (s : Bool) (m : List Fp) :
    tableBusCount uniqD1.interactions tr t pub b s m =
      tableBusCount ZkFormal.NearV3.Uniq.interactions tr t pub b s m := by
  rw [show uniqD1.interactions = ZkFormal.NearV3.Uniq.interactions ++ UniqGap.interactions from rfl,
    ZkFormal.NearV3.Assembly.tableBusCount_append, uniqGap_count_off h1, Nat.add_zero]

end ZkFormal.NearV3.D1
