import ZkFormal.NearV3.Assembly.NearAirCheckG2

/-!
# Static well-formedness of the assembled v3 AIR

`nearAirV3_wf` and `nearAirV3_npOkPg` are the side conditions the admission
certificate needs; both are kernel evaluations on the concrete `nearAirV3`.  `nearAirV3_wf`,
`nearAirV3_air_wf` and the `g = 2` case (`nearAirV3_npOkPg_g2`, the one the certificate uses) live in
`Assembly.NearAirCheckG2`, which the certificate imports instead of this module.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.V2

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- P2 side conditions at `auxGroup = g` for `1 ≤ g ≤ 3`. -/
theorem nearAirV3_npOkPg (g : Nat) (hg1 : 1 ≤ g) (hg3 : g ≤ 3) :
    ZkFormal.V2.G.NpOkPg nearAirV3 (ZkFormal.V2.G.pg g) := by
  have hg : g = 1 ∨ g = 2 ∨ g = 3 := by omega
  rcases hg with rfl | rfl | rfl
  · refine ⟨⟨⟨1, rfl, by decide, by decide⟩, ?_, ?_⟩, ?_⟩ <;> decide +kernel
  · exact nearAirV3_npOkPg_g2
  · refine ⟨⟨⟨3, rfl, by decide, by decide⟩, ?_, ?_⟩, ?_⟩ <;> decide +kernel

end ZkFormal.NearV3.Assembly
