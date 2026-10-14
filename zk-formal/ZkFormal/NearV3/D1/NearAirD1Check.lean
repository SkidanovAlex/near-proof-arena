import ZkFormal.NearV3.D1.NearAirD1Defs
import ZkFormal.V2.G.Defs
import ZkFormal.Size.Aligned

/-!
# Static facts of `nearAirV3D1` (kernel evaluations)

Lane `v3-d1-tables`.  The side conditions the D1 admission certificate will need, as for
`nearAirV3` (`Assembly.NearAirCheckG2`, `Assembly.NearAirSize`): structural well-formedness
(columns, buses, degree ≤ 16, multiplicity bits, height caps, bus budgets with the public
messages), the P2 side condition at `auxGroup = 2`, and the aligned proof-size bound.
-/

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.V2 ZkFormal.Size

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem nearAirV3D1_wf : nearAirV3D1.wf 16 = true := by decide +kernel

theorem nearAirV3D1_air_wf : nearAirV3D1.toAir.wf 16 = true :=
  AirP.wf_air nearAirV3D1 16 nearAirV3D1_wf

theorem nearAirV3D1_npOkPg_g2 : ZkFormal.V2.G.NpOkPg nearAirV3D1 (ZkFormal.V2.G.pg 2) := by
  refine ⟨⟨⟨2, rfl, by decide, by decide⟩, ?_, ?_⟩, ?_⟩ <;> decide +kernel

/-- The aligned deduplicated proof-size bound of `nearAirV3D1` at `auxGroup = 2`
(`nearAirV3`: 6,435,489; the D1 tables and `mrkV3` at `maxLog 20` add 491,717 bytes). -/
theorem nearAirV3D1_sizeMaxAligned :
    sizeMaxAligned nearAirV3D1.toAir (ZkFormal.V2.G.pg 2) = 6927206 := by
  decide +kernel

end ZkFormal.NearV3.D1
