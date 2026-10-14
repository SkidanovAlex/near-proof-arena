import ZkFormal.NearV3.Assembly.NearAir
import ZkFormal.V2.G.Defs

/-!
# Static well-formedness of the assembled v3 AIR, at `auxGroup = 2`

`nearAirV3_wf` (with `nearAirV3_air_wf`) and the `auxGroup = 2` instance of the `NpOkPg` side
condition are what the admission certificate needs (`NearAdmission.nearAirV3_npOkPg_2`); both are
kernel evaluations on the concrete `nearAirV3`.  `Assembly.NearAirCheck` keeps the statement for every
`1 ≤ g ≤ 3` (`nearAirV3_npOkPg`), from this `g = 2` case and the `g = 1, 3` evaluations, outside the
certificate's import closure (docs/logs/v3-elab-budget-2026-10.md).
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.V2

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Structural well-formedness of every table (columns, buses, constraint degree
≤ 16, multiplicity bits, height caps, and the global bus budgets). -/
theorem nearAirV3_wf : nearAirV3.wf 16 = true := by decide +kernel

/-- The v1 side condition on the underlying AIR. -/
theorem nearAirV3_air_wf : nearAirV3.toAir.wf 16 = true :=
  AirP.wf_air nearAirV3 16 nearAirV3_wf

/-- P2 side conditions at `auxGroup = 2`. -/
theorem nearAirV3_npOkPg_g2 : ZkFormal.V2.G.NpOkPg nearAirV3 (ZkFormal.V2.G.pg 2) := by
  refine ⟨⟨⟨2, rfl, by decide, by decide⟩, ?_, ?_⟩, ?_⟩ <;> decide +kernel

end ZkFormal.NearV3.Assembly
