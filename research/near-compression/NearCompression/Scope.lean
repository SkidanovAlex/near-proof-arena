import NearSpecV3.D3.FunctionCall

/-! Arithmetic tied to the actual pinned D3 cap. These theorems do not convert
gas to interpreter steps: that requires a separate metering/resource proof. -/
namespace NearCompression

def targetGas : Nat := 1000000000000000

theorem legacy_gas_cap : NearSpecV3.D3.gAlpha = 3450888781824 := by decide

theorem target_exceeds_legacy : NearSpecV3.D3.gAlpha < targetGas := by decide

/-- 290 is a gas-capacity planning number, not a certified number of traces.
Host calls, zero-cost/control operations, memory and non-WASM work need bounds. -/
theorem gas_capacity_290 :
    NearSpecV3.D3.gAlpha * 289 < targetGas ∧
      targetGas ≤ NearSpecV3.D3.gAlpha * 290 := by constructor <;> decide

/-- A research relation for the cap extension only. It retains ALL other
D3 restrictions, and is therefore NOT full PV86 state-transition coverage.
No change to the frozen challenge or security profile is made. -/
def checkD3Peta (claim witness : NearSpec.Bytes) : Except String Unit :=
  NearSpecV3.checkD2Core (NearSpecV3.D3.d3Hooks NearSpecV3.Wasm.pv86)
    true claim witness (some targetGas)

end NearCompression
