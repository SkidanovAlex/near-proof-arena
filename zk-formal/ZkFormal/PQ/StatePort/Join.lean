import ZkFormal.PQ.StatePort.Bridge
import ZkFormal.NearV3.Assembly.NearAir
import ZkFormal.NearV3.D1.NearAirD1Defs

/-!
# ZkFormal.PQ.StatePort.Join — the bus partition for joining the classical state tables with direct-Wasm

Lane `pq-state-port`.  The plan (envelope study §6, and `pq-wasm-base` `results/pq-wasm-base/
STATEMENT.md` §2) is: **one base proof** containing both the classical NEAR state tables and the
direct-Wasm execution tables, joined on shared buses.

The two families already use disjoint bus id ranges, so the join needs no renaming inside either
family — only one constant, the offset this lane applies to every classical interaction:

* **direct-Wasm** (`WasmBase/Chips.lean`): `busState = 0`, `busFetch = 1`, `busStk = 2`,
  `busR16 = 3`, `busByte = 4`, `busData = 5`, `busFunc = 6`.  That is buses **0–6**.
* **classical state tables**: every interaction's bus is `< 128` (proved below by kernel
  evaluation on both AIRs), and the port shifts each to `128 + bus`, i.e. **128–199**.

So `BUS_OFFSET = 128` in the driver, and `busOffset` in the Lean tool, keep the two families apart
with the whole range 7–127 still free for the join's own glue tables.

## What is proved here

`nearAirV3_buses_below_128` and `nearAirV3D1_buses_below_128` — every classical bus is below 128,
so the translation `bus ↦ 128 + bus` cannot collide with the Wasm range 0–6 (or with any future
Wasm bus below 128).  This is the static side of the join; it is exactly the fact the driver's
`BUS_OFFSET` relies on.

## What is not proved here

The join itself — one proof whose public statement is `ctx ‖ enc S_0 ‖ enc S_S`, with `rcptD1`
sending the CALL message the Wasm `BOUNDARY` receives, and Wasm storage host calls answered on the
trie buses — is a composition over the *statement* layer, not a new AIR fact:

* the AIR side is: take the disjoint union of the two table sets (no bus renaming, proved above);
* the Lean side is a D3α-style receipt-level fold (`runCall` inside receipt application) over the
  D1 extraction and `wasm_base_sound`.

Cost estimate 15–25 agent-days (envelope study §6).  Nothing here changes either family's tables.
-/

namespace ZkFormal.PQ.StatePort

open ZkFormal.Air ZkFormal.V2 ZkFormal.NearV3

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- **The classical D0a buses fit below the join offset.** -/
theorem nearAirV3_buses_below_128 :
    (Assembly.nearAirV3.tables.all fun T =>
      T.interactions.all fun i => i.bus < 128) = true := by
  decide +kernel

/-- **The classical D1 buses fit below the join offset.** -/
theorem nearAirV3D1_buses_below_128 :
    (D1.nearAirV3D1.tables.all fun T =>
      T.interactions.all fun i => i.bus < 128) = true := by
  decide +kernel

/-- The direct-Wasm bus range.  `WasmBase/Chips.lean` uses `busState` … `busFunc` = 0–6; the HOST
chip (`lane/pq-host-chip`) adds `HOSTQ`/`HOSTR`/`HOSTT` = 7–9, so the family now reaches 9.  Kept
here as a constant so the partition is stated in one place on the classical side. -/
def wasmBusMax : Nat := 9

/-- **The partition.**  With the port's offset of 128, every translated classical bus is
`≥ 128`, and every Wasm bus is `≤ 9`; the two ranges can never meet. -/
theorem join_partition (bWasm bClassical : Nat)
    (hW : bWasm ≤ wasmBusMax) (hC : bClassical < 128) :
    bWasm ≠ 128 + bClassical := by
  -- `bClassical < 128` is enough here: `bWasm ≤ 9` and `128 + bClassical ≥ 128`.
  intro h
  have hwm : wasmBusMax = 9 := rfl
  have hW9 : bWasm ≤ 9 := hwm ▸ hW
  omega

/-- The largest classical bus actually used, across the 25-, 30- and 33-table exports.  `D0a` and
`D1` stop at 71; the 33-table a7b variant uses **72–75**, so 75 is the real bound (`< 128` alone is
too loose: it would allow 127, and `128 + 127 = 255`). -/
def classicalBusMax : Nat := 75

/-- **The host buses fit above both families.**  The classical range after `+128` reaches at most
`128 + 75 = 203`, so the cross-proof host buses start at 208.  This is the corrected allocation: an
earlier version of `JOIN-INTERFACE.md` put them at 200–202, which would have collided with classical
buses 72–74. -/
theorem host_buses_clear (bClassical bWasm : Nat)
    (hC : bClassical ≤ classicalBusMax) (hW : bWasm ≤ wasmBusMax) :
    bWasm < 208 ∧ 128 + bClassical < 208 := by
  have hwm : wasmBusMax = 9 := rfl
  have hcm : classicalBusMax = 75 := rfl
  have hW9 : bWasm ≤ 9 := hwm ▸ hW
  have hC75 : bClassical ≤ 75 := hcm ▸ hC
  have h1 : bWasm < 208 := by omega
  have h2 : 128 + bClassical < 208 := by omega
  exact ⟨h1, h2⟩

end ZkFormal.PQ.StatePort
