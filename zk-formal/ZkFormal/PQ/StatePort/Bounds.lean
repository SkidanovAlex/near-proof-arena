import ZkFormal.NearV3.Assembly.NearAir
import ZkFormal.NearV3.D1.NearAirD1Defs
import ZkFormal.V2.Air

/-!
# ZkFormal.PQ.StatePort.Bounds — the P2 side condition: `multBoundP < p`

Lane `pq-state-port`.  `AirP.multBoundP` is the static worst-case multiplicity of the classical
AIR, public messages included.  The SWIRL port uses LogUp, whose balance is **mod p**; it agrees
with the classical exact multiset balance precisely when both sides are `< p`.  Both `nearAirV3`
(D0a) and `nearAirV3D1` satisfy this, as kernel evaluations (`decide +kernel`), the same style as
`NearAirCheckG2.nearAirV3_wf` and `NearAirD1Check.nearAirV3D1_wf`.

The envelope study's figures are `multBoundP nearAirV3 = 924,245,270` and
`multBoundP nearAirV3D1 = 1,196,142,300` (phase-1 export), both below `p = 2,013,265,921`.  This
tree's `nearAirV3D1` carries the D1 additions, so its value differs; what is proved here is the
inequality that the bridge needs, not the concrete number.  The margin is at least 1.6x.
-/

namespace ZkFormal.PQ.StatePort

open ZkFormal.V2 ZkFormal.NearV3

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- **P2 for D0a**: the classical `nearAirV3` multiplicity bound is below the BabyBear prime. -/
theorem nearAirV3_multBoundP_lt : Assembly.nearAirV3.multBoundP < ZkFormal.Algebra.P := by
  decide +kernel

/-- **P2 for D1**: the classical `nearAirV3D1` multiplicity bound is below the BabyBear prime. -/
theorem nearAirV3D1_multBoundP_lt : D1.nearAirV3D1.multBoundP < ZkFormal.Algebra.P := by
  decide +kernel

end ZkFormal.PQ.StatePort
