import ZkFormal.NearV3.D1.Extract.WalkU.Proof2
import ZkFormal.NearV3.D1.Extract.UvalProof
import ZkFormal.NearV3.D1.Extract.KibD1Proof
import ZkFormal.NearV3.D1.Extract.ExtBuses

/-!
# `ZkFormal.NearV3.D1.Extract.ViewsUnread` — the unread-key tables' views on a `nearAirV3D1` trace

Lane `v3-d1-a7b` (plan §5 R-5 → (B)): `walkU` (30), `uvalV3` (32), `kibD1` (27) from
`HoldsP nearAirV3D1`, as `ViewsD1` for the D0a tables.  (`nodeD1` / `uniqD1`: `ExtBuses`.)
-/

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

variable {pub : List Fp} {tr : Trace Fp}

theorem walkUViewD1 (h : HoldsP nearAirV3D1 pub tr) :
    ∃ ws, WalkUWf ws ∧ ZkFormal.Near.TableTraffic WalkU.interactions tr T_WALKU pub (walkUTraffic ws) :=
  walkU_view tr pub T_WALKU (walkULocal h)

theorem uvalViewD1 (h : HoldsP nearAirV3D1 pub tr) :
    ∃ es, UvalWf es ∧ ZkFormal.Near.TableTraffic UvalV3.interactions tr T_UVAL pub (uvalTraffic es) :=
  uval_view tr pub T_UVAL (uvalLocal h)

theorem kibD1ViewD1 (h : HoldsP nearAirV3D1 pub tr) :
    ∃ es, KibD1Wf es ∧ ZkFormal.Near.TableTraffic KibD1.interactions tr T_KIB pub (kibD1Traffic es) :=
  kibD1_view tr pub T_KIB (kibLocal h)

end ZkFormal.NearV3.D1
