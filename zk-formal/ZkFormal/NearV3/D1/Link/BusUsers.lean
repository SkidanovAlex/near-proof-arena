import ZkFormal.NearV3.Assembly.LinkBus
import ZkFormal.NearV3.Assembly.NearAirBus
import ZkFormal.NearV3.D1.NearAirD1Defs

/-!
# `ZkFormal.NearV3.D1.Link.BusUsers` — the users of a bus in `nearAirV3D1` (L1)

Lane `v3-d1-phase2`, item L1.  D0a's `Assembly/LinkBus` reads `HoldsP.balance` per bus as a sum
over the bus's users, with the kernel-checked side condition `UsersOk b U` over `nearAirV3`'s 25
tables.  The generated copy (`D1/L/Assembly/LinkBus`) takes the `nearAirV3D1` forms:

* `busCount_nearAirV3D1`: `busCount nearAirV3D1` as the index-annotated sum of its tables;
* `UsersOkD1`, `isAtD1`: D0a's `UsersOk` / `isAt` over `nearTablesD1`.
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Assembly

/-- **`busCount` of `nearAirV3D1`** is the index-annotated sum of its tables. -/
theorem busCount_nearAirV3D1 (tr : Trace Fp) (pub : List Fp) (b : Nat) (s : Bool) (m : List Fp) :
    busCount nearAirV3D1.toAir tr pub b s m =
      (nearTablesD1.mapIdx fun (t : Nat) (T : ZkFormal.Air.Table) =>
        tableBusCount T.interactions tr t pub b s m).sum := by
  rw [busCount]
  change busCount.go tr pub b s m nearTablesD1 0 = _
  rw [busCount_go_eq]
  rw [mapIdx_congr nearTablesD1 (fun (i : Nat) (T : ZkFormal.Air.Table) => by rw [Nat.zero_add])]

/-- Every table of `nearAirV3D1` outside `U` has no interaction on bus `b`. -/
def UsersOkD1 (b : Nat) (U : List Nat) : Bool :=
  (List.range nearTablesD1.length).all fun t =>
    U.contains t || (nearTablesD1.getD t default).interactions.all fun i => i.bus != b

/-- The interactions of table `t` of `nearAirV3D1`. -/
def isAtD1 (t : Nat) : List Interaction := (nearTablesD1.getD t default).interactions

end ZkFormal.NearV3.D1.Link
