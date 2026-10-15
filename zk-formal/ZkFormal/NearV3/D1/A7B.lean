import ZkFormal.NearV3.D1.NearAirD1Check
import ZkFormal.NearV3.D1.Extract.ViewsUnread
import ZkFormal.NearV3.D1.Extract.RidProof
import ZkFormal.NearV3.D1.Link.Records
import ZkFormal.NearV3.D1.Link.Statements
import ZkFormal.NearV3.D1.Prep.Spec
import ZkFormal.NearV3.D1.Public.Split

/-!
# `ZkFormal.NearV3.D1.A7B` — build root of lane v3-d1-a7b (plan §5 R-5 → (B))

The unread-key AIR (`nearAirV3D1`'s 33 tables, kernel facts), the views of the new and changed
tables, and the shared modules they touch.  `Phase2` imports it too; until the L1 lane adapts
its generated copies (`D1/L`, e.g. `LinkBus`) to the 33-table AIR, build this root.
-/
