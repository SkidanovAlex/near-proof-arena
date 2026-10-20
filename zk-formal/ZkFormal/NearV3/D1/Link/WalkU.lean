import ZkFormal.NearV3.Extract.Ups.UpsWalk
import ZkFormal.NearV3.Assembly.LinkBus
import ZkFormal.NearV3.D1.Extract.ViewsUnread
import ZkFormal.NearV3.D1.Link.BusUsers

/-!
# `ZkFormal.NearV3.D1.Link.WalkU` — `walkU` on `EDGE` / `BMAP` (L1)

Lane `v3-d1-phase2`, item L1 (after the merge of lane `v3-d1-a7b`, milestone 2b).  Table 30
(`walkU`, the unread-key walks of R-5 → (B)) is a chain consumer on `EDGE` and `BMAP`; its traffic
on these buses is D0a's `walkSends3` / `walkRecvs3` of its records (`walkUTraffic`).  So D0a's
`WalkBal r.nodes r.heads r.walks r.ups b` (node, head, walk and ups traffic balance exactly) is
false in D1: the node records' edge counters also run through the unread walks.

* `WalkBalD vs hs ws v b`: D0a's `WalkBal` over the candidate walks **and** some unread walks
  `wx` (with `walkU`'s well-formedness `WalkUWf`, whose non-stub rows are D0a rows);
* `walkU_users_ok`: the users of `EDGE` / `BMAP` in `nearAirV3D1` are node, head, walk, ups and
  `walkU` (kernel `decide`);
* `walkU_count`: on `EDGE` / `BMAP`, `walkU`'s bus count is D0a's walk count of its records.

The balance itself (`walkBal_of_d1`) is in the generated `D1/L/Assembly/LinkBus` (override).
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.D1
open ZkFormal.NearV3.Assembly

/-- **The D1 walk balance on `EDGE` / `BMAP`**: D0a's `WalkBal` with the candidate walks `ws`
followed by some unread walks `wx` (the records of `walkU`). -/
def WalkBalD (vs : List NodeS3) (hs : List HeadE) (ws : List WalkR) (v : List ZkFormal.NearV3.UpsSeg)
    (b : Nat) : Prop :=
  ∃ wx, WalkUWf wx ∧ UpsRows.WalkBal vs hs (ws ++ wx) v b

theorem walkU_users_ok :
    UsersOkD1 B_EDGE [Assembly.T_NODE, Assembly.T_HEAD, Assembly.T_WALK, Assembly.T_UPS, T_WALKU] = true ∧
    UsersOkD1 ZkFormal.NearV3.B_BMAP [Assembly.T_NODE, Assembly.T_HEAD, Assembly.T_WALK, Assembly.T_UPS, T_WALKU] = true :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem isAtD1_walkU : isAtD1 T_WALKU = WalkU.interactions := rfl

/-- On `EDGE` / `BMAP`, `walkU`'s bus count is D0a's walk count of its records. -/
theorem walkU_count {pub : List Fp} {tr : Trace Fp} {wu : List WalkR}
    (tW : TableTraffic WalkU.interactions tr T_WALKU pub (walkUTraffic wu)) {b : Nat}
    (hb : b = B_EDGE ∨ b = ZkFormal.NearV3.B_BMAP) (s : Bool) (m : List Fp) :
    tableBusCount (isAtD1 T_WALKU) tr T_WALKU pub b s m = tcnt (walkTraffic3 wu) s b m := by
  rw [isAtD1_walkU, tcnt_of_traffic tW]
  cases s <;> simp only [tcnt, walkUTraffic, walkTraffic3, walkUSends, walkURecvs, if_pos hb,
    Bool.false_eq_true, ite_true, ite_false]

end ZkFormal.NearV3.D1.Link
