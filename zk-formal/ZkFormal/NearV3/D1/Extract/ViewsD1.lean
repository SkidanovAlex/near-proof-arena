import ZkFormal.NearV3.Assembly.ViewsV3
import ZkFormal.NearV3.D1.Extract.AirD1

/-!
# `ZkFormal.NearV3.D1.Extract.ViewsD1` — the unchanged per-table views on a `nearAirV3D1` trace

Lane `v3-d1-phase2` (milestone V6).  Every per-table view of `nearAirV3` is stated for any trace
and table index (`TableLocal T tr t pub → …`), and the tables at the indices below are the same
in `nearAirV3D1` (`getElem?_d1_same`), so the D0a theorems apply verbatim: this module only
re-instantiates `Assembly.ViewsV3` from `HoldsP nearAirV3D1`.  (`rcptV3D1` at 16 and `mrkV3` at
maxLog 20 at 23 are the changed tables, V4 / V5; the D1 tables are V1–V3.)
-/

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.NearV3.Assembly

variable {pub : List Fp} {tr : Trace Fp}

theorem nodeLocalD1 (h : HoldsP nearAirV3D1 pub tr) :
    ZkFormal.Near.TableLocal ZkFormal.NearV3.NodeV3.tableU tr T_NODE pub :=
  tableLocal_ext (tableLocalD1_same h (by decide) (by decide) (by decide) getElem?_node)
    (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h) (Nat.le_refl _)

theorem headLocalD1 (h : HoldsP nearAirV3D1 pub tr) :
    ZkFormal.Near.TableLocal {ZkFormal.NearV3.HeadV3.table with maxLog := 13} tr T_HEAD pub :=
  tableLocalD1_same h (by decide) (by decide) (by decide) getElem?_head

theorem valLocalD1 (h : HoldsP nearAirV3D1 pub tr) :
    ZkFormal.Near.TableLocal ZkFormal.NearV3.ValV3.table tr T_VAL pub :=
  tableLocal_ext (tableLocalD1_same h (by decide) (by decide) (by decide) getElem?_val)
    (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h) (Nat.le_refl _)

theorem walkLocalD1 (h : HoldsP nearAirV3D1 pub tr) :
    ZkFormal.Near.TableLocal {ZkFormal.NearV3.WalkV3.table with maxLog := 22} tr T_WALK pub :=
  tableLocalD1_same h (by decide) (by decide) (by decide) getElem?_walk

theorem uniqLocalD1 (h : HoldsP nearAirV3D1 pub tr) :
    ZkFormal.Near.TableLocal ZkFormal.NearV3.Uniq.table tr T_UNIQ pub :=
  tableLocalD1_same h (by decide) (by decide) (by decide) getElem?_uniq

theorem upsLocalD1 (h : HoldsP nearAirV3D1 pub tr) :
    ZkFormal.Near.TableLocal ZkFormal.NearV3.UpsV3.table tr T_UPS pub :=
  tableLocal_ext (tableLocalD1_same h (by decide) (by decide) (by decide) getElem?_ups)
    (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h) (Nat.le_refl _)

theorem acctLocalD1 (h : HoldsP nearAirV3D1 pub tr) :
    ZkFormal.Near.TableLocal acctTableV3 tr T_ACCT pub :=
  tableLocalD1_same h (by decide) (by decide) (by decide) getElem?_acct

theorem akeyLocalD1 (h : HoldsP nearAirV3D1 pub tr) :
    ZkFormal.Near.TableLocal ZkFormal.NearV3.AkeyV3.table tr T_AKEY pub :=
  tableLocalD1_same h (by decide) (by decide) (by decide) getElem?_akey

theorem bndLocalD1 (h : HoldsP nearAirV3D1 pub tr) :
    ZkFormal.Near.TableLocal ZkFormal.NearV3.BndV3.table tr T_BND pub :=
  tableLocalD1_same h (by decide) (by decide) (by decide) getElem?_bnd

theorem srcpLocalD1 (h : HoldsP nearAirV3D1 pub tr) :
    ZkFormal.Near.TableLocal ZkFormal.NearV3.SrcpDD.table tr T_SRCP pub :=
  tableLocalD1_same h (by decide) (by decide) (by decide) getElem?_srcp

theorem sizeLocalD1 (h : HoldsP nearAirV3D1 pub tr) :
    ZkFormal.Near.TableLocal {ZkFormal.NearV3.SizeV3.table with maxLog := 4} tr T_SIZE pub :=
  tableLocal_ext (tableLocalD1_same h (by decide) (by decide) (by decide) getElem?_size)
    (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h) (Nat.le_refl _)

/-! ## The views (as `Assembly.ViewsV3`, on a D1 trace) -/

theorem nodeViewD1 (h : HoldsP nearAirV3D1 pub tr) :
    ∃ vs, ZkFormal.NearV3.NodeWf3 vs ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.NodeV3.interactions tr T_NODE pub
        (ZkFormal.NearV3.nodeTraffic3 vs) :=
  ZkFormal.NearV3.node3_view tr pub T_NODE (nodeLocalD1 h)

theorem walkViewD1 (h : HoldsP nearAirV3D1 pub tr) :
    ∃ ws, ZkFormal.NearV3.WalkWf3 ws ∧ (ws.flatMap (·.steps)).length ≤ 2 ^ 22 ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.WalkV3.interactions tr T_WALK pub
        (ZkFormal.NearV3.walkTraffic3 ws) :=
  ZkFormal.NearV3.walk3_view_at 22 (by decide) tr pub T_WALK (walkLocalD1 h)

theorem headViewD1 (h : HoldsP nearAirV3D1 pub tr) :
    ∃ hs, ZkFormal.NearV3.HeadWf hs ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.HeadV3.interactions tr T_HEAD pub
        (ZkFormal.NearV3.headTraffic hs) :=
  ZkFormal.NearV3.head_view_at 13 (by decide) tr pub T_HEAD (headLocalD1 h)

theorem valViewD1 (h : HoldsP nearAirV3D1 pub tr) :
    ∃ es, ZkFormal.NearV3.ValWf es ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.ValV3.interactions tr T_VAL pub
        (ZkFormal.NearV3.valTraffic es) :=
  ZkFormal.NearV3.val_view tr pub T_VAL (valLocalD1 h)

theorem uniqViewD1 (h : HoldsP nearAirV3D1 pub tr) :
    ∃ es, ZkFormal.NearV3.UniqWf es ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.Uniq.interactions tr T_UNIQ pub
        (ZkFormal.NearV3.uniqTraffic es) :=
  ZkFormal.NearV3.uniq_view tr pub T_UNIQ (uniqLocalD1 h)

theorem upsViewD1 (h : HoldsP nearAirV3D1 pub tr) :
    ∃ u, ZkFormal.NearV3.UpsWf u ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.UpsV3.interactions tr T_UPS pub
        (ZkFormal.NearV3.upsTraffic u) :=
  ZkFormal.NearV3.ups_view tr pub T_UPS (upsLocalD1 h)

theorem acctViewD1 (h : HoldsP nearAirV3D1 pub tr) :
    ∃ as, ZkFormal.NearV3.AcctV3WfE 19 as ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.AcctV3.interactions tr T_ACCT pub
        (ZkFormal.NearV3.acctV3Traffic as) :=
  ZkFormal.NearV3.acctV3E_view_at 19 (by decide) tr pub T_ACCT (acctLocalD1 h)

theorem akeyViewD1 (h : HoldsP nearAirV3D1 pub tr) :
    ∃ es, ZkFormal.NearV3.AkeyWf es ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.AkeyV3.interactions tr T_AKEY pub
        (ZkFormal.NearV3.akeyTraffic es) :=
  ZkFormal.NearV3.akey_view tr pub T_AKEY (akeyLocalD1 h)

theorem bndViewD1 (h : HoldsP nearAirV3D1 pub tr) :
    ∃ es, ZkFormal.NearV3.BndWf es ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.BndV3.interactions tr T_BND pub
        (ZkFormal.NearV3.bndTraffic es) :=
  ZkFormal.NearV3.bnd_view tr pub T_BND (bndLocalD1 h)

theorem sizeViewD1 (h : HoldsP nearAirV3D1 pub tr) :
    ∃ v, ZkFormal.NearV3.SizeWf pub v ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.SizeV3.interactions tr T_SIZE pub
        (ZkFormal.NearV3.sizeTraffic v) :=
  ZkFormal.NearV3.size_view_at 4 (by decide) tr pub T_SIZE (sizeLocalD1 h)

end ZkFormal.NearV3.D1
