import ZkFormal.NearV3.D1.Extract.AirD1
import ZkFormal.NearV3.Assembly.ExtractV3

/-!
# `ZkFormal.NearV3.D1.Link.Index` — `nearAirV3D1`'s unchanged table indices (L1)

Lane `v3-d1-phase2`, item L1.  `Assembly.ExtractV3`'s `getElem?_…` lemmas for `nearAirV3D1`
(by `rfl`); the generated link copies (`D1/L`) use them in place of the originals
(`scripts/rcpt_d1_copy.py --profile link`, `refs`).
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.NearV3.Assembly ZkFormal.NearV3.D1

/-- Table 2 is `nodeD1` (`nodeA7` extended with the stub windows, lane v3-d1-a7b);
`ViewsD1.nodeA7LocalD1` gives `nodeA7`'s local legality. -/
theorem getElem?_node_d1 : nearAirV3D1.tables[T_NODE]? = some nodeD1 := rfl

theorem getElem?_head_d1 : nearAirV3D1.tables[T_HEAD]? =
    some {ZkFormal.NearV3.HeadV3.table with maxLog := 13} := rfl

theorem getElem?_val_d1 : nearAirV3D1.tables[T_VAL]? =
    some ZkFormal.NearV3.UnfoldA7.valA7 := rfl

theorem getElem?_walk_d1 : nearAirV3D1.tables[T_WALK]? =
    some {ZkFormal.NearV3.WalkV3.table with maxLog := 22} := rfl

/-- Table 6 is `uniqD1` (`uniqV3` extended with the gap lookups, lane v3-d1-a7b);
`ViewsD1.uniqLocalD1` gives `uniqV3`'s local legality. -/
theorem getElem?_uniq_d1 : nearAirV3D1.tables[T_UNIQ]? = some uniqD1 := rfl

theorem getElem?_ups_d1 : nearAirV3D1.tables[T_UPS]? =
    some ZkFormal.NearV3.UnfoldA7.upsA7 := rfl

theorem getElem?_acct_d1 : nearAirV3D1.tables[T_ACCT]? =
    some acctTableV3 := rfl

theorem getElem?_akey_d1 : nearAirV3D1.tables[T_AKEY]? =
    some ZkFormal.NearV3.AkeyV3.table := rfl

theorem getElem?_bnd_d1 : nearAirV3D1.tables[T_BND]? =
    some ZkFormal.NearV3.BndV3.table := rfl

theorem getElem?_srcp_d1 : nearAirV3D1.tables[T_SRCP]? =
    some ZkFormal.NearV3.SrcpDD.table := rfl

theorem getElem?_size_d1 : nearAirV3D1.tables[T_SIZE]? =
    some ZkFormal.NearV3.UnfoldA7.sizeA7 := rfl

theorem getElem?_sort_d1 : nearAirV3D1.tables[T_SORT]? =
    some sortTableV3 := rfl

end ZkFormal.NearV3.D1.Link
