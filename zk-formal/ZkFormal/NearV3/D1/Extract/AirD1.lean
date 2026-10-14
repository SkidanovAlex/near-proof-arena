import ZkFormal.Near.Extract.Common
import ZkFormal.NearV3.D1.NearAirD1Defs
import ZkFormal.V2.VerifierDefs

/-!
# `ZkFormal.NearV3.D1.Extract.AirD1` — table indices of `nearAirV3D1` and `TableLocal` from `HoldsP`

Lane `v3-d1-phase2` (docs/zk-formal/V3-D1-PHASE2.md, milestone V0).  The first, mechanical step of
`ExtractD1Stmt`, as `Assembly/ExtractV3.lean` for `nearAirV3`:

* `getElem?_d1_same`: every index `t < 25` other than `16` (`rcptV3D1`) and `23` (`mrkV3` at
  `maxLog 20`) holds the same table as in `nearAirV3`, so each D0a per-table view (stated for
  any trace and table index) applies to `nearAirV3D1` unchanged;
* the five D1 tables at `25 … 29` and the two replaced ones;
* `tableLocalD1`: `HoldsP nearAirV3D1 pub tr → TableLocal T tr t pub` for `tables[t]? = some T`.

Imports only definition modules (no D0a proof module), so the D1 closure stays small.
-/

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

def T_TX : Nat := 25
def T_AKM : Nat := 26
def T_KIB : Nat := 27
def T_PLF : Nat := 28
def T_RID : Nat := 29

/-- `HoldsP` gives the local legality of the table at index `t` (as `Assembly.tableLocal_of_holdsP`). -/
theorem tableLocalD1 {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (h : HoldsP AP pub tr) {t : Nat} {T : ZkFormal.Air.Table} (ht : AP.tables[t]? = some T) :
    ZkFormal.Near.TableLocal T tr t pub := by
  have hlt : t < AP.tables.length := by
    rcases Nat.lt_or_ge t AP.tables.length with hl | hl
    · exact hl
    · rw [List.getElem?_eq_none hl] at ht; cases ht
  have hT : AP.tables[t] = T := by
    rw [List.getElem?_eq_getElem hlt] at ht; exact Option.some.inj ht
  obtain ⟨h1, h2⟩ := h.logBound t hlt
  refine ⟨h1, hT ▸ h2, ?_, ?_⟩
  · intro r hr e he; exact h.constr t hlt r hr e (hT ▸ he)
  · intro r hr i hi b hb; exact h.bits t hlt r hr i (hT ▸ hi) b hb

theorem nearTablesFull_length : ZkFormal.NearV3.Assembly.nearTablesFull.length = 25 := rfl

theorem tables_d1 : nearAirV3D1.tables = nearTablesD1 := rfl

/-- **Unchanged tables.** -/
theorem getElem?_d1_same {t : Nat} (ht : t < 25) (h16 : t ≠ 16) (h23 : t ≠ 23) :
    nearAirV3D1.tables[t]? = ZkFormal.NearV3.Assembly.nearAirV3.tables[t]? := by
  rw [tables_d1, nearTablesD1, List.getElem?_append_left (by
      rw [List.length_set, List.length_set, nearTablesFull_length]; exact ht),
    List.getElem?_set_ne (Ne.symm h23), List.getElem?_set_ne (Ne.symm h16)]
  rfl

theorem getElem?_d1_rcpt : nearAirV3D1.tables[16]? = some RcptD1.tableQD1 := rfl
theorem getElem?_d1_mrk : nearAirV3D1.tables[23]? = some mrkTableD1 := rfl
theorem getElem?_d1_tx : nearAirV3D1.tables[T_TX]? = some TxV3.table := rfl
theorem getElem?_d1_akm : nearAirV3D1.tables[T_AKM]? = some AkmV3.table := rfl
theorem getElem?_d1_kib : nearAirV3D1.tables[T_KIB]? = some KibV3.table := rfl
theorem getElem?_d1_plf : nearAirV3D1.tables[T_PLF]? = some PlfV3.table := rfl
theorem getElem?_d1_rid : nearAirV3D1.tables[T_RID]? = some RidV3.table := rfl

theorem tables_d1_length : nearAirV3D1.tables.length = 30 := rfl

variable {pub : List Fp} {tr : Trace Fp}

/-- An unchanged table of `nearAirV3` keeps its local legality in a `nearAirV3D1` trace. -/
theorem tableLocalD1_same (h : HoldsP nearAirV3D1 pub tr) {t : Nat} {T : ZkFormal.Air.Table}
    (ht : t < 25) (h16 : t ≠ 16) (h23 : t ≠ 23)
    (hT : ZkFormal.NearV3.Assembly.nearAirV3.tables[t]? = some T) :
    ZkFormal.Near.TableLocal T tr t pub :=
  tableLocalD1 h ((getElem?_d1_same ht h16 h23).trans hT)

theorem txLocal (h : HoldsP nearAirV3D1 pub tr) : ZkFormal.Near.TableLocal TxV3.table tr T_TX pub :=
  tableLocalD1 h getElem?_d1_tx
theorem akmLocal (h : HoldsP nearAirV3D1 pub tr) : ZkFormal.Near.TableLocal AkmV3.table tr T_AKM pub :=
  tableLocalD1 h getElem?_d1_akm
theorem kibLocal (h : HoldsP nearAirV3D1 pub tr) : ZkFormal.Near.TableLocal KibV3.table tr T_KIB pub :=
  tableLocalD1 h getElem?_d1_kib
theorem plfLocal (h : HoldsP nearAirV3D1 pub tr) : ZkFormal.Near.TableLocal PlfV3.table tr T_PLF pub :=
  tableLocalD1 h getElem?_d1_plf
theorem ridLocal (h : HoldsP nearAirV3D1 pub tr) : ZkFormal.Near.TableLocal RidV3.table tr T_RID pub :=
  tableLocalD1 h getElem?_d1_rid
theorem rcptD1Local (h : HoldsP nearAirV3D1 pub tr) :
    ZkFormal.Near.TableLocal RcptD1.tableQD1 tr 16 pub :=
  tableLocalD1 h getElem?_d1_rcpt
theorem mrkD1Local (h : HoldsP nearAirV3D1 pub tr) : ZkFormal.Near.TableLocal mrkTableD1 tr 23 pub :=
  tableLocalD1 h getElem?_d1_mrk

end ZkFormal.NearV3.D1
