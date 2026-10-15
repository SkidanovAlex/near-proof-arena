import ZkFormal.Near.Extract.Common
import ZkFormal.NearV3.D1.NearAirD1Defs
import ZkFormal.V2.VerifierDefs

/-!
# `ZkFormal.NearV3.D1.Extract.AirD1` — table indices of `nearAirV3D1` and `TableLocal` from `HoldsP`

Lane `v3-d1-phase2` (docs/zk-formal/V3-D1-PHASE2.md, milestone V0).  The first, mechanical step of
`ExtractD1StmtT`, as `Assembly/ExtractV3.lean` for `nearAirV3`:

* `getElem?_d1_same`: every index `t < 25` other than `16` (`rcptV3D1`), `23` (`mrkV3` at
  `maxLog 20`), `2` (`nodeD1`) and `6` (`uniqD1`) holds the same table as in `nearAirV3`, so each
  D0a per-table view (stated for any trace and table index) applies to `nearAirV3D1` unchanged
  (`2`, `6` are extensions: their base views apply through `Assembly.tableLocal_ext`);
* the eight D1 tables at `25 … 32` and the four replaced ones;
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
def T_WALKU : Nat := 30
def T_NMEM : Nat := 31
def T_UVAL : Nat := 32

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

/-- **Unchanged tables.**  (`h2`, `h6`: the extended `nodeD1` / `uniqD1`, lane v3-d1-a7b; auto
parameters, so that literal-index callers are unchanged.) -/
theorem getElem?_d1_same {t : Nat} (ht : t < 25) (h16 : t ≠ 16) (h23 : t ≠ 23)
    (h2 : t ≠ 2 := by decide) (h6 : t ≠ 6 := by decide) :
    nearAirV3D1.tables[t]? = ZkFormal.NearV3.Assembly.nearAirV3.tables[t]? := by
  rw [tables_d1, nearTablesD1, List.getElem?_append_left (by
      rw [List.length_set, List.length_set, List.length_set, List.length_set,
        nearTablesFull_length]; exact ht),
    List.getElem?_set_ne (Ne.symm h6), List.getElem?_set_ne (Ne.symm h2),
    List.getElem?_set_ne (Ne.symm h23), List.getElem?_set_ne (Ne.symm h16)]
  rfl

theorem getElem?_d1_rcpt : nearAirV3D1.tables[16]? = some RcptD1.tableQD1 := rfl
theorem getElem?_d1_mrk : nearAirV3D1.tables[23]? = some mrkTableD1 := rfl
theorem getElem?_d1_node : nearAirV3D1.tables[2]? = some nodeD1 := rfl
theorem getElem?_d1_uniq : nearAirV3D1.tables[6]? = some uniqD1 := rfl
theorem getElem?_d1_tx : nearAirV3D1.tables[T_TX]? = some TxV3.table := rfl
theorem getElem?_d1_akm : nearAirV3D1.tables[T_AKM]? = some AkmV3.table := rfl
theorem getElem?_d1_kib : nearAirV3D1.tables[T_KIB]? = some KibD1.table := rfl
theorem getElem?_d1_plf : nearAirV3D1.tables[T_PLF]? = some PlfV3.table := rfl
theorem getElem?_d1_rid : nearAirV3D1.tables[T_RID]? = some RidV3.table := rfl
theorem getElem?_d1_walkU : nearAirV3D1.tables[T_WALKU]? = some WalkU.table := rfl
theorem getElem?_d1_nmem : nearAirV3D1.tables[T_NMEM]? = some NmemV3.table := rfl
theorem getElem?_d1_uval : nearAirV3D1.tables[T_UVAL]? = some UvalV3.table := rfl

theorem tables_d1_length : nearAirV3D1.tables.length = 33 := rfl

variable {pub : List Fp} {tr : Trace Fp}

/-- An unchanged table of `nearAirV3` keeps its local legality in a `nearAirV3D1` trace. -/
theorem tableLocalD1_same (h : HoldsP nearAirV3D1 pub tr) {t : Nat} {T : ZkFormal.Air.Table}
    (ht : t < 25) (h16 : t ≠ 16) (h23 : t ≠ 23)
    (hT : ZkFormal.NearV3.Assembly.nearAirV3.tables[t]? = some T)
    (h2 : t ≠ 2 := by decide) (h6 : t ≠ 6 := by decide) :
    ZkFormal.Near.TableLocal T tr t pub :=
  tableLocalD1 h ((getElem?_d1_same ht h16 h23 h2 h6).trans hT)

theorem txLocal (h : HoldsP nearAirV3D1 pub tr) : ZkFormal.Near.TableLocal TxV3.table tr T_TX pub :=
  tableLocalD1 h getElem?_d1_tx
theorem akmLocal (h : HoldsP nearAirV3D1 pub tr) : ZkFormal.Near.TableLocal AkmV3.table tr T_AKM pub :=
  tableLocalD1 h getElem?_d1_akm
theorem kibLocal (h : HoldsP nearAirV3D1 pub tr) : ZkFormal.Near.TableLocal KibD1.table tr T_KIB pub :=
  tableLocalD1 h getElem?_d1_kib
theorem nodeD1Local (h : HoldsP nearAirV3D1 pub tr) : ZkFormal.Near.TableLocal nodeD1 tr 2 pub :=
  tableLocalD1 h getElem?_d1_node
theorem uniqD1Local (h : HoldsP nearAirV3D1 pub tr) : ZkFormal.Near.TableLocal uniqD1 tr 6 pub :=
  tableLocalD1 h getElem?_d1_uniq
theorem walkULocal (h : HoldsP nearAirV3D1 pub tr) :
    ZkFormal.Near.TableLocal WalkU.table tr T_WALKU pub :=
  tableLocalD1 h getElem?_d1_walkU
theorem nmemLocal (h : HoldsP nearAirV3D1 pub tr) :
    ZkFormal.Near.TableLocal NmemV3.table tr T_NMEM pub :=
  tableLocalD1 h getElem?_d1_nmem
theorem uvalLocal (h : HoldsP nearAirV3D1 pub tr) :
    ZkFormal.Near.TableLocal UvalV3.table tr T_UVAL pub :=
  tableLocalD1 h getElem?_d1_uval
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
