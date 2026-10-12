import ZkFormal.NearV3.Render.Padded
import ZkFormal.NearV3.Qv.Candidates.CombinedTraffic
import ZkFormal.NearV3.Qv.Candidates.CombinedWordAggregate
import ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair

/-!
# Concrete aligned generator for the queue-value table `qvV3`

`nearAirV3` table 22 is `Qv.Candidates.KeyTrafficRepair.table`: the combined queue
parser (`CombinedTable`) with its four `KEYNIB` sends replaced by three zero-based ones
(no `START`; nibble `2·pos`, `2·pos+1`; `END` at `2·pos+2`).  The honest rows are the
existing mixed queue rows (`mixedTrace (plan pre v pres resolve) vs log`: the read-plan
walks, then the value records), at the aligned height `padLog22 (logOf rows)`.

* local: the constraints are `CombinedTable`'s (`KeyTrafficRepair.local_of_base` of
  `mixedTrace_table_local`);
* traffic `repairedTraffic ws vs`: the walk word traffic with the repaired key words
  (`Walk.repairedKeyWordMessages`, the native `Qv.Extract.repairedKeyTraffic` shape) plus the
  canonical record traffic; every bus other than the `KEYNIB` sends is `mixedTraffic`'s.

The mixed trace reads the same rows for every table index, so the statements hold at any
index `t`.
-/
namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ValueGen NearSpec

/-! ## The repaired key sends of one walk row -/

/-- The three repaired `KEYNIB` sends. -/
def repairedKeyInteractions : List Interaction := (KeyTrafficRepair.interactions.drop 5).take 3

theorem repaired_key_filter (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic KeyTrafficRepair.interactions tr t r pub B_KEYNIB true =
      rowTraffic repairedKeyInteractions tr t r pub B_KEYNIB true := by
  simp [rowTraffic,KeyTrafficRepair.interactions,repairedKeyInteractions,CombinedTable.interactions,
    Dsl.send,Dsl.recv,B_KEYNIB,B_VBYTES,B_QSH,B_FINAL,ValueTable.B_QVC]

theorem Walk.repaired_key_nat_bits (w : Walk) (pos : Nat) (b : UInt8) :
    ∀ i ∈ repairedKeyInteractions, (∀ e ∈ i.mult,
      rowNatExpr e=true ∧ rowNatEval (w.row pos b) e≤1) ∧
      (∀ e ∈ i.msg, rowNatExpr e=true) := by
  simp [repairedKeyInteractions,KeyTrafficRepair.interactions,CombinedTable.interactions,
    Dsl.send,Dsl.recv,rowNatExpr,rowNatEval,CombinedTable.wid,CombinedTable.nibble,
    CombinedTable.wf,CombinedTable.wl,CombinedTable.walk,CombinedTable.wp,ValueTable.reg,
    Dsl.c,Dsl.k,Dsl.smul,Dsl.sum,List.range_succ]
  cases (pos+1 == w.kind.bytes.length) <;> decide

/-- The repaired key messages of walk row `pos` (byte `b`). -/
def Walk.repairedKeyMessages (w : Walk) (pos : Nat) (b : UInt8) : List Msg :=
  let wid := W_QV+w.tau+64*w.slot
  [[wid,2*pos,b.toNat/16,0],[wid,2*pos+1,b.toNat%16,0]] ++
  (if pos+1=w.kind.bytes.length then [[wid,2*pos+2,SYM_END,1]] else [])

theorem Walk.repaired_key_messages (w : Walk) (pos : Nat) (b : UInt8) :
    natRowTraffic repairedKeyInteractions (w.row pos b) B_KEYNIB true =
      w.repairedKeyMessages pos b := by
  have hi := w.high_nibble pos b
  have lo := w.low_nibble pos b
  simp only [repairedKeyInteractions,KeyTrafficRepair.interactions,CombinedTable.interactions,
    List.drop,List.take,List.append,natRowTraffic,List.flatMap_cons,List.flatMap_nil,Dsl.send,
    Dsl.recv,natMultBits,List.map_cons,List.map_nil]
  simp [CombinedTable.wf,CombinedTable.wl,CombinedTable.walk,CombinedTable.wp,
    CombinedTable.wid,CombinedTable.slot,ValueTable.tau,Dsl.c,Dsl.k,Dsl.smul,Dsl.sum,
    rowNatEval,Walk.repairedKeyMessages] at hi lo ⊢
  by_cases hl : pos+1=w.kind.bytes.length <;>
    simp [hl,hi,lo,Nat.add_assoc,natMultBits,rowNatEval,Walk.cell37,Walk.cell44]

theorem Walk.repaired_key_field_messages (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c, tr.cell t r c = Fp.ofNat ((w.row pos b).getD c 0)) :
    rowTraffic KeyTrafficRepair.interactions tr t r pub B_KEYNIB true =
      (w.repairedKeyMessages pos b).map Msg.toFp := by
  rw [repaired_key_filter,
    rowTraffic_nat _ _ _ _ _ _ hc (w.repaired_key_nat_bits pos b) _ _, w.repaired_key_messages]

/-! ## Words -/

theorem flatMap_congr_mem' {α β : Type} (xs : List α) (f g : α → List β)
    (h : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- The repaired key word of a walk: its nibbles at positions `0, 1, …`, then `END`. -/
def Walk.repairedKeyWordMessages (w : Walk) : List Msg :=
  let wid := W_QV+w.tau+64*w.slot
  (nibbles w.kind.bytes).zipIdx.map (fun ni => [wid,ni.2,ni.1,0]) ++
    [[wid,2*w.kind.bytes.length,SYM_END,1]]

theorem Walk.repaired_key_word_messages (w : Walk) :
    w.kind.bytes.zipIdx.flatMap (fun bi => w.repairedKeyMessages bi.2 bi.1) =
      w.repairedKeyWordMessages := by
  cases hk : w.kind <;>
    simp [Walk.repairedKeyMessages,Walk.repairedKeyWordMessages,Kind.bytes,hk,u64,leN,
      List.range_succ,List.zipIdx,nibbles]

/-- Aggregation of placed walks, for any interaction list. -/
theorem placed_words_traffic_is (is : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (bus : Nat) (sd : Bool) (ws : List Walk) (start : Nat) (msgs : Walk → List (List Fp))
    (hc : ∀ r<(ws.flatMap Walk.rows).length, ∀ c,
      tr.cell t (start+r) c=Fp.ofNat (((ws.flatMap Walk.rows).getD r []).getD c 0))
    (hword : ∀ w ∈ ws, ∀ off,
      (∀ bi ∈ w.kind.bytes.zipIdx, ∀ c,
        tr.cell t (off+bi.2) c=Fp.ofNat ((w.row bi.2 bi.1).getD c 0)) →
      w.kind.bytes.zipIdx.flatMap (fun bi =>
        rowTraffic is tr t (off+bi.2) pub bus sd)=msgs w) :
    (List.range (ws.flatMap Walk.rows).length).flatMap (fun r =>
      rowTraffic is tr t (start+r) pub bus sd)=ws.flatMap msgs := by
  induction ws generalizing start with
  | nil => simp
  | cons w ws ih =>
    have hcw : ∀ bi ∈ w.kind.bytes.zipIdx, ∀ c,
        tr.cell t (start+bi.2) c=Fp.ofNat ((w.row bi.2 bi.1).getD c 0) := by
      intro bi hbi c
      have he := List.mem_zipIdx_iff_getElem?.mp hbi
      have hp : bi.2<w.kind.bytes.length := by
        have := List.getElem?_eq_some_iff.mp he
        exact this.1
      rw [hc bi.2 (by simp only [List.flatMap_cons,List.length_append,Walk.rows_length]; omega) c]
      simp only [List.flatMap_cons,append_getD_left w.rows (ws.flatMap Walk.rows) bi.2 [] (by simpa [Walk.rows_length] using hp),
        Walk.rows_at w bi.2 hp,List.getD_eq_getElem?_getD,he,Option.getD_some]
    have htail : ∀ r<(ws.flatMap Walk.rows).length, ∀ c,
        tr.cell t (start+w.kind.bytes.length+r) c=
          Fp.ofNat (((ws.flatMap Walk.rows).getD r []).getD c 0) := by
      intro r hr c
      rw [show start+w.kind.bytes.length+r=start+(w.rows.length+r) by rw [Walk.rows_length]; omega]
      rw [hc _ (by simp only [List.flatMap_cons,List.length_append]; omega) c]
      simp only [List.flatMap_cons,append_getD_offset]
    have ht := ih (start+w.kind.bytes.length) htail (fun v hv => hword v (by simp [hv]))
    have hh := hword w (by simp) start hcw
    rw [zipIdx_flatMap_positions w.kind.bytes (fun j => rowTraffic is tr t (start+j) pub bus sd)] at hh
    simp only [List.flatMap_cons,List.length_append,Walk.rows_length,List.range_add,
      List.flatMap_append,List.flatMap_map]
    rw [hh]
    simpa only [Nat.add_assoc] using congrArg (fun xs => msgs w++xs) ht

/-! ## The whole table -/

/-- Word traffic with the repaired key sends. -/
def Walk.repairedWordMessages (w : Walk) (bus : Nat) (sd : Bool) : List Msg :=
  if bus=B_KEYNIB ∧ sd=true then w.repairedKeyWordMessages else w.wordMessages bus sd

/-- **The honest traffic of `qvV3`** (`KeyTrafficRepair.interactions`). -/
def repairedTraffic (ws : List Walk) (vs : List Record) : Traffic where
  sends := fun bus => ws.flatMap (fun w => w.repairedWordMessages bus true) ++ (canonicalTraffic vs).sends bus
  recvs := fun bus => ws.flatMap (fun w => w.repairedWordMessages bus false) ++ (canonicalTraffic vs).recvs bus

theorem repaired_key_recv_eq (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic KeyTrafficRepair.interactions tr t r pub B_KEYNIB false =
      rowTraffic CombinedTable.interactions tr t r pub B_KEYNIB false := by
  simp [rowTraffic,KeyTrafficRepair.interactions,CombinedTable.interactions,
    Dsl.send,Dsl.recv,B_KEYNIB,B_VBYTES,B_QSH,B_FINAL,ValueTable.B_QVC]

theorem repaired_rows_eq (tr : Trace Fp) (t r : Nat) (pub : List Fp) (bus : Nat) (sd : Bool)
    (h : ¬ (bus=B_KEYNIB ∧ sd=true)) :
    rowTraffic KeyTrafficRepair.interactions tr t r pub bus sd =
      rowTraffic CombinedTable.interactions tr t r pub bus sd := by
  by_cases hb : bus=B_KEYNIB
  · subst hb
    have hs : sd=false := by cases sd <;> simp_all
    subst hs
    exact repaired_key_recv_eq tr t r pub
  · exact KeyTrafficRepair.other_bus tr t r pub bus hb sd

/-- A row whose `walk` and `wl` flags are zero emits no repaired key message. -/
theorem repaired_key_silent (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hw : tr.cell t r CombinedTable.walk = 0) (hl : tr.cell t r CombinedTable.wl = 0) :
    rowTraffic KeyTrafficRepair.interactions tr t r pub B_KEYNIB true = [] := by
  rw [KeyTrafficRepair.key_row, hw, hl]
  simp

theorem mixedTrace_repaired_key (ws : List Walk) (vs : List Record) (log : Nat) (pub : List Fp)
    (hfit : (ws.flatMap Walk.rows).length+recordsSize vs≤2^log) :
    (List.range (2^log)).flatMap (fun r =>
      rowTraffic KeyTrafficRepair.interactions (mixedTrace ws vs log) 0 r pub B_KEYNIB true) =
      (ws.flatMap Walk.repairedKeyWordMessages).map Msg.toFp := by
  have he : 2^log=(ws.flatMap Walk.rows).length+(2^log-(ws.flatMap Walk.rows).length) := by omega
  have hrange := congrArg List.range he
  rw [List.range_add] at hrange
  rw [hrange,List.flatMap_append,List.flatMap_map]
  have hz : (List.range (2^log-(ws.flatMap Walk.rows).length)).flatMap (fun j =>
      rowTraffic KeyTrafficRepair.interactions (mixedTrace ws vs log) 0
        ((ws.flatMap Walk.rows).length+j) pub B_KEYNIB true) = [] := by
    refine List.flatMap_eq_nil_iff.2 fun j _ => ?_
    apply repaired_key_silent
    · rw [mixedTrace_suffix]; exact recordsCell_high vs j _ (by decide)
    · rw [mixedTrace_suffix]; exact recordsCell_high vs j _ (by decide)
  rw [hz,List.append_nil]
  have hc := mixedTrace_prefix (F:=Fp) ws vs log 0
  have h := placed_words_traffic_is KeyTrafficRepair.interactions (mixedTrace ws vs log) 0 pub
    B_KEYNIB true ws 0 (fun w => w.repairedKeyWordMessages.map Msg.toFp)
    (by simpa only [Nat.zero_add,PrefixCells,natCast_eq] using hc)
    (fun w _ off hcw => by
      calc _ = w.kind.bytes.zipIdx.flatMap (fun bi => (w.repairedKeyMessages bi.2 bi.1).map Msg.toFp) :=
            flatMap_congr_mem' _ _ _ (fun bi hi =>
              w.repaired_key_field_messages bi.2 bi.1 _ 0 _ pub (hcw bi hi))
        _ = _ := by rw [← List.map_flatMap,w.repaired_key_word_messages])
  simpa only [Nat.zero_add,List.map_flatMap] using h

theorem flatMap_range_congr {β : Type} (n : Nat) (f g : Nat → List β) (h : ∀ r, f r = g r) :
    (List.range n).flatMap f = (List.range n).flatMap g := by
  rw [show f = g from funext h]

/-- **The honest mixed queue rows have the repaired traffic** under `KeyTrafficRepair`. -/
theorem mixedTrace_repaired_traffic (ws : List Walk) (vs : List Record)
    (hv : ∀ v ∈ vs,v.Valid) (hs : ∀ w ∈ ws,w.kind.code=3 → 3≤w.slot)
    (log : Nat) (pub : List Fp)
    (hfit : (ws.flatMap Walk.rows).length+recordsSize vs≤2^log) :
    TableTraffic KeyTrafficRepair.interactions (mixedTrace ws vs log) 0 pub (repairedTraffic ws vs) := by
  have key : ∀ bus sd, ((List.range (2^log)).flatMap (fun r =>
      rowTraffic KeyTrafficRepair.interactions (mixedTrace ws vs log) 0 r pub bus sd)).Perm
      ((if sd then (repairedTraffic ws vs).sends bus else (repairedTraffic ws vs).recvs bus).map Msg.toFp) := by
    intro bus sd
    by_cases hk : bus=B_KEYNIB ∧ sd=true
    · obtain ⟨rfl, rfl⟩ := hk
      rw [mixedTrace_repaired_key ws vs log pub hfit]
      have hc : (canonicalTraffic vs).sends B_KEYNIB = [] := by
        simp [canonicalTraffic,B_KEYNIB,B_VBYTES,B_QSH,ValueTable.B_QVC]
      simp [repairedTraffic,Walk.repairedWordMessages,hc]
    · rw [flatMap_range_congr _ _ _ (fun r => repaired_rows_eq _ 0 r pub bus sd hk)]
      have hw : (fun w : Walk => w.repairedWordMessages bus sd) = (fun w => w.wordMessages bus sd) := by
        funext w; simp only [Walk.repairedWordMessages, if_neg hk]
      have he : (if sd then (repairedTraffic ws vs).sends bus else (repairedTraffic ws vs).recvs bus) =
          (if sd then (mixedTraffic ws vs).sends bus else (mixedTraffic ws vs).recvs bus) := by
        cases sd
        · have hw' := congrFun (congrArg (fun f => fun l : List Walk => l.flatMap f) hw) ws
          simp only [Bool.false_eq_true, ite_false, repairedTraffic, mixedTraffic]
          rw [show (fun w : Walk => w.repairedWordMessages bus false) = (fun w => w.wordMessages bus false) from hw]
        · simp only [ite_true, repairedTraffic, mixedTraffic]
          rw [show (fun w : Walk => w.repairedWordMessages bus true) = (fun w => w.wordMessages bus true) from hw]
      rw [he]
      exact mixedTrace_all_messages ws vs hv hs log pub bus sd hfit
  intro bus msg
  rw [tableBusCount_eq,tableBusCount_eq]
  exact ⟨(key bus true).count_eq msg, (key bus false).count_eq msg⟩

/-! ## Reindexing a table-independent trace -/

section reindex
variable {tr : Trace Fp} {t s : Nat} (hl : tr.log t = tr.log s) (hc : tr.cell t = tr.cell s)
include hl hc

theorem eval_reindex (e : Expr) (r : Nat) (pub : List Fp) : e.eval tr t r pub = e.eval tr s r pub := by
  have hh : tr.height t = tr.height s := by unfold Trace.height; rw [hl]
  unfold Expr.eval Expr.evalWith rowEnv
  simp only [hh, hc]

theorem rowTraffic_reindex (is : List Interaction) (r : Nat) (pub : List Fp) (b : Nat) (sd : Bool) :
    rowTraffic is tr t r pub b sd = rowTraffic is tr s r pub b sd := by
  unfold rowTraffic
  apply flatMap_congr_mem'
  intro i _
  have hm : i.multNat tr t r pub = i.multNat tr s r pub := by
    unfold Interaction.multNat
    have H : ∀ (l : List Expr) (k : Nat),
        Interaction.multNat.go tr t r pub l k = Interaction.multNat.go tr s r pub l k := by
      intro l; induction l with
      | nil => intro k; rfl
      | cons e es ih => intro k; simp only [Interaction.multNat.go]; rw [eval_reindex hl hc e r pub, ih (k+1)]
    exact H i.mult 0
  have hv : i.msgVal tr t r pub = i.msgVal tr s r pub := by
    unfold Interaction.msgVal
    apply List.map_congr_left; intro e _; exact eval_reindex hl hc e r pub
  rw [hm, hv]

theorem tableLocal_reindex {T : Air.Table} {pub : List Fp} (h : TableLocal T tr s pub) :
    TableLocal T tr t pub := by
  have hh : tr.height t = tr.height s := by unfold Trace.height; rw [hl]
  refine ⟨by rw [hl]; exact h.log_ge, by rw [hl]; exact h.log_le, ?_, ?_⟩
  · intro r hr e he; rw [eval_reindex hl hc]; exact h.constr r (by rw [← hh]; exact hr) e he
  · intro r hr i hi bb hb; rw [eval_reindex hl hc]; exact h.bits r (by rw [← hh]; exact hr) i hi bb hb

theorem tableTraffic_reindex {is : List Interaction} {pub : List Fp} {tf : Traffic}
    (h : TableTraffic is tr s pub tf) : TableTraffic is tr t pub tf := by
  have hh : tr.height t = tr.height s := by unfold Trace.height; rw [hl]
  intro b m
  rw [tableBusCount_eq, tableBusCount_eq, hh,
    flatMap_range_congr _ _ _ (fun r => rowTraffic_reindex hl hc is r pub b true),
    flatMap_range_congr _ _ _ (fun r => rowTraffic_reindex hl hc is r pub b false),
    ← tableBusCount_eq, ← tableBusCount_eq]
  exact h b m

end reindex

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen

namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Size
open ZkFormal.Near.Render ZkFormal.NearV3.Qv ZkFormal.NearV3.Qv.Candidates ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen

/-- Rows of the honest queue table: the read-plan walk rows, then the value records. -/
def qvRows (ws : List Walk) (vs : List ValueGen.Record) : Nat :=
  (ws.flatMap Walk.rows).length + ValueGen.recordsSize vs

def qvTraceAligned (pre : NearSpec.PTrie) (v : MainValues) (pres : List NearSpec.PTrie)
    (resolve : Resolve) (vs : List ValueGen.Record) : Trace Fp :=
  mixedTrace (plan pre v pres resolve) vs (padLog22 (logOf (qvRows (plan pre v pres resolve) vs)))

/-- What the honest queue table needs: valid main-queue values and records, the row bound,
and the public implicit-queue count (`PH` bytes `26..29`, read by `CombinedTable.kPublic`)
equal to the number of implicit pre-tries. -/
structure QvOk (pre : NearSpec.PTrie) (v : MainValues) (pres : List NearSpec.PTrie)
    (resolve : Resolve) (vs : List ValueGen.Record) (pub : List Fp) : Prop where
  valid : v.Valid
  records : ∀ x ∈ vs, x.Valid
  rows : qvRows (plan pre v pres resolve) vs ≤ 2 ^ 22
  pubCount : ∀ r, CombinedTable.kPublic.eval (qvTraceAligned pre v pres resolve vs) 0 r pub =
    @Nat.cast Fp Lean.Grind.Semiring.natCast pres.length

/-- **Queue-value table completeness at the aligned height** (cap `22`), for the repaired
key interface `KeyTrafficRepair.table` of `nearAirV3`, with traffic `repairedTraffic`. -/
theorem qv_aligned_complete (pre : NearSpec.PTrie) (v : MainValues) (pres : List NearSpec.PTrie)
    (resolve : Resolve) (vs : List ValueGen.Record) (pub : List Fp)
    (ok : QvOk pre v pres resolve vs pub) (t : Nat) :
    TableLocal KeyTrafficRepair.table (qvTraceAligned pre v pres resolve vs) t pub ∧
    TableTraffic KeyTrafficRepair.interactions (qvTraceAligned pre v pres resolve vs) t pub
      (repairedTraffic (plan pre v pres resolve) vs) ∧
    (qvTraceAligned pre v pres resolve vs).log t % 3 = 1 := by
  have hh := padded_log_fits _ ok.rows
  have hl : (qvTraceAligned pre v pres resolve vs).log t =
      (qvTraceAligned pre v pres resolve vs).log 0 := rfl
  have hc : (qvTraceAligned pre v pres resolve vs).cell t =
      (qvTraceAligned pre v pres resolve vs).cell 0 := rfl
  let d : Walk := ⟨.delayed, 0, 0, 0, none, 0, 0, false, false⟩
  have hL := mixedTrace_table_local pre v pres resolve ok.valid d vs ok.records _ pub
    ⟨hh.2.1, hh.2.2.1⟩ hh.1 ok.pubCount
  have hT := mixedTrace_repaired_traffic _ vs ok.records (plan_group_slot pre v pres resolve) _ pub hh.1
  exact ⟨tableLocal_reindex hl hc (KeyTrafficRepair.local_of_base hL),
    tableTraffic_reindex hl hc hT, hh.2.2.2⟩

end ZkFormal.NearV3.Render
