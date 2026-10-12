import ZkFormal.NearV3.Qv.Extract.PhysicalEmptyRead
import ZkFormal.NearV3.Qv.Extract.PhysicalBufferedRead

/-!
# ZkFormal.NearV3.Rcpt.Link.QvRc — the physical queue reads over an abstract record-completeness premise

`Qv.Extract.physical_empty_read` / `physical_buffered_read` / `physical_count_read` assume a
**four-sender** `VBYTES` balance (qv + acct + akey = val).  In `nearAirV3` the codec also sends on
`VBYTES`, so that balance is not the AIR's.  The balance is used only through
`physical_balanced_record_complete` (each parser record's bytes are exactly the value record's
stream) and the SHA byte premise only through `value_bytes_of_sha` (`Bytes8` of the value records).

Here both are abstracted: `RecComplete` (record completeness of every nonempty parser record) and
`hb8 : ∀ e ∈ vals, Bytes8 e.bytes`; the reads are re-proved over them (same proofs).
`recComplete_of`: `RecComplete` from **any** start-closed set of other `VBYTES` senders
(`QvCodec` instantiates it with codec + acct + akey).
-/

namespace ZkFormal.NearV3.Qv.Extract.QvRc

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.ValueTable

/-- Every nonempty parser record of `segs` carries exactly the bytes of its value record. -/
def RecComplete (tr : Trace Fp) (tq : Nat) (pub : List Fp) (segs : List (Nat × Nat))
    (vals : List ValE) : Prop :=
  ∀ p ∈ segs, cv tr tq p.1 len ≠ 0 →
    (physicalRecordBytes tr tq p.1 p.2 pub).Perm
      (((valRecvs vals B_VBYTES).map Msg.toFp).filter
        (fun m => decide ((byteKey m).1 = tr.cell tq p.1 vid)))

/-- `RecComplete` from an exact `VBYTES` permutation whose non-qv senders are start-closed. -/
theorem recComplete_of {tr : Trace Fp} {tq : Nat} {pub : List Fp}
    (hL : TableLocal Candidates.CombinedTable.table tr tq pub)
    (q : WalkChain tr tq) (v : ParserChain tr tq (segEnd 0 q.segs))
    (vals : List ValE) (hv : ValWf vals) (others : List (List Fp)) (hcl : StartClosed others)
    (hglobal : (v.segs.flatMap (fun p => physicalRecordBytes tr tq p.1 p.2 pub) ++ others).Perm
      ((valRecvs vals B_VBYTES).map Msg.toFp)) :
    RecComplete tr tq pub v.segs vals := by
  intro p hp hn
  have hmove := (List.perm_cons_erase hp).flatMap_right
    (fun z => physicalRecordBytes tr tq z.1 z.2 pub)
  have hfinal := (hmove.append_right others).symm.trans hglobal
  have hb := seg_le_end v.segs (segEnd 0 q.segs) v.consecutive p hp
  have hfit : p.1+p.2≤tr.height tq := Nat.le_trans hb.2 v.fits
  have hw : ∀ r, p.1≤r → r<p.1+p.2 → tr.cell tq r Candidates.CombinedTable.walk=0 := by
    intro r hr hn
    exact zero_of_false hL (by omega) (x:=Candidates.CombinedTable.walk) (by simp [walkBools])
      (q.suffix r (by omega) (by omega))
  refine physical_record_complete hL hfit hw (v.valid p hp) hv hn
    ((v.segs.erase p).flatMap (fun z => physicalRecordBytes tr tq z.1 z.2 pub) ++ others) ?_
    (startClosed_append (physical_records_closed hL q v (v.segs.erase p)
      (fun z hz => List.mem_of_mem_erase hz)) hcl)
  simpa only [List.flatMap_cons, List.append_assoc] using hfinal

variable {tr : Trace Fp} {tq : Nat} {pub : List Fp}
  (hL : TableLocal Candidates.CombinedTable.table tr tq pub)
  (q : WalkChain tr tq) (v : ParserChain tr tq (segEnd 0 q.segs))
  {vals : List ValE} (hv : ValWf vals) (hrc : RecComplete tr tq pub v.segs vals)
  (hb8 : ∀ e ∈ vals, Bytes8 e.bytes)
include hL hv hrc hb8

theorem buffered_native (p : Nat × Nat) (hp : p∈v.segs) (hm : tr.cell tq p.1 mBuffer=1) :
    ∃ e∈vals, e.vz=false ∧ e.vid=cv tr tq p.1 vid ∧ e.len=p.2 ∧
      ∃ shards, BufferedValue (some (toBytes e.bytes)) shards ∧
        (List.range' p.1 p.2).flatMap (fun r =>
          rowTraffic Candidates.CombinedTable.interactions tr tq r pub B_QSH true)=
        Parser.nativeShardMessages (tr.cell tq p.1 tau) shards := by
  have hb := seg_le_end v.segs (segEnd 0 q.segs) v.consecutive p hp
  have hfit : p.1+p.2≤tr.height tq := Nat.le_trans hb.2 v.fits
  have hw : ∀ r, p.1≤r → r<p.1+p.2 → tr.cell tq r Candidates.CombinedTable.walk=0 := by
    intro r hr hn
    exact zero_of_false hL (by omega) (x:=Candidates.CombinedTable.walk) (by simp [walkBools])
      (q.suffix r (by omega) (by omega))
  have hs := v.valid p hp
  have hmin := (Parser.buffered_header_rows hL hfit hw hs hm 3 (by omega)).1
  have hn : cv tr tq p.1 len≠0 := by
    rcases Parser.length_cases hL hfit hw hs with h|h <;> omega
  exact buffered_native_record hL hfit hw hs hv hb8 (hrc p hp hn) hm

theorem empty_native (p : Nat × Nat) (hp : p∈v.segs) (hm : tr.cell tq p.1 mEmpty=1) :
    ∃ e∈vals, e.vz=false ∧ e.vid=cv tr tq p.1 vid ∧ e.len=16 ∧
      EmptyQueue (some (toBytes e.bytes)) := by
  have hb := seg_le_end v.segs (segEnd 0 q.segs) v.consecutive p hp
  have hfit : p.1+p.2≤tr.height tq := Nat.le_trans hb.2 v.fits
  have hw : ∀ r, p.1≤r → r<p.1+p.2 → tr.cell tq r Candidates.CombinedTable.walk=0 := by
    intro r hr hn
    exact zero_of_false hL (by omega) (x:=Candidates.CombinedTable.walk) (by simp [walkBools])
      (q.suffix r (by omega) (by omega))
  have hs := v.valid p hp
  have hmin := Parser.empty_row_count hL hfit hw hs hm
  have hn : cv tr tq p.1 len≠0 := by
    rcases Parser.length_cases hL hfit hw hs with h|h <;> omega
  exact empty_native_record hL hfit hw hs hv hb8 (hrc p hp hn) hm

theorem shard_all :
    ∃ shards : Nat × Nat → List Nat,
      (∀ p∈v.segs, tr.cell tq p.1 mBuffer=1 →
        ∃ e∈vals, e.vz=false ∧ e.vid=cv tr tq p.1 vid ∧ e.len=p.2 ∧
          BufferedValue (some (toBytes e.bytes)) (shards p)) ∧
      (List.range (tr.height tq)).flatMap
        (fun r => rowTraffic Candidates.CombinedTable.interactions tr tq r pub B_QSH true)=
      v.segs.flatMap (fun p => if tr.cell tq p.1 mBuffer=1 then
        Parser.nativeShardMessages (tr.cell tq p.1 tau) (shards p) else []) := by
  classical
  have hx : ∀ p : Nat × Nat, ∃ shards : List Nat,
      p∈v.segs → tr.cell tq p.1 mBuffer=1 →
        (∃ e∈vals, e.vz=false ∧ e.vid=cv tr tq p.1 vid ∧ e.len=p.2 ∧
          BufferedValue (some (toBytes e.bytes)) shards) ∧
        (List.range' p.1 p.2).flatMap (fun r =>
          rowTraffic Candidates.CombinedTable.interactions tr tq r pub B_QSH true)=
          Parser.nativeShardMessages (tr.cell tq p.1 tau) shards := by
    intro p
    by_cases hp : p∈v.segs
    · by_cases hm : tr.cell tq p.1 mBuffer=1
      · obtain ⟨e,he,hz,hid,hlen,ss,hbuf,hstream⟩ := buffered_native hL q v hv hrc hb8 p hp hm
        exact ⟨ss,fun _ _ => ⟨⟨e,he,hz,hid,hlen,hbuf⟩,hstream⟩⟩
      · exact ⟨[],fun _ hm' => False.elim (hm hm')⟩
    · exact ⟨[],fun hp' _ => False.elim (hp hp')⟩
  let shards := fun p => Classical.choose (hx p)
  have hshards := fun p => Classical.choose_spec (hx p)
  refine ⟨shards,fun p hp hm => (hshards p hp hm).1,?_⟩
  rw [shard_sends_suffix hL q, parser_shard_suffix hL q v true]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro p hp
  by_cases hm : tr.cell tq p.1 mBuffer=1
  · simpa only [hm,ite_true,List.flatMap_def,shards] using (hshards p hp hm).2
  · simpa only [hm,ite_false,List.flatMap_def] using nonbuffer_record_silent hL q v p hp hm true

theorem shard_balance_bounded
    (hqsh : ∀ m, tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QSH true m=
      tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QSH false m) :
    ∃ shards : Nat × Nat → List Nat,
      (∀ p∈v.segs, tr.cell tq p.1 mBuffer=1 →
        ∃ e∈vals, e.vz=false ∧ e.vid=cv tr tq p.1 vid ∧ e.len=p.2 ∧
          BufferedValue (some (toBytes e.bytes)) (shards p) ∧ (shards p).length<P) ∧
      ((List.range (segEnd 0 q.segs)).flatMap
        (fun r => rowTraffic Candidates.CombinedTable.interactions tr tq r pub B_QSH false)).Perm (
      v.segs.flatMap (fun p => if tr.cell tq p.1 mBuffer=1 then
        Parser.nativeShardMessages (tr.cell tq p.1 tau) (shards p) else [])) := by
  obtain ⟨ss,he,htotal⟩ := shard_all hL q v hv hrc hb8
  refine ⟨ss,?_,List.perm_iff_count.mpr ?_⟩
  · intro p hp hm
    obtain ⟨e,he,hz,hid,hlen,hbuf⟩ := he p hp hm
    have hend := seg_le_end v.segs (segEnd 0 q.segs) v.consecutive p hp
    have hfit : p.1+p.2≤tr.height tq := Nat.le_trans hend.2 v.fits
    exact ⟨e,he,hz,hid,hlen,hbuf,(physical_native_shard_bound hL hfit hv he hz hlen hbuf).2⟩
  · intro m
    have h := hqsh m
    rw [tableBusCount_eq,tableBusCount_eq,htotal,shard_receives_prefix hL q] at h
    exact h.symm

/-- `physical_empty_read` over `RecComplete` / `Bytes8`. -/
theorem empty_read
    (hqvc : ∀ m, tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QVC true m=
      tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QVC false m)
    (w : Nat × Nat) (hw : w∈q.segs)
    (hpresent : tr.cell tq w.1 Candidates.CombinedTable.absent=0)
    (hmode : cv tr tq w.1 len=0) :
    ∃ e∈vals, e.vz=false ∧ e.vid=cv tr tq w.1 vid ∧ e.len=16 ∧
      EmptyQueue (some (toBytes e.bytes)) := by
  obtain ⟨p,hp,hempty,hvid,-⟩ := physical_empty_provider_exists hL q v hqvc w hw hpresent hmode
  obtain ⟨e,he,hz,hid,hlen,hval⟩ := empty_native hL q v hv hrc hb8 p hp hempty
  exact ⟨e,he,hz,hid.trans hvid,hlen,hval⟩

/-- `physical_buffered_read` over `RecComplete` / `Bytes8`. -/
theorem buffered_read
    (hqsh : ∀ m, tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QSH true m=
      tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QSH false m)
    (hqvc : ∀ m, tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QVC true m=
      tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QVC false m)
    (w : Nat × Nat) (hw : w∈q.segs)
    (hpresent : tr.cell tq w.1 Candidates.CombinedTable.absent=0)
    (hmode : cv tr tq w.1 len=1) :
    ∃ e∈vals, e.vz=false ∧ e.vid=cv tr tq w.1 vid ∧
      ∃ shards, BufferedValue (some (toBytes e.bytes)) shards ∧ shards.length<P ∧
        ∀ m∈(List.range (segEnd 0 q.segs)).flatMap
          (fun r => rowTraffic Candidates.CombinedTable.interactions tr tq r pub B_QSH false),
          m∈Parser.nativeShardMessages (tr.cell tq w.1 tau) shards := by
  obtain ⟨p,hp,hbuf,hvid,htau⟩ := physical_buffered_provider_exists hL q v hqvc w hw hpresent hmode
  obtain ⟨ss,hrecords,hperm⟩ := shard_balance_bounded hL q v hv hrc hb8 hqsh
  obtain ⟨e,he,hz,hid,-,hnative,hbound⟩ := hrecords p hp hbuf
  have htfield : tr.cell tq p.1 tau=tr.cell tq w.1 tau := by
    have h := congrArg Fp.ofNat htau
    simpa only [cv,Fp.ofNat_toNat] using h
  refine ⟨e,he,hz,hid.trans hvid,ss p,hnative,hbound,?_⟩
  intro m hm
  rw [←htfield]
  exact unique_shard_member hL q v.segs ss hperm hp hbuf hm

/-- `physical_count_read` over `RecComplete` / `Bytes8`. -/
theorem count_read
    (hqsh : ∀ m, tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QSH true m=
      tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QSH false m)
    (hqvc : ∀ m, tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QVC true m=
      tableBusCount Candidates.CombinedTable.interactions tr tq pub B_QVC false m)
    (w : Nat × Nat) (hw : w∈q.segs)
    (hcount : tr.cell tq w.1 Candidates.CombinedTable.countRead=1) :
    ∃ e∈vals, e.vz=false ∧ e.vid=cv tr tq w.1 vid ∧
      ∃ shards, BufferedValue (some (toBytes e.bytes)) shards ∧ shards.length<P ∧
        cv tr tq w.1 count=shards.length ∧
        ∀ m∈(List.range (segEnd 0 q.segs)).flatMap
          (fun r => rowTraffic Candidates.CombinedTable.interactions tr tq r pub B_QSH false),
          m∈Parser.nativeShardMessages (tr.cell tq w.1 tau) shards := by
  have hend := seg_le_end q.segs 0 q.consecutive w hw
  have hn := (q.valid w hw).1
  have hrow : w.1<tr.height tq := by have := q.fits; omega
  have hprefix : w.1<segEnd 0 q.segs := by omega
  obtain ⟨hpresent,hmode⟩ := count_request_read_mode hL hrow hcount
  obtain ⟨e,he,hz,hid,ss,hbuf,hbound,hrequests⟩ :=
    buffered_read hL q v hv hrc hb8 hqsh hqvc w hw hpresent hmode
  have hreq := shard_count_request_mem tr tq w.1 (segEnd 0 q.segs) pub hprefix hcount
  have hcnt := Parser.native_shard_count_nat hbound (hrequests _ hreq)
  exact ⟨e,he,hz,hid,ss,hbuf,hbound,hcnt.2,hrequests⟩

end ZkFormal.NearV3.Qv.Extract.QvRc
