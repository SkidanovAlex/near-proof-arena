import ZkFormal.NearV3.Rcpt.Link.QvCodec
import ZkFormal.NearV3.Rcpt.Link.AkeyAkc

/-!
# ZkFormal.NearV3.Rcpt.Link.ValExact — exact value records of the acct and akey `VBYTES` streams

`stream_record`: in an exact `VBYTES` permutation whose other senders are start-closed, a selected
nonempty stream `(k, i, b i)_{i<L}` **is** the whole value record `k` (length `L`, bytes `b`), and no
other sender uses id `k` (`Qv.Extract.stream_isolate` / `stream_other_id_ne`).

With the five-sender permutation (`vbytes_perm`):
* **`acct_value_exact`**: for an acct record `a`, the value record with `vid = a.k` has bytes exactly
  `a.pre` (so length `72`);
* **`akey_value_exact`**: for an akey record `e`, the value record with `vid = e.vid` has bytes exactly
  `e.bytes` (length `9`, byte `8` = `1`), and **no acct record has `k = e.vid`**;
* **`akk_value`**: for a receipt with `ee ∧ akf = 0`: the value record `akk` is 9 bytes with byte 8 = 1,
  and `akk` is no acct slot (`∀ a ∈ r.accts, a.k ≠ akk`).
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Assembly
  ZkFormal.NearV3.Assembly.LinkVBytes ZkFormal.NearV3.Qv.Extract ZkFormal.NearV3.Sched

/-- A selected nonempty stream of an exact, otherwise start-closed `VBYTES` permutation is a whole
value record, and its id is used by no other sender. -/
theorem stream_record {vals : List ValE} (hv : ValWf vals) (k L : Nat) (b : Nat → Nat)
    (hL : 0 < L) (hLP : L < P) (hk : k < P) (hb : ∀ i < L, b i < P)
    (others : List (List Fp)) (hcl : StartClosed others)
    (hbal : ((List.range L).map (fun i => Msg.toFp [k, i, b i]) ++ others).Perm
      ((valRecvs vals B_VBYTES).map Msg.toFp)) :
    (∃ e ∈ vals, e.vz = false ∧ e.vid = k ∧ e.bytes = (List.range L).map b) ∧
      ∀ m ∈ others, (byteKey m).1 ≠ Fp.ofNat k := by
  let stream := (List.range L).map (fun i => Msg.toFp [k, i, b i])
  have hstart : ∃ x ∈ stream, byteKey x = (Fp.ofNat k, 0) :=
    ⟨Msg.toFp [k, 0, b 0], List.mem_map.mpr ⟨0, List.mem_range.mpr hL, rfl⟩, rfl⟩
  have hselected : ∀ x ∈ stream, (byteKey x).1 = Fp.ofNat k := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    rfl
  have hne := stream_other_id_ne byteKey (Fp.ofNat k) stream others _ hbal
    (value_byte_keys_unique hv) hstart hcl
  have hiso := stream_isolate byteKey (Fp.ofNat k) stream others _ hbal
    (value_byte_keys_unique hv) hstart hselected hcl
  refine ⟨?_, hne⟩
  have h0mem : Msg.toFp [k, 0, b 0] ∈ stream := List.mem_map.mpr ⟨0, List.mem_range.mpr hL, rfl⟩
  have hmem := (List.mem_filter.mp (hiso.mem_iff.mp h0mem)).1
  obtain ⟨e, he, j, hj, hz, hid, -, -⟩ := value_byte_member hv hmem
  have heid : e.vid = k := by
    have h0 : (Fp.ofNat k).toNat = k := by rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt hk]
    exact hid.symm.trans h0
  have hb' : stream.Perm (valueRecordStream e) := by
    have hf := value_stream_filter hv e he
    simpa only [byteKey, ← heid, hf] using hiso
  have heqlen : e.bytes.length = L := by
    have h := hb'.length_eq
    simpa [stream, valueRecordStream, hz] using h.symm
  refine ⟨e, he, hz, heid, ?_⟩
  apply List.ext_getElem
  · simp [heqlen]
  intro i hi hi'
  have hiL : i < L := by omega
  have hm : Msg.toFp [k, i, b i] ∈ stream := List.mem_map.mpr ⟨i, List.mem_range.mpr hiL, rfl⟩
  have hmem := hb'.mem_iff.mp hm
  simp only [valueRecordStream, hz, Bool.false_eq_true, ite_false] at hmem
  obtain ⟨j, hj, heq⟩ := List.mem_map.mp hmem
  have hj' := List.mem_range.mp hj
  simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq] at heq
  have hji : j = i := Link3.ofNat_eq (by omega) (by omega) heq.2.1
  subst j
  have hb1 : e.bytes.getD i 0 < P := by
    simpa [List.getD_eq_getElem?_getD, hi] using (hv.canon e he).2.2.2 _ (List.getElem_mem hi)
  have hb2 := Link3.ofNat_eq hb1 (hb i hiL) heq.2.2.1
  simpa [List.getD_eq_getElem?_getD, hi] using hb2

theorem range_getD_map (l : List Nat) : (List.range l.length).map (fun i => l.getD i 0) = l := by
  apply List.ext_getElem
  · simp
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

section
variable {pub : List Fp} {tr : Trace Fp} {r : V3Records}
  (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r)
include hH T W

/-- **The acct's value record is exactly its pre bytes** (length 72). -/
theorem acct_value_exact {a : AcctV} (ha : a ∈ r.accts) :
    ∃ e ∈ r.values, e.vz = false ∧ e.vid = a.k ∧ e.bytes = a.pre := by
  have hQ : TableLocal Qv.Candidates.KeyTrafficRepair.table tr T_QV pub :=
    tableLocal_of_holdsP hH (t := T_QV) rfl
  have hl := Qv.Candidates.KeyTrafficRepair.local_to_base hQ
  obtain ⟨q⟩ := walk_chain_exists hl
  obtain ⟨pc⟩ := parser_chain_exists hl q
  have hw := W.accts.resolve_left (List.ne_nil_of_mem ha)
  obtain ⟨hpre, -, hk, -⟩ := hw.v1.len a ha
  have hcan := hw.v1.canon a ha
  obtain ⟨s, t, hst⟩ := List.append_of_mem ha
  let sel := (List.range a.pre.length).map (fun i => Msg.toFp [a.k, i, a.pre.getD i 0])
  let others := pc.segs.flatMap (fun p => Qv.Extract.physicalRecordBytes tr T_QV p.1 p.2 pub) ++
    codecV tr pub (List.range (tr.height T_CODEC)) ++ (acctV3Sends s B_VBYTES).map Msg.toFp ++
    (acctV3Sends t B_VBYTES).map Msg.toFp ++ (akeySends r.akeys B_VBYTES).map Msg.toFp
  have hsplit : (acctV3Sends r.accts B_VBYTES).map Msg.toFp =
      (acctV3Sends s B_VBYTES).map Msg.toFp ++ sel ++ (acctV3Sends t B_VBYTES).map Msg.toFp := by
    rw [hst]
    simp only [acctV3Sends, ite_true, List.flatMap_append, List.flatMap_cons, List.map_append, sel,
      emitAt_zero, List.map_map, List.append_assoc]
    rfl
  have hbal : (sel ++ others).Perm ((valRecvs r.values B_VBYTES).map Msg.toFp) := by
    refine List.Perm.trans ?_ (vbytes_perm hH T q pc)
    rw [hsplit]
    apply List.perm_iff_count.mpr
    intro m
    simp only [others, List.count_append]
    omega
  have hcl : StartClosed others :=
    startClosed_append (startClosed_append (startClosed_append (startClosed_append
      (physical_records_closed hl q pc pc.segs (fun _ h => h)) (codec_closed hH))
      (account_streams_closed s)) (account_streams_closed t)) (access_key_streams_closed r.akeys)
  have hbP : ∀ i < a.pre.length, a.pre.getD i 0 < P := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact hcan _ (List.mem_append_left _ (List.getElem_mem _))
  obtain ⟨⟨e, he, hz, hid, hb⟩, -⟩ := stream_record W.values a.k a.pre.length (fun i => a.pre.getD i 0)
    (by omega) (by unfold P; omega) hk hbP others hcl hbal
  exact ⟨e, he, hz, hid, by rw [hb, range_getD_map]⟩

/-- **The akey's value record is exactly its 9 bytes, and no acct record has its id.** -/
theorem akey_value_exact {e : AkeyE} (he : e ∈ r.akeys) :
    (∃ v ∈ r.values, v.vz = false ∧ v.vid = e.vid ∧ v.bytes = e.bytes) ∧
      ∀ a ∈ r.accts, a.k ≠ e.vid := by
  have hQ : TableLocal Qv.Candidates.KeyTrafficRepair.table tr T_QV pub :=
    tableLocal_of_holdsP hH (t := T_QV) rfl
  have hl := Qv.Candidates.KeyTrafficRepair.local_to_base hQ
  obtain ⟨q⟩ := walk_chain_exists hl
  obtain ⟨pc⟩ := parser_chain_exists hl q
  have hlen := W.akeys.len e he
  have hcan := W.akeys.canon e he
  obtain ⟨s, t, hst⟩ := List.append_of_mem he
  let sel := (List.range 9).map (fun i => Msg.toFp [e.vid, i, e.bytes.getD i 0])
  let others := pc.segs.flatMap (fun p => Qv.Extract.physicalRecordBytes tr T_QV p.1 p.2 pub) ++
    codecV tr pub (List.range (tr.height T_CODEC)) ++ (acctV3Sends r.accts B_VBYTES).map Msg.toFp ++
    (akeySends s B_VBYTES).map Msg.toFp ++ (akeySends t B_VBYTES).map Msg.toFp
  have hsplit : (akeySends r.akeys B_VBYTES).map Msg.toFp =
      (akeySends s B_VBYTES).map Msg.toFp ++ sel ++ (akeySends t B_VBYTES).map Msg.toFp := by
    rw [hst]
    simp only [akeySends, ite_true, List.flatMap_append, List.flatMap_cons, List.map_append, sel,
      List.map_map, List.append_assoc]
    rfl
  have hbal : (sel ++ others).Perm ((valRecvs r.values B_VBYTES).map Msg.toFp) := by
    refine List.Perm.trans ?_ (vbytes_perm hH T q pc)
    rw [hsplit]
    apply List.perm_iff_count.mpr
    intro m
    simp only [others, List.count_append]
    omega
  have hcl : StartClosed others :=
    startClosed_append (startClosed_append (startClosed_append (startClosed_append
      (physical_records_closed hl q pc pc.segs (fun _ h => h)) (codec_closed hH))
      (account_streams_closed r.accts)) (access_key_streams_closed s)) (access_key_streams_closed t)
  have hbP : ∀ i < 9, e.bytes.getD i 0 < P := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact hcan.2.2 _ (List.getElem_mem _)
  obtain ⟨⟨v, hv, hz, hid, hb⟩, hne⟩ := stream_record W.values e.vid 9 (fun i => e.bytes.getD i 0)
    (by omega) (by unfold P; omega) hcan.1 hbP others hcl hbal
  refine ⟨⟨v, hv, hz, hid, by rw [hb, ← hlen, range_getD_map]⟩, ?_⟩
  intro a ha hk
  have hpre := (LinkVPost.acct_wf W ha).1
  refine hne (Msg.toFp [a.k, 0, a.pre.getD 0 0]) ?_ (by rw [hk]; rfl)
  simp only [others, List.mem_append]
  left; left; right
  apply List.mem_map_of_mem
  simp only [acctV3Sends, ite_true]
  exact List.mem_flatMap.mpr ⟨a, ha, by rw [emitAt_zero]; exact List.mem_map.mpr ⟨0, by simp [hpre], rfl⟩⟩

/-- **The access key of a refund's `VAL` walk**: the value record `akk` is 9 bytes with byte 8 = 1
(FullAccess), and `akk` is no acct slot. -/
theorem akk_value {x : RcptE} (hx : x ∈ flatR r.lists) (hee : x.ee = true) (hf : x.akf = 0) :
    (∃ v ∈ r.values, v.vz = false ∧ v.vid = x.akk ∧ v.bytes.length = 9 ∧ v.bytes.getD 8 0 = 1) ∧
      ∀ a ∈ r.accts, a.k ≠ x.akk := by
  obtain ⟨e, hem, hv⟩ := akc_akey hH T W hx hee hf
  obtain ⟨⟨v, hvm, hz, hid, hb⟩, hne⟩ := akey_value_exact hH T W hem
  refine ⟨⟨v, hvm, hz, hid.trans hv, by rw [hb]; exact W.akeys.len e hem,
    by rw [hb]; exact W.akeys.last e hem⟩, fun a ha => hv ▸ hne a ha⟩

end

end ZkFormal.NearV3.RcptLink
