import ZkFormal.NearV3.Rcpt.Link.QvRc
import ZkFormal.NearV3.Assembly.LinkVBytes
import ZkFormal.NearV3.Assembly.LinkSha

/-!
# ZkFormal.NearV3.Rcpt.Link.QvCodec — the physical queue reads' premises from `HoldsP` (five `VBYTES` senders)

The `VBYTES` bus of `nearAirV3` has users val (receives), codec, acct, akey, qv (send).
* `codec_closed`: the codec's `VBYTES` sends are start-closed (every sending row is an encoding row
  of a block whose first row sends position `0` with the same `vid`: lane v3-link's
  `Codec.vrow_msg` / `codec_pre`);
* **`recComplete_holdsP`**: `QvRc.RecComplete` for the qv parser chain, from the exact five-sender
  balance (others = codec + acct + akey, all start-closed);
* `qsh_holdsP` / `qvc_holdsP`: the qv-internal `QSH` / `QVC` balances in base-table form;
* `bytes8_holdsP`: `Bytes8` of every value record, from the trie link's `ShaHyp` (SHA union).
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Assembly
  ZkFormal.NearV3.Assembly.LinkVBytes ZkFormal.NearV3.Qv.Extract ZkFormal.NearV3.Sched

/-- The codec's `VBYTES` sends are start-closed. -/
theorem codec_closed {pub : List Fp} {tr : Trace Fp} (hH : HoldsP nearAirV3 pub tr) :
    StartClosed (codecV tr pub (List.range (tr.height T_CODEC))) := by
  have hL := codec_local hH codecOwn
  have hH22 := codec_h22 hH codecOwn
  intro m hm
  obtain ⟨x, hx, hmx⟩ := List.mem_flatMap.mp hm
  have hxh := List.mem_range.mp hx
  rw [codec_row] at hmx
  obtain ⟨hmult, rfl⟩ := List.mem_replicate.mp hmx
  obtain ⟨f', -, hf', hF', hxf', hP', msgx⟩ := Codec.vrow_msg hL hH22 hxh hmult
  obtain ⟨-, V', -⟩ := Codec.codec_pre hL hH22 hf' hF'
  obtain ⟨m0, msg0⟩ := V' 0 (by omega)
  rw [Nat.add_zero] at m0 msg0
  refine ⟨(Codec.interactions[0]!).msgVal tr T_CODEC f' pub,
    List.mem_flatMap.mpr ⟨f', List.mem_range.mpr hf', by
      rw [codec_row]; exact List.mem_replicate.mpr ⟨by rw [m0, hP']; decide, rfl⟩⟩, ?_⟩
  rw [msg0, msgx]
  rfl

/-- qv bus counts in base-table (`CombinedTable`) form, off `KEYNIB`. -/
theorem qv_base_count {pub : List Fp} {tr : Trace Fp} {b : Nat} (hb : b ≠ B_KEYNIB) (s : Bool)
    (m : List Fp) :
    tableBusCount (isAt T_QV) tr T_QV pub b s m =
      tableBusCount Qv.Candidates.CombinedTable.interactions tr T_QV pub b s m := by
  rw [tableBusCount_eq, tableBusCount_eq]
  congr 1
  apply LinkVBytes.flatMap_congr'
  intro x _
  exact Qv.Candidates.KeyTrafficRepair.other_bus _ _ _ _ _ hb _

/-- **Record completeness** of the qv parser records from `HoldsP` (five-sender `VBYTES`). -/
theorem recComplete_holdsP {pub : List Fp} {tr : Trace Fp} {r : V3Records}
    (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r)
    (q : WalkChain tr T_QV) (pc : ParserChain tr T_QV (segEnd 0 q.segs)) :
    QvRc.RecComplete tr T_QV pub pc.segs r.values := by
  have hQ : TableLocal Qv.Candidates.KeyTrafficRepair.table tr T_QV pub :=
    tableLocal_of_holdsP hH (t := T_QV) rfl
  have hl := Qv.Candidates.KeyTrafficRepair.local_to_base hQ
  have hqv : (List.range (tr.height T_QV)).flatMap
      (fun x => rowTraffic (isAt T_QV) tr T_QV x pub B_VBYTES true) =
      pc.segs.flatMap (fun p => Qv.Extract.physicalRecordBytes tr T_QV p.1 p.2 pub) := by
    rw [← Qv.Extract.byte_all_physical hl q pc]
    apply LinkVBytes.flatMap_congr'
    intro x _
    exact Qv.Candidates.KeyTrafficRepair.other_bus _ _ _ _ _ (by decide) _
  let others : List (List Fp) :=
    codecV tr pub (List.range (tr.height T_CODEC)) ++
      (acctV3Sends r.accts B_VBYTES).map Msg.toFp ++ (akeySends r.akeys B_VBYTES).map Msg.toFp
  have v0 : valSends r.values B_VBYTES = [] := by simp [valSends, B_VBYTES, B_BYTES, B_ENT, B_SIZE]
  have a0 : acctRecvs r.accts B_VBYTES = [] := by simp [acctRecvs, B_VBYTES, B_MEM]
  have k0 : akeyRecvs r.akeys B_VBYTES = [] := by simp [akeyRecvs, B_AKC, B_VBYTES]
  have hbal : (pc.segs.flatMap (fun p => Qv.Extract.physicalRecordBytes tr T_QV p.1 p.2 pub) ++
      others).Perm ((valRecvs r.values B_VBYTES).map Msg.toFp) := by
    apply List.perm_iff_count.mpr
    intro M
    have h := bal_users hH (b := B_VBYTES) (U := [T_VAL, T_CODEC, Assembly.T_ACCT, T_AKEY, T_QV]) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) M
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
    rw [val_count T _ _ _ (by decide +kernel), val_count T _ _ _ (by decide +kernel),
      show isAt Assembly.T_ACCT = AcctV3.interactions from rfl, tcnt_of_traffic T.accts, tcnt_of_traffic T.accts,
      show isAt T_AKEY = AkeyV3.interactions from rfl, tcnt_of_traffic T.akeys, tcnt_of_traffic T.akeys,
      tableBusCount_noside (s := false) (is := isAt T_CODEC) (by decide +kernel),
      tableBusCount_noside (s := false) (is := isAt T_QV) (by decide +kernel),
      tableBusCount_eq (isAt T_CODEC), tableBusCount_eq (isAt T_QV), hqv] at h
    simp only [tcnt, ite_true, Bool.false_eq_true, ite_false, valTraffic, acctV3Traffic, akeyTraffic,
      v0, a0, k0, List.map_nil, List.count_nil, Nat.zero_add, Nat.add_zero] at h
    simp only [others, codecV, List.count_append] at h ⊢
    omega
  have hclosed : StartClosed others :=
    startClosed_append (startClosed_append (codec_closed hH) (account_streams_closed r.accts))
      (access_key_streams_closed r.akeys)
  exact QvRc.recComplete_of hl q pc r.values W.values others hclosed hbal

/-- The qv-internal `QSH` balance (base-table form). -/
theorem qsh_holdsP {pub : List Fp} {tr : Trace Fp} (hH : HoldsP nearAirV3 pub tr) (m : List Fp) :
    tableBusCount Qv.Candidates.CombinedTable.interactions tr T_QV pub B_QSH true m =
      tableBusCount Qv.Candidates.CombinedTable.interactions tr T_QV pub B_QSH false m := by
  have h := bal_users hH (b := B_QSH) (U := [T_QV]) (by decide) (by decide) (by decide +kernel)
    (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rwa [qv_base_count (by decide), qv_base_count (by decide)] at h

/-- The qv-internal `QVC` balance (base-table form). -/
theorem qvc_holdsP {pub : List Fp} {tr : Trace Fp} (hH : HoldsP nearAirV3 pub tr) (m : List Fp) :
    tableBusCount Qv.Candidates.CombinedTable.interactions tr T_QV pub
        Qv.Candidates.ValueTable.B_QVC true m =
      tableBusCount Qv.Candidates.CombinedTable.interactions tr T_QV pub
        Qv.Candidates.ValueTable.B_QVC false m := by
  have h := bal_users hH (b := Qv.Candidates.ValueTable.B_QVC) (U := [T_QV]) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rwa [qv_base_count (by decide), qv_base_count (by decide)] at h

/-- `Bytes8` of every value record, from the trie link's `ShaHyp` against the SHA union. -/
theorem bytes8_holdsP {pub : List Fp} {tr : Trace Fp} {r : V3Records}
    (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r)
    {others : List Msg}
    (S : Link3.ShaHyp r.nodes r.heads r.values others (shaU tr pub true) (shaU tr pub false)) :
    ∀ e ∈ r.values, Bytes8 e.bytes := by
  refine Qv.Extract.value_bytes_of_sha [T_SHA_T, T_SHA_R] ?_ r.values W.values T.values ?_
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact shaLocal_of_tableLocal (tableLocal_of_holdsP hH getElem?_sha_t)
    · exact shaLocal_of_tableLocal (tableLocal_of_holdsP hH getElem?_sha_r)
  · intro m
    have h := S.bytes m
    rw [tcnt_of_traffic T.values]
    change _ ≤ shaU tr pub false B_BYTES m
    rw [h]
    simp only [tcnt, ite_true, valTraffic, cnt, List.map_append, List.count_append]
    omega

end ZkFormal.NearV3.RcptLink
