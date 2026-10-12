import ZkFormal.NearV3.Assembly.LinkTrieFam
import ZkFormal.NearV3.Assembly.LinkFields
import ZkFormal.NearV3.Candidates.ProcessRepairReceiptReceiverShape
import ZkFormal.NearV3.Candidates.ProcessRepairReceiptFinalFields
import ZkFormal.NearV3.Rcpt.Link.QvBal
import ZkFormal.NearV3.Rcpt.Link.Keynib

/-!
# ZkFormal.NearV3.Assembly.LinkRcptWalk — each receipt's account walk (`nearAirV3`)

Receipt `i` (flattened, applied order) receives `FINAL [i, 0, FK_VAL, kslot]`; the walks are the
only `FINAL` senders (`RcptLink.qv_hfinal`), so a `walkV3` walk `wv` has `wv.w = i`, `wv.tau = 0`,
`wv.fk = FK_VAL`, `wv.k = kslot` (`rcpt_final`).  The walk's `KEYNIB` receives are rcpt or qv
sends (`LinkKeynib.keynib_bal`); qv walk ids are `≥ W_QV` and the receipt ids `< W_AK`
(`flatR_le`), so they are receipt `i`'s `keyMsgs i keySyms` (`walk_messages`), and the walk key
is `accountKeyPath receiver` (`rcpt_walk`; the pure step is the candidate lane's
`ProcessRepairReceiptWalkKey.symbols`).  With `LinkTrieFam.walk_reach`:

* **`rcpt_reach`** — `fullReach (Rpost …) (headAt 0).rid (accountKeyPath recv) = some kslot`
  (`vid0 = 0`, value ids are positions);
* **`rcpt_find`**, **`rcpt_set`** — the main trie family `Tf r 0 st v` (length-preserving `v`)
  finds / gets `v kslot` at the receiver's account key and `set` there updates slot `kslot`.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkRcptWalk

open ZkFormal.NearV3 ZkFormal.NearV3.Link3 ZkFormal.NearV3.UpsRows LinkImplicit LinkSched0 LinkTrieFam

section
variable {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
  {tr : Trace Fp} {r : V3Records}

/-- At most `W_AK` receipts (`n ≤ 5000`). -/
theorem flatR_le (hp : NearSpecV3.prepD0 cb h = .ok p)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    (flatR r.lists).length ≤ W_AK := by
  have hc := W.lists.count (fun i _ => pubNat_pubOf_lt _ _)
  rw [ZkFormal.NearV3.RcptV3Proof.prepared_receipt_count hp oh (prepD0_roots hp)] at hc
  have := (ZkFormal.NearV3.RcptV3Proof.prepD0_count_bound hp).1
  rw [hc]; unfold W_AK; omega

/-- Receipt `i`'s receiver: bytes, at most 64 of them; its slot is canonical. -/
theorem rcpt_shape {pub : List Fp} (W : V3RecordsWf pub r) {i : Nat} (hi : i < (flatR r.lists).length) :
    Bytes8 (flatR r.lists)[i].v ∧ (flatR r.lists)[i].v.length ≤ 64 ∧ (flatR r.lists)[i].kslot < P := by
  obtain ⟨toks, -, -, hwf, -⟩ := W.lists.toks
  have hW := hwf i hi
  have hvalid := hW.ids.2.1
  simp only [NearSpec.AccountId.valid, Bool.and_eq_true, decide_eq_true_eq, toBytes,
    List.length_map] at hvalid
  exact ⟨hW.ids.2.2.2.2.1, hvalid.1.2, hW.small.1⟩

/-- **`KEYNIB`**: the key receives of a walk with a receipt id are that receipt's `keyMsgs`. -/
theorem walk_messages (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {w : WalkR} (hw : w ∈ r.walks) (hr : w.w < (flatR r.lists).length) :
    ∀ j, 1 ≤ j → j < w.steps.length →
      (Msg.toFp [w.w, j - 1, (w.step j).sym, if j + 1 = w.steps.length then 1 else 0]) ∈
      (RcptE.keyMsgs w.w ((flatR r.lists).getD w.w default).keySyms).map Msg.toFp := by
  intro j hj hj'
  have hn := flatR_le (oh := oh) hp W
  let m : Msg := [w.w, j - 1, (w.step j).sym, if j + 1 = w.steps.length then 1 else 0]
  have hm : m ∈ walkRecvs3 r.walks B_KEYNIB := by
    unfold walkRecvs3
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl, List.mem_flatMap]
    refine ⟨w, hw, List.mem_map.mpr ⟨j - 1, List.mem_range.mpr (by omega), ?_⟩⟩
    simp only [m, show j - 1 + 1 = j by omega, show j - 1 + 2 = j + 1 by omega]
  have hc : 0 < ((walkRecvs3 r.walks B_KEYNIB).map Msg.toFp).count (Msg.toFp m) :=
    List.count_pos_iff.mpr (List.mem_map_of_mem hm)
  rw [LinkKeynib.keynib_bal hH T] at hc
  rcases Nat.eq_zero_or_pos (((rcptSends3 _ r.lists B_KEYNIB).map Msg.toFp).count (Msg.toFp m)) with h0 | h0
  · -- a qv send: its walk id is `≥ W_QV`
    rw [h0, Nat.zero_add] at hc
    have hq := List.count_pos_iff.mp hc
    have hQ : TableLocal Qv.Candidates.KeyTrafficRepair.table tr T_QV
        (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) :=
      tableLocal_of_holdsP hH (t := T_QV) rfl
    obtain ⟨q⟩ := Qv.Extract.walk_chain_exists (Qv.Candidates.KeyTrafficRepair.local_to_base hQ)
    rw [LinkKeynib.qvKeys, show isAt T_QV = Qv.Candidates.KeyTrafficRepair.interactions from rfl,
      Qv.Extract.repaired_key_physical hQ q] at hq
    obtain ⟨pp, hpp, hpmsg⟩ := List.mem_flatMap.mp hq
    obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hpp
    subst pp
    have hid := Qv.Extract.repaired_key_owner _ _ hpmsg
    obtain ⟨n, hn0, hnP, he⟩ :=
      Qv.Extract.queue_walk_id_range (Qv.Candidates.KeyTrafficRepair.local_to_base hQ) q i hi
    rw [he] at hid
    change Fp.ofNat w.w = Fp.ofNat n at hid
    have hwP : w.w < P := by unfold W_AK P at *; omega
    have hh := Link.ofNat_inj hwP hnP hid
    unfold W_AK W_QV at *
    omega
  · -- a receipt send with id `w.w`: receipt `w.w`'s account key messages
    obtain ⟨mr, hmr, he⟩ := List.mem_map.mp (List.count_pos_iff.mp h0)
    have hrange := Qv.Extract.receipt_key_id_range hn hmr
    have hid := congrArg (fun xs : List Fp => xs.getD 0 0) he
    change (mr.map Fp.ofNat).getD 0 (Fp.ofNat 0) = Fp.ofNat w.w at hid
    rw [Link3.getD_map'] at hid
    have hidNat : mr.getD 0 0 = w.w := Link.ofNat_inj (by unfold W_QV P at *; omega)
      (by unfold W_AK P at *; omega) hid
    exact List.mem_map.mpr
      ⟨mr, Candidates.ProcessRepairReceiptKeyOwner.account_owner hn hr hmr hidNat, he⟩

/-- **`FINAL`**: receipt `i`'s account-walk receive is sent by a walk of `walkV3`. -/
theorem rcpt_final
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {i : Nat} (hi : i < (flatR r.lists).length) (hiP : i < P) :
    ∃ wv ∈ r.walks, wv.w = i ∧ wv.tau = 0 ∧ wv.fk = FK_VAL ∧ wv.k = (flatR r.lists)[i].kslot := by
  have hmem : [i, 0, FK_VAL, (flatR r.lists)[i].kslot] ∈ rcptRecvs3 r.lists B_FINAL := by
    unfold rcptRecvs3
    rw [LinkRids.located_flat r.lists (fun r x => rRecvs r x B_FINAL)]
    refine List.mem_flatMap.mpr ⟨((flatR r.lists)[i], i), ?_, ?_⟩
    · have hz : i < ((flatR r.lists).zipIdx).length := by simpa using hi
      have := List.getElem_mem hz
      simpa [List.getElem_zipIdx] using this
    · simp [rRecvs, show B_FINAL ≠ B_DIGEST by decide]
  have hperm := RcptLink.qv_hfinal hH T
  have hin : Msg.toFp [i, 0, FK_VAL, (flatR r.lists)[i].kslot] ∈
      (walkSends3 r.walks B_FINAL).map Msg.toFp :=
    hperm.mem_iff.mpr (List.mem_append_right _ (List.mem_map_of_mem hmem))
  obtain ⟨mw, hmw, he⟩ := List.mem_map.mp hin
  have hws : walkSends3 r.walks B_FINAL = r.walks.map fun wv => [wv.w, wv.tau, wv.fk, wv.k] := by
    simp [walkSends3, B_EDGE, B_BMAP, B_FINAL]
  rw [hws] at hmw
  obtain ⟨wv, hwv, rfl⟩ := List.mem_map.mp hmw
  exact ⟨wv, hwv, Candidates.ProcessRepairReceiptFinalFields.fields W.walks hwv hiP
    (rcpt_shape W hi).2.2 he⟩

/-- **Receipt `i`'s account walk**: a `VAL` walk of instance `0` to its slot, keyed by the
receiver's account key. -/
theorem rcpt_walk (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {i : Nat} (hi : i < (flatR r.lists).length) :
    ∃ wv ∈ r.walks, wv.w = i ∧ wv.tau = 0 ∧ wv.fk = FK_VAL ∧ wv.k = (flatR r.lists)[i].kslot ∧
      wv.key3 = NearSpec.accountKeyPath (toBytes (flatR r.lists)[i].v) := by
  have hn := flatR_le (oh := oh) hp W
  have hiP : i < P := by unfold W_AK P at *; omega
  obtain ⟨wv, hwv, hw, ht, hf, hk⟩ := rcpt_final hH T W hi hiP
  refine ⟨wv, hwv, hw, ht, hf, hk, ?_⟩
  obtain ⟨hb, hsize, -⟩ := rcpt_shape W hi
  obtain ⟨hlen, hcanon, hkey⟩ :=
    Candidates.ProcessRepairReceiptReceiverShape.native_key (flatR r.lists)[i] hb hsize
  have hget : (flatR r.lists).getD wv.w default = (flatR r.lists)[i] := by
    rw [hw]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hm := walk_messages hp hH T W hwv (by rw [hw]; exact hi)
  rw [hget] at hm
  exact (Candidates.ProcessRepairReceiptWalkKey.symbols W.walks hwv _ hlen hcanon hm).2.trans hkey

/-- Value ids are positions: the record at `vpos (vid0 es) k` has id `k`. -/
theorem vid_vpos {es : List ValE} (hvw : ValWf es) {k : Nat} (hk : k < P)
    (ht : vpos (vid0 es) k < es.length) : es[vpos (vid0 es) k].vid = k := by
  rw [vid_at hvw (vlen_le hvw) _ ht, vpos, Nat.add_mod_mod]
  have ha : vid0 es < P := by
    unfold vid0; cases es with
    | nil => simp at ht
    | cons e _ => simpa using (hvw.canon e (by simp)).1
  rw [show vid0 es + (k + P - vid0 es) = k + P by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hk]

/-- **Receipt `i`'s account key reaches its slot** in instance `0`'s record tree. -/
theorem rcpt_reach (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {i : Nat} (hi : i < (flatR r.lists).length) :
    fullReach (Rpost r.nodes r.values) (headAt r.heads 0).rid
        (NearSpec.accountKeyPath (toBytes (flatR r.lists)[i].v)) =
      some (vpos (vid0 r.values) (flatR r.lists)[i].kslot) ∧
    ∃ hlt : vpos (vid0 r.values) (flatR r.lists)[i].kslot < r.values.length,
      r.values[vpos (vid0 r.values) (flatR r.lists)[i].kslot].vid = (flatR r.lists)[i].kslot := by
  obtain ⟨wv, hwv, -, ht, hf, hk, hkey⟩ := rcpt_walk hp hH T W hi
  obtain ⟨hr, hlt⟩ := walk_reach hp hsz hH T W hwv hf
  rw [ht, hkey, hk] at hr
  rw [hk] at hlt
  exact ⟨hr, hlt, vid_vpos W.values (rcpt_shape W hi).2.2 hlt⟩

theorem accountKeyPath_ne (a : NearSpec.Bytes) : NearSpec.accountKeyPath a ≠ NearSpecV3.keyBwState := by
  intro he
  have := congrArg (fun l => l.getD 1 0) he
  simp [NearSpec.accountKeyPath, NearSpecV3.keyBwState, NearSpec.nibbles] at this

/-- **`get`/`find`** of the main trie family at receipt `i`'s account key. -/
theorem rcpt_find (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (h0 : 0 < p.sched.length) (st : NearSpec.Bytes)
    {i : Nat} (hi : i < (flatR r.lists).length) {v : Nat → NearSpec.Bytes} (hv : LenOk r v) :
    (Tf r 0 st v).find (NearSpec.accountKeyPath (toBytes (flatR r.lists)[i].v)) =
        some (some (v (flatR r.lists)[i].kslot)) ∧
      (Tf r 0 st v).get (NearSpec.accountKeyPath (toBytes (flatR r.lists)[i].v)) =
        some (v (flatR r.lists)[i].kslot) := by
  obtain ⟨hr, hlt, hid⟩ := rcpt_reach hp hsz hH T W hi
  have := Tf_find hp hsz hH T W h0 (Nat.zero_le _) st (accountKeyPath_ne _) hr hlt hv
  rwa [hid] at this

/-- **`set`** of the main trie family at receipt `i`'s account key (same length). -/
theorem rcpt_set (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (h0 : 0 < p.sched.length) (st : NearSpec.Bytes)
    {i : Nat} (hi : i < (flatR r.lists).length) {v : Nat → NearSpec.Bytes} (hv : LenOk r v)
    {b : NearSpec.Bytes} (hb : b.length = (v (flatR r.lists)[i].kslot).length) :
    (Tf r 0 st v).set (NearSpec.accountKeyPath (toBytes (flatR r.lists)[i].v)) b =
      some (Tf r 0 st (fun k => if k = (flatR r.lists)[i].kslot then b else v k)) := by
  obtain ⟨hr, hlt, hid⟩ := rcpt_reach hp hsz hH T W hi
  have := Tf_set hp hsz hH T W h0 (Nat.zero_le _) st (accountKeyPath_ne _) hr hlt hv
    (b := b) (by rw [hid]; exact hb.symm)
  rwa [hid] at this

/-! ## The access-key walk of a gas refund (`ee`) -/

/-- A receipt's `KEYNIB` send with id `W_AK + i` is receipt `i`'s access-key message. -/
theorem ak_owner {pub : List Fp} {ls : RcptV3Vs} (hn : (flatR ls).length ≤ W_AK) {i : Nat}
    {m : Msg} (hm : m ∈ rcptSends3 pub ls B_KEYNIB) (hid : m.getD 0 0 = W_AK + i) :
    ((flatR ls).getD i default).ee = true ∧ m ∈ RcptE.keyMsgs (W_AK + i) ((flatR ls).getD i default).akSyms := by
  rw [LinkKeynib.rcptSends3_keynib] at hm
  obtain ⟨⟨x, q⟩, hxq, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨k, hk, hke⟩ := List.getElem_of_mem hxq
  have hk' : k < (flatR ls).length := by simpa using hk
  have hx : (flatR ls).zipIdx[k] = ((flatR ls)[k], k) := by simp [List.getElem_zipIdx]
  rw [hx] at hke
  simp only [Prod.mk.injEq] at hke
  obtain ⟨hx1, hq1⟩ := hke
  subst hx1; subst hq1
  rcases List.mem_append.mp hm with hm | hm
  · rw [Candidates.ProcessRepairReceiptKeyOwner.message_id _ _ hm] at hid
    unfold W_AK at *; omega
  · split at hm
    · rename_i hee
      rw [Candidates.ProcessRepairReceiptKeyOwner.message_id _ _ hm] at hid
      have : k = i := by omega
      subst this
      have hg : (flatR ls).getD k default = (flatR ls)[k] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
      rw [hg]; exact ⟨hee, hm⟩
    · simp at hm

/-- **`KEYNIB`** of the access-key walk: its key receives are receipt `i`'s `akSyms` messages. -/
theorem ak_messages (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {w : WalkR} (hw : w ∈ r.walks) {i : Nat} (hwi : w.w = W_AK + i) (hi : i < (flatR r.lists).length) :
    ∀ j, 1 ≤ j → j < w.steps.length →
      (Msg.toFp [w.w, j - 1, (w.step j).sym, if j + 1 = w.steps.length then 1 else 0]) ∈
      (RcptE.keyMsgs w.w ((flatR r.lists).getD i default).akSyms).map Msg.toFp := by
  intro j hj hj'
  have hn := flatR_le (oh := oh) hp W
  let m : Msg := [w.w, j - 1, (w.step j).sym, if j + 1 = w.steps.length then 1 else 0]
  have hm : m ∈ walkRecvs3 r.walks B_KEYNIB := by
    unfold walkRecvs3
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl, List.mem_flatMap]
    refine ⟨w, hw, List.mem_map.mpr ⟨j - 1, List.mem_range.mpr (by omega), ?_⟩⟩
    simp only [m, show j - 1 + 1 = j by omega, show j - 1 + 2 = j + 1 by omega]
  have hc : 0 < ((walkRecvs3 r.walks B_KEYNIB).map Msg.toFp).count (Msg.toFp m) :=
    List.count_pos_iff.mpr (List.mem_map_of_mem hm)
  rw [LinkKeynib.keynib_bal hH T] at hc
  have hwP : w.w < W_QV := by rw [hwi]; unfold W_AK W_QV at *; omega
  rcases Nat.eq_zero_or_pos (((rcptSends3 _ r.lists B_KEYNIB).map Msg.toFp).count (Msg.toFp m)) with h0 | h0
  · rw [h0, Nat.zero_add] at hc
    have hq := List.count_pos_iff.mp hc
    have hQ : TableLocal Qv.Candidates.KeyTrafficRepair.table tr T_QV
        (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) :=
      tableLocal_of_holdsP hH (t := T_QV) rfl
    obtain ⟨q⟩ := Qv.Extract.walk_chain_exists (Qv.Candidates.KeyTrafficRepair.local_to_base hQ)
    rw [LinkKeynib.qvKeys, show isAt T_QV = Qv.Candidates.KeyTrafficRepair.interactions from rfl,
      Qv.Extract.repaired_key_physical hQ q] at hq
    obtain ⟨pp, hpp, hpmsg⟩ := List.mem_flatMap.mp hq
    obtain ⟨k, hk, hpk⟩ := List.getElem_of_mem hpp
    subst pp
    have hid := Qv.Extract.repaired_key_owner _ _ hpmsg
    obtain ⟨n, hn0, hnP, he⟩ :=
      Qv.Extract.queue_walk_id_range (Qv.Candidates.KeyTrafficRepair.local_to_base hQ) q k hk
    rw [he] at hid
    change Fp.ofNat w.w = Fp.ofNat n at hid
    have hh := Link.ofNat_inj (by unfold W_QV P at *; omega) hnP hid
    omega
  · obtain ⟨mr, hmr, he⟩ := List.mem_map.mp (List.count_pos_iff.mp h0)
    have hrange := Qv.Extract.receipt_key_id_range hn hmr
    have hid := congrArg (fun xs : List Fp => xs.getD 0 0) he
    change (mr.map Fp.ofNat).getD 0 (Fp.ofNat 0) = Fp.ofNat w.w at hid
    rw [Link3.getD_map'] at hid
    have hidNat : mr.getD 0 0 = w.w := Link.ofNat_inj (by unfold W_QV P at *; omega)
      (by unfold W_QV P at *; omega) hid
    rw [hwi] at hidNat
    have := (ak_owner hn hmr hidNat).2
    rw [← hwi] at this
    exact List.mem_map.mpr ⟨mr, this, he⟩

theorem fields_ak {ws : List WalkR} (hW : WalkWf3 ws) {w : WalkR} (hw : w ∈ ws)
    {a f k : Nat} (ha : a < P) (hf : f ≤ 1) (hk : k < P)
    (he : Msg.toFp [w.w, w.tau, w.fk, w.k] = Msg.toFp [a, 0, f, k]) :
    w.w = a ∧ w.tau = 0 ∧ w.fk = f ∧ w.k = k := by
  have hc := hW.canon w hw
  have hlen := hW.len w hw
  have hlast := hc.2.2 w.last (Walk3.row_mem (by omega))
  have hfk : w.fk < P := by unfold WalkR.fk; split <;> decide
  have hval : w.k < P := by
    unfold WalkR.k
    split
    · exact Link.getD_lt hlast.2.2.2 _
    · unfold P; omega
  simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq] at he
  exact ⟨Link.ofNat_inj hc.1 ha he.1, Link.ofNat_inj hc.2.1 (by decide) he.2.1,
    Link.ofNat_inj hfk (by unfold P; omega) he.2.2.1, Link.ofNat_inj hval hk he.2.2.2.1⟩

theorem nib_len (l : List Nat) : (l.flatMap fun ch => [ch / 16, ch % 16]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.length_append, ih]; simp; omega

/-- The access-key path of the symbols `akSyms`. -/
theorem akSyms_key (x : RcptE) (hs : Bytes8 x.s) (hkt : x.kt ≤ 1) (hpk : Bytes8 x.pk) :
    x.akSyms.take (x.akSyms.length - 1) =
      NearSpecV3.keyAccessKey (toBytes x.s) ⟨x.kt, toBytes x.pk⟩ := by
  have hb : Bytes8 ([2] ++ x.s ++ [2] ++ [x.kt] ++ x.pk) := by
    intro c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((((hc | hc) | hc) | hc) | hc)
    · omega
    · exact hs c hc
    · omega
    · omega
    · exact hpk c hc
  have hu : NearSpec.u8 x.kt = toBytes [x.kt] := by
    rcases (show x.kt = 0 ∨ x.kt = 1 by omega) with e | e <;> rw [e] <;> decide
  unfold RcptE.akSyms NearSpecV3.keyAccessKey NearSpec.PublicKey.encode
  rw [List.length_append, List.length_singleton, Nat.add_sub_cancel, List.take_left' rfl,
    ← Link.nibbles_toBytes _ hb, hu]
  simp [toBytes]

/-- **The access-key walk of receipt `i`** (`ee`): a walk of instance `0`, kind `akf`, target
`akk`, keyed by the signer's access-key path. -/
theorem ak_walk (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {i : Nat} (hi : i < (flatR r.lists).length) (hee : (flatR r.lists)[i].ee = true) :
    ∃ wv ∈ r.walks, wv.tau = 0 ∧ wv.fk = (flatR r.lists)[i].akf ∧ wv.k = (flatR r.lists)[i].akk ∧
      wv.key3 = NearSpecV3.keyAccessKey (toBytes (flatR r.lists)[i].s)
        ⟨(flatR r.lists)[i].kt, toBytes (flatR r.lists)[i].pk⟩ := by
  have hn := flatR_le (oh := oh) hp W
  obtain ⟨toks, -, -, hwf, -⟩ := W.lists.toks
  have hWf := hwf i hi
  have hx : (flatR r.lists)[i] ∈ flatR r.lists := List.getElem_mem hi
  -- `FINAL`
  have hmem : [W_AK + i, 0, (flatR r.lists)[i].akf, (flatR r.lists)[i].akk] ∈ rcptRecvs3 r.lists B_FINAL := by
    unfold rcptRecvs3
    rw [LinkRids.located_flat r.lists (fun r x => rRecvs r x B_FINAL)]
    refine List.mem_flatMap.mpr ⟨((flatR r.lists)[i], i), ?_, ?_⟩
    · have hz : i < ((flatR r.lists).zipIdx).length := by simpa using hi
      have := List.getElem_mem hz
      simpa [List.getElem_zipIdx] using this
    · simp [rRecvs, show B_FINAL ≠ B_DIGEST by decide, hee]
  have hin : Msg.toFp [W_AK + i, 0, (flatR r.lists)[i].akf, (flatR r.lists)[i].akk] ∈
      (walkSends3 r.walks B_FINAL).map Msg.toFp :=
    (RcptLink.qv_hfinal hH T).mem_iff.mpr (List.mem_append_right _ (List.mem_map_of_mem hmem))
  obtain ⟨mw, hmw, he⟩ := List.mem_map.mp hin
  have hws : walkSends3 r.walks B_FINAL = r.walks.map fun wv => [wv.w, wv.tau, wv.fk, wv.k] := by
    simp [walkSends3, B_EDGE, B_BMAP, B_FINAL]
  rw [hws] at hmw
  obtain ⟨wv, hwv, rfl⟩ := List.mem_map.mp hmw
  obtain ⟨hw, ht, hf, hk⟩ := fields_ak W.walks hwv (by unfold W_AK P at *; omega) hWf.akf hWf.small.2.2.1 he
  refine ⟨wv, hwv, ht, hf, hk, ?_⟩
  -- `KEYNIB`
  have hvs := hWf.ids.2.2.1
  simp only [NearSpec.AccountId.valid, Bool.and_eq_true, decide_eq_true_eq, toBytes,
    List.length_map] at hvs
  have henc := LinkRidBytes.encBytes hp hsz hH T W _ hx
  have hpk : Bytes8 (flatR r.lists)[i].pk := fun c hc => henc c (by simp [RcptV.enc, hc])
  have hb : ∀ c ∈ [2] ++ (flatR r.lists)[i].s ++ [2] ++ [(flatR r.lists)[i].kt] ++ (flatR r.lists)[i].pk,
      c < 256 := by
    intro c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((((hc | hc) | hc) | hc) | hc)
    · omega
    · exact hWf.ids.2.2.2.2.2 c hc
    · omega
    · have := hWf.lens.2.2.1; omega
    · exact hpk c hc
  have hlen : (flatR r.lists)[i].akSyms.length < P := by
    simp only [RcptE.akSyms, List.length_append, nib_len, List.length_cons, List.length_nil]
    have := hWf.lens.2.1
    have := hWf.lens.2.2.1
    unfold P; omega
  have hcanon : ∀ a ∈ (flatR r.lists)[i].akSyms, a < P := by
    intro a ha
    rcases nib_syms _ hb a ha with e | e
    · unfold P; omega
    · rw [e]; decide
  have hget : (flatR r.lists).getD i default = (flatR r.lists)[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hm := ak_messages hp hH T W hwv hw hi
  rw [hget] at hm
  exact (Candidates.ProcessRepairReceiptWalkKey.symbols W.walks hwv _ hlen hcanon hm).2.trans
    (akSyms_key _ hWf.ids.2.2.2.2.2 hWf.lens.2.2.1 hpk)

/-- **An `ABS` walk** of `walkV3`: its key is absent from its instance's record tree, for every
value assignment. -/
theorem walk_abs (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {wv : WalkR} (hwv : wv ∈ r.walks) (hfk : wv.fk = FK_ABS) (v : Nat → NearSpec.Bytes) :
    (Fv r wv.tau v).find wv.key3 = some none := by
  have L := trieLink_of hp hsz hH T W
  have hK := LinkKeynib.keynibOk_of hp hsz hH T W
  have hall : WalkWf3 (allWalks r.walks r.ups) := allWalks_wf_22 W.nodes W.walks W.walkSteps W.ups L.bmap
  have G := walkHyp_any W.nodes W.heads W.values hall L.parent L.vparent
    (walkBal_all W.ups (Or.inl rfl) L.edge) (walkBal_all W.ups (Or.inr rfl) L.bmap) (recBytes_of W L)
    (fun w hw => by
      rcases List.mem_append.1 hw with h' | h'
      · exact hsym_of W.walks hK w h'
      · exact ups_sym r.ups w h')
    (valsBy r.nodes r.values v)
  obtain ⟨hd, hhd, htau, -, hA⟩ := Walk3.walk3_find_of G (List.mem_append_left _ hwv)
  have he : hd = headAt r.heads wv.tau := by rw [← htau]; exact (L.chain.head_all hd hhd).2
  rw [he] at hA
  exact hA hfk

theorem keyAccessKey_ne (a : NearSpec.Bytes) (k : NearSpec.PublicKey) :
    NearSpecV3.keyAccessKey a k ≠ NearSpecV3.keyBwState := by
  intro he
  have := congrArg (fun l => l.getD 1 0) he
  simp [NearSpecV3.keyAccessKey, NearSpecV3.keyBwState, NearSpec.nibbles] at this

/-- **The access-key lookup of a gas refund** in the main trie family (length-preserving `v`):
`VAL` finds the value of record `akk`, `ABS` finds nothing. -/
theorem ak_find (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (h0 : 0 < p.sched.length) (st : NearSpec.Bytes)
    {i : Nat} (hi : i < (flatR r.lists).length) (hee : (flatR r.lists)[i].ee = true)
    {v : Nat → NearSpec.Bytes} (hv : LenOk r v) :
    (Tf r 0 st v).find (NearSpecV3.keyAccessKey (toBytes (flatR r.lists)[i].s)
        ⟨(flatR r.lists)[i].kt, toBytes (flatR r.lists)[i].pk⟩) =
      some (if (flatR r.lists)[i].akf = FK_VAL then some (v (flatR r.lists)[i].akk) else none) := by
  have L := trieLink_of hp hsz hH T W
  obtain ⟨wv, hwv, ht, hf, hk, hkey⟩ := ak_walk hp hsz hH T W hi hee
  obtain ⟨toks, -, -, hwf, -⟩ := W.lists.toks
  have hakf := (hwf i hi).akf
  have hakk := (hwf i hi).small.2.2.1
  rw [← hkey]
  by_cases h0f : (flatR r.lists)[i].akf = FK_VAL
  · rw [if_pos h0f]
    obtain ⟨hr, hlt⟩ := walk_reach hp hsz hH T W hwv (hf.trans h0f)
    rw [ht] at hr
    have hid := vid_vpos W.values (k := wv.k) (by rw [hk]; exact hakk) hlt
    have := (Tf_find hp hsz hH T W h0 (Nat.zero_le _) st (by rw [hkey]; exact keyAccessKey_ne _ _) hr hlt hv).1
    rw [this, hid, hk]
  · rw [if_neg h0f]
    have hA : wv.fk = FK_ABS := by
      rw [hf]; unfold FK_VAL at h0f; unfold FK_ABS; omega
    have habs := walk_abs hp hsz hH T W hwv hA v
    rw [ht] at habs
    rw [NearSpec.PTrie.find_upsert_other _ _ _ _ _ (Fv_wf W L (Nat.zero_le _) hv) (by decide)
      (by rw [hkey]; exact keyAccessKey_ne _ _) (Tf_upsert hp hsz hH T W h0 (Nat.zero_le _) st hv)]
    exact habs

end

end LinkRcptWalk

end ZkFormal.NearV3.Assembly
