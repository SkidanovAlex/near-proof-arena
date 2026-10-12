import ZkFormal.NearV3.Rcpt.Link.AcctSlots
import ZkFormal.NearV3.Link.Sha3

/-!
# ZkFormal.NearV3.Rcpt.Link.ValBytes — value-record bytes and the acct pre bytes (`preB`)

* `val_bytes8` — a value record referenced by a node slot has byte-valued bytes (the `sha_core`
  argument of `Link3.val_sha`, keeping its first conclusion);
* `acct_written'` — an acct slot is the value id of a written node slot (`VSLOT`);
* `acct_pre_byte` — `VBYTES` (users val, codec, acct, akey, qv; acct sends `(k, j, pre_j)`, only
  val receives): every acct pre byte is the byte of a value record with `vid = k`;
* **`preB_of`** — under the trie link's `ShaHyp`, every acct record's pre bytes are bytes.
-/

namespace ZkFormal.NearV3.Link3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpecV3 ZkFormal.NearV3

variable {vs : List NodeS3} {hs : List HeadE} {es : List ValE}
variable {others : List Msg} {shaS shaR : Nat → List Fp → Nat}

theorem val_bytes8 (hw : NodeWf3 vs) (hvw : ValWf es) (hvb : VParentBal vs es)
    (H : ShaHyp vs hs es others shaS shaR) {p : Nat} (hp : p < vs.length) {i l : Nat} {pre po : List Nat} {w : Bool}
    (hv : vs[p].v.value = some (i, l, pre, po, w)) :
    ∃ t, ∃ ht : t < es.length, es[t].vid = i ∧ Bytes8 es[t].bytes := by
  have hlen := vlen_le hvw
  obtain ⟨t, ht, hpos, hi, hl, hV⟩ := val_pos hw hvw hvb hlen hp hv
  have hvt := vid_small hvw ht
  have hbl : es[t].bytes.length = l := by
    have := hvw.shape _ (List.getElem_mem ht)
    cases hz : es[t].vz
    · rw [(this.2 hz).1, hl]
    · rw [(this.1 hz).2, ← hl, (this.1 hz).1]; rfl
  have hm := val_dig_mem (hs := hs) hp hv
  rw [← hi, hvt, ← hbl] at hm
  have hd : ∀ x ∈ pre, x < ZkFormal.Algebra.P := by
    intro x hx; apply hw.canon _ (List.getElem_mem hp)
    cases hvv : vs[p].v with
    | leaf k sl m =>
      rw [hvv] at hv
      cases sl with
      | ref => simp [NodeV3.value] at hv
      | val lb i' l' pr p' w' =>
        simp [NodeV3.value] at hv; obtain ⟨-, -, rfl, -⟩ := hv
        simp [NodeV3.raw, NSlot3.raw, hx]
    | ext => rw [hvv] at hv; simp [NodeV3.value] at hv
    | branch sv kids m =>
      rw [hvv] at hv
      cases sv with
      | none => simp [NodeV3.value] at hv
      | some sl =>
        cases sl with
        | ref => simp [NodeV3.value] at hv
        | val lb i' l' pr p' w' =>
          simp [NodeV3.value] at hv; obtain ⟨-, -, rfl, -⟩ := hv
          simp [NodeV3.raw, NSlot3.raw, hx]
  have hcore := Link.sha_core H.sha _ H.bytes (enc := es[t].bytes)
    (by unfold msgId K_VPRE ZkFormal.Algebra.P; omega)
    (fun x hx => (hvw.canon _ (List.getElem_mem ht)).2.2.2 x hx)
    (by
      have hsh := hvw.shape _ (List.getElem_mem ht)
      have hr := hvw.rows
      have hm := le_sum_mem (l := es.map fun e => if e.vz then 1 else e.len)
        (List.mem_map.mpr ⟨es[t], List.getElem_mem ht, rfl⟩)
      cases hz : es[t].vz
      · rw [(hsh.2 hz).1]; simp only [hz] at hm; simp at hm; unfold ZkFormal.Algebra.P; omega
      · rw [(hsh.1 hz).2]; simp; unfold ZkFormal.Algebra.P; omega)
    hd (vpre_sends hw hvw H.othersId ht) (H.digest _ (cnt_pos3 hm))
  exact ⟨t, ht, hi, hcore.1⟩

end ZkFormal.NearV3.Link3

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Assembly
open ZkFormal.NearV3.Link3 (mem_emitAt3 ofNat_eq)

/-- An acct slot is the value id of a written node slot (`VSLOT`). -/
theorem acct_written' {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) {a : AcctV} (ha : a ∈ r.accts) :
    ∃ p, ∃ hp : p < r.nodes.length, ∃ l pre po,
      r.nodes[p].v.value = some (a.k, l, pre, po, true) := by
  have hvb := vparentBal_of hH T
  have hm : [a.k] ∈ ZkFormal.NearV3.acctV3Sends r.accts B_VSLOT := by
    simp only [ZkFormal.NearV3.acctV3Sends, show B_VSLOT ≠ ZkFormal.NearV3.B_VBYTES by decide,
      show B_VSLOT ≠ B_BYTES by decide, show B_VSLOT ≠ B_MEM by decide, ite_false, ite_true,
      List.mem_map]
    exact ⟨a, ha, rfl⟩
  have hc := List.count_pos_iff.mpr (List.mem_map_of_mem (f := Msg.toFp) hm)
  rw [vslot_bal hH T] at hc
  obtain ⟨x, hx, he⟩ := List.mem_map.mp (List.count_pos_iff.mp hc)
  simp only [ZkFormal.NearV3.nodeRecvs3, show B_VSLOT ≠ B_DIGEST by decide,
    show B_VSLOT ≠ B_PARENT by decide, show B_VSLOT ≠ B_EDGE by decide,
    show B_VSLOT ≠ ZkFormal.NearV3.B_BMAP by decide, show B_VSLOT ≠ ZkFormal.NearV3.B_DUP by decide,
    show B_VSLOT ≠ ZkFormal.NearV3.B_ENT by decide, show B_VSLOT ≠ ZkFormal.NearV3.B_UPB by decide,
    ite_false, ite_true, List.mem_flatMap] at hx
  obtain ⟨⟨s, n⟩, hsn, hx⟩ := hx
  obtain ⟨hn, rfl⟩ := ZkFormal.NearV3.Link3.mem_zip_range hsn
  split at hx
  · rename_i i l pre po hv
    simp only [List.mem_singleton] at hx
    subst hx
    have hlen := ZkFormal.NearV3.Link3.vlen_le W.values
    obtain ⟨t, ht, -, hi, -, -⟩ := ZkFormal.NearV3.Link3.val_pos W.nodes W.values hvb hlen hn hv
    have hvt := ZkFormal.NearV3.Link3.vid_small W.values ht
    have hk : a.k < P := by
      rcases W.accts with he | hw'
      · rw [he] at ha; simp at ha
      · exact (hw'.v1.len a ha).2.2.1
    simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
    have := ZkFormal.Near.Link.ofNat_inj (by unfold P; omega) hk he
    subst this
    exact ⟨n, hn, l, pre, po, hv⟩
  · simp at hx

/-- **`VBYTES`**: every acct pre byte is a byte of a value record with `vid = k`. -/
theorem acct_pre_byte {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) {a : AcctV} (ha : a ∈ r.accts)
    {j : Nat} (hj : j < 72) :
    ∃ t, ∃ ht : t < r.values.length, r.values[t].vid = a.k ∧
      a.pre.getD j 0 = r.values[t].bytes.getD j 0 := by
  have hw := W.accts.resolve_left (List.ne_nil_of_mem ha)
  obtain ⟨hpre, -, hk, -⟩ := hw.v1.len a ha
  have hcan := hw.v1.canon a ha
  have hpj : a.pre.getD j 0 < P := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact hcan _ (List.mem_append_left _ (List.getElem_mem _))
  let M : Msg := [a.k, j, a.pre.getD j 0]
  have hb := bal_users hH (b := B_VBYTES) (U := [T_VAL, T_CODEC, Assembly.T_ACCT, T_AKEY, T_QV]) (by decide)
    (by decide) (by decide +kernel) (by decide +kernel) (Msg.toFp M)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hb
  rw [val_count T _ _ _ (by decide +kernel), val_count T _ _ _ (by decide +kernel),
    show isAt Assembly.T_ACCT = AcctV3.interactions from rfl, tcnt_of_traffic T.accts, tcnt_of_traffic T.accts,
    tableBusCount_noside (s := false) (is := isAt T_CODEC) (by decide +kernel),
    tableBusCount_noside (s := false) (is := isAt T_AKEY) (by decide +kernel),
    tableBusCount_noside (s := false) (is := isAt T_QV) (by decide +kernel)] at hb
  have hs : 0 < tcnt (acctV3Traffic r.accts) true B_VBYTES (Msg.toFp M) := by
    simp only [tcnt, ite_true, acctV3Traffic]
    apply List.count_pos_iff.mpr
    apply List.mem_map_of_mem
    simp only [acctV3Sends, ite_true, List.mem_flatMap]
    exact ⟨a, ha, mem_emitAt3.mpr ⟨j, by omega, by simp [M]⟩⟩
  have r0 : tcnt (acctV3Traffic r.accts) false B_VBYTES (Msg.toFp M) = 0 := by
    simp [tcnt, acctV3Traffic, acctRecvs, B_VBYTES, B_MEM]
  have v0 : tcnt (valTraffic r.values) true B_VBYTES (Msg.toFp M) = 0 := by
    simp [tcnt, valTraffic, valSends, B_VBYTES, B_BYTES, B_ENT, B_SIZE]
  have hv : 0 < tcnt (valTraffic r.values) false B_VBYTES (Msg.toFp M) := by omega
  simp only [tcnt, Bool.false_eq_true, ite_false, valTraffic, valRecvs, ite_true] at hv
  obtain ⟨m, hm, he⟩ := List.mem_map.mp (List.count_pos_iff.mp hv)
  obtain ⟨e, he', hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he'
  split at hm
  · simp at hm
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    have ce := W.values.canon _ he'
    simp only [M, Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq] at he
    have e1 := ofNat_eq ce.1 hk he.1
    have hqP : q < P := by
      have := List.mem_range.mp hq; have := ZkFormal.NearV3.Link3.val_bytes_lt W.values ht
      unfold P; omega
    have e2 := ofNat_eq hqP (by unfold P; omega) he.2.1
    subst e2
    have hbq : r.values[t].bytes.getD q 0 < P := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (List.mem_range.mp hq)]
      exact ce.2.2.2 _ (List.getElem_mem _)
    exact ⟨t, ht, e1, (ofNat_eq hbq hpj he.2.2.1).symm⟩

/-- **`preB`**: the acct records' pre bytes are bytes. -/
theorem preB_of {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) {others : List Msg}
    {shaS shaR : Nat → List Fp → Nat}
    (S : ZkFormal.NearV3.Link3.ShaHyp r.nodes r.heads r.values others shaS shaR) :
    ∀ a ∈ r.accts, Bytes8 a.pre := by
  intro a ha
  have hw := W.accts.resolve_left (List.ne_nil_of_mem ha)
  obtain ⟨hpre, -⟩ := hw.v1.len a ha
  obtain ⟨p, hp, l, pre, po, hv⟩ := acct_written' hH T W ha
  obtain ⟨t, ht, hvt, hB⟩ :=
    ZkFormal.NearV3.Link3.val_bytes8 W.nodes W.values (vparentBal_of hH T) S hp hv
  apply Link.bytes8_of_getD hpre
  intro j hj
  obtain ⟨t', ht', hvt', he⟩ := acct_pre_byte hH T W ha hj
  have := ZkFormal.NearV3.Link3.vid_inj W.values (ZkFormal.NearV3.Link3.vlen_le W.values) ht ht'
    (by rw [hvt, hvt'])
  subst this
  rw [he]
  exact Link.getD_lt_of_bytes8 hB j

end ZkFormal.NearV3.RcptLink
