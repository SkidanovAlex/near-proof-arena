import ZkFormal.NearV3.Assembly.LinkSchedRead
import ZkFormal.NearV3.Qv.Extract.SupplierStreams
import ZkFormal.NearV3.Qv.Extract.ByteAggregate
import ZkFormal.NearV3.Qv.Extract.WalkChain

/-!
# ZkFormal.NearV3.Assembly.LinkVBytes — `VBYTES` exactness of the codec's previous value

A codec block `f` of `nearAirV3` with `pres = 1` sends `VBYTES (vid, i, bpre_{f+i})` for
`i < L = 37 + 24·NN`.  **`codec_value`**: the value record `vid` is exactly these `L` bytes (not
merely a longer record with this prefix).

Argument (`Qv.Extract.stream_isolate`): the `VBYTES` balance is exact — the value records'
receives are a permutation of the sends of codec, acct, akey and qv.  Every sender other than
block `f`'s rows is *start-closed* (a send `(v, p, ·)` comes with a send `(v, 0, ·)` of the same
sender family):
* other codec rows (`Codec.vrow`: a row with nonzero `VBYTES` multiplicity is an encoding row of
  some block `f'`, whose first row sends position `0`; `f'` is not inside block `f`, since a first
  row has `pos = 0`);
* acct, akey (`account_streams_closed`, `access_key_streams_closed`);
* qv (`physical_records_closed` over the extracted parser chain, `byte_all_physical`).
Value-record keys `(vid, pos)` are unique, so block `f`'s stream is the whole record `vid`.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E

namespace Codec
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- **A codec row with a `VBYTES` send is an encoding row of a block.** -/
theorem vrow (hL : CLocal tr t pub) (hH : tr.height t ≤ 2 ^ 22) {r : Nat} (hr : r < tr.height t)
    (hm : (interactions[0]!).multNat tr t r pub ≠ 0) :
    ∃ f, f ≤ r ∧ cv tr t f kF = 1 ∧ r - f < 37 + 24 * cv tr t f NN := by
  apply enc_row hL hH hr
  have K := kinds hL hr
  apply Classical.byContradiction; intro hne
  obtain ⟨q, c1⟩ := zd hL hr (e := sub (c vbg) (.mul (c pres) encG)) (by simp [constraints, cKind])
  zs c1 []
  have h0 : (cv tr t r kH : Int) + (cv tr t r kR + cv tr t r kZ) = 0 := by omega
  rw [h0] at c1
  have := lt (tr := tr) (t := t) r vbg
  exact hm (mult_zero (i := interactions[0]!) rfl (by simp only [zev_c, cur_cv]; omega))

/-- The `VBYTES` send of such a row: multiplicity `pres` of its block, message
`(vid, r - f, bpre_r)`. -/
theorem vrow_msg (hL : CLocal tr t pub) (hH : tr.height t ≤ 2 ^ 22) {r : Nat} (hr : r < tr.height t)
    (hm : (interactions[0]!).multNat tr t r pub ≠ 0) :
    ∃ f, f ≤ r ∧ f < tr.height t ∧ cv tr t f kF = 1 ∧ r - f < 37 + 24 * cv tr t f NN ∧
      cv tr t f pres = 1 ∧
      (interactions[0]!).msgVal tr t r pub = [cv tr t f vid, r - f, cv tr t r bpre].map Fp.ofNat := by
  obtain ⟨f, hfr, hF, hrf⟩ := vrow hL hH hr hm
  have hf : f < tr.height t := by omega
  obtain ⟨hp, V, -⟩ := codec_pre hL hH hf hF
  obtain ⟨m, msg⟩ := V (r - f) (by omega)
  rw [show f + (r - f) = r by omega] at m msg
  refine ⟨f, hfr, hf, hF, hrf, by omega, msg⟩

end Codec

end ZkFormal.NearV3.Sched

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkVBytes

open ZkFormal.NearV3 ZkFormal.NearV3.Sched ZkFormal.NearV3.Qv.Extract

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- `rowTraffic` through the interactions on `(b, s)`. -/
theorem rowTraffic_filter (is : List Interaction) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (b : Nat) (s : Bool) :
    rowTraffic is tr t r pub b s = (is.filter fun i => decide (i.bus = b ∧ i.send = s)).flatMap
      fun i => List.replicate (i.multNat tr t r pub) (i.msgVal tr t r pub) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [rowTraffic, List.flatMap_cons, List.filter_cons] at ih ⊢
    rw [ih]
    by_cases h : i.bus = b ∧ i.send = s
    · simp [h]
    · simp [h]

theorem codec_vfilter :
    (isAt T_CODEC).filter (fun i => decide (i.bus = B_VBYTES ∧ i.send = true)) =
      [Codec.interactions[0]!] := by decide +kernel

/-- The codec's `VBYTES` sends of a row. -/
theorem codec_row (tr : Trace Fp) (pub : List Fp) (r : Nat) :
    rowTraffic (isAt T_CODEC) tr T_CODEC r pub B_VBYTES true =
      List.replicate ((Codec.interactions[0]!).multNat tr T_CODEC r pub)
        ((Codec.interactions[0]!).msgVal tr T_CODEC r pub) := by
  rw [rowTraffic_filter, codec_vfilter, List.flatMap_singleton]

/-- The physical `VBYTES` sends of the codec table on rows `rs`. -/
def codecV (tr : Trace Fp) (pub : List Fp) (rs : List Nat) : List (List Fp) :=
  rs.flatMap fun r => rowTraffic (isAt T_CODEC) tr T_CODEC r pub B_VBYTES true

theorem range_split3 (f L h : Nat) (hle : f + L ≤ h) :
    List.range h = List.range f ++ List.range' f L ++ List.range' (f + L) (h - (f + L)) := by
  have h1 := List.range'_append (s := 0) (m := f) (n := L) (step := 1)
  have h2 := List.range'_append (s := 0) (m := f + L) (n := h - (f + L)) (step := 1)
  simp only [Nat.zero_add, Nat.one_mul] at h1 h2
  rw [List.range_eq_range', List.range_eq_range', h1, h2, show f + L + (h - (f + L)) = h by omega]

/-- **`VBYTES` exactness**: the value record a present codec block reads is exactly its `L`
pre bytes. -/
theorem codec_value {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r)
    {f : Nat} (hf : f < tr.height T_CODEC) (hF : cv tr T_CODEC f Codec.kF = 1)
    (hP : cv tr T_CODEC f Codec.pres = 1) :
    (∃ e ∈ r.values, e.vz = false ∧ e.vid = cv tr T_CODEC f Codec.vid ∧
      e.bytes = (List.range (37 + 24 * cv tr T_CODEC f Codec.NN)).map
        fun i => cv tr T_CODEC (f + i) Codec.bpre) ∧
    ∀ a ∈ r.accts, a.k ≠ cv tr T_CODEC f Codec.vid := by
  simp only [show @ZkFormal.Near.cv = @ZkFormal.Chacha.cv from rfl] at hf hF hP ⊢
  have hL := codec_local hH codecOwn
  have hH22 := codec_h22 hH codecOwn
  have enc := Codec.enc_rows hL hH22 hf hF
  obtain ⟨-, V, -⟩ := Codec.codec_pre hL hH22 hf hF
  generalize hLdef : 37 + 24 * Chacha.cv tr T_CODEC f Codec.NN = L at *
  have hL5 : 5 + 24 * Chacha.cv tr T_CODEC f Codec.NN + 32 = L := by omega
  generalize hv : Chacha.cv tr T_CODEC f Codec.vid = v
  have hvP : v < P := by rw [← hv]; exact ZkFormal.Chacha.cv_lt _ _
  have hfit : f + L ≤ tr.height T_CODEC := by have := (enc (L - 1) (by omega)).1; omega
  -- block `f`'s stream
  let stream : List (List Fp) := (List.range L).map fun i => Msg.toFp [v, i, Chacha.cv tr T_CODEC (f + i) Codec.bpre]
  have hsel : codecV tr pub (List.range' f L) = stream := by
    unfold codecV
    simp only [stream]
    rw [List.range'_eq_map_range, List.flatMap_map, List.map_eq_flatMap]
    apply flatMap_congr'
    intro i hi
    have hi' := List.mem_range.mp hi
    obtain ⟨m, msg⟩ := V i (by omega)
    rw [codec_row, m, hP, msg, hv]
    rfl
  -- other codec rows are start-closed
  have hothC : StartClosed (codecV tr pub (List.range f) ++
      codecV tr pub (List.range' (f + L) (tr.height T_CODEC - (f + L)))) := by
    intro m hm
    have hrow : ∀ x, x ∈ List.range f ∨ x ∈ List.range' (f + L) (tr.height T_CODEC - (f + L)) →
        ∀ y ∈ rowTraffic (isAt T_CODEC) tr T_CODEC x pub B_VBYTES true,
          y ∈ codecV tr pub (List.range f) ++
            codecV tr pub (List.range' (f + L) (tr.height T_CODEC - (f + L))) := by
      intro x hx y hy
      rcases hx with hx | hx
      · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨x, hx, hy⟩)
      · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, hy⟩)
    obtain ⟨x, hx, hmx⟩ : ∃ x, (x ∈ List.range f ∨ x ∈ List.range' (f + L) (tr.height T_CODEC - (f + L))) ∧
        m ∈ rowTraffic (isAt T_CODEC) tr T_CODEC x pub B_VBYTES true := by
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨x, hx, hmx⟩ := List.mem_flatMap.mp hm; exact ⟨x, Or.inl hx, hmx⟩
      · obtain ⟨x, hx, hmx⟩ := List.mem_flatMap.mp hm; exact ⟨x, Or.inr hx, hmx⟩
    have hxh : x < tr.height T_CODEC := by
      rcases hx with hx | hx
      · have := List.mem_range.mp hx; omega
      · have := List.mem_range'_1.mp hx; omega
    rw [codec_row] at hmx
    obtain ⟨hmult, rfl⟩ := List.mem_replicate.mp hmx
    obtain ⟨f', hf'x, hf', hF', hxf', hP', msgx⟩ := Codec.vrow_msg hL hH22 hxh hmult
    obtain ⟨-, V', -⟩ := Codec.codec_pre hL hH22 hf' hF'
    obtain ⟨m0, msg0⟩ := V' 0 (by omega)
    rw [Nat.add_zero] at m0 msg0
    -- `f'` is not a row of block `f`
    have hout : f' ∈ List.range f ∨ f' ∈ List.range' (f + L) (tr.height T_CODEC - (f + L)) := by
      by_cases h1 : f' < f
      · exact Or.inl (List.mem_range.mpr h1)
      by_cases h2 : f + L ≤ f'
      · exact Or.inr (List.mem_range'_1.mpr ⟨h2, by omega⟩)
      exfalso
      by_cases h3 : f' = f
      · subst h3
        rcases hx with hx | hx
        · have := List.mem_range.mp hx; omega
        · have := List.mem_range'_1.mp hx; omega
      · have hp0 := (ZkFormal.NearV3.Sched.Codec.first_row hL hf' hF').2.1
        have hpi := (enc (f' - f) (by omega)).2.2.1
        rw [show f + (f' - f) = f' by omega] at hpi
        omega
    refine ⟨(Codec.interactions[0]!).msgVal tr T_CODEC f' pub,
      hrow f' hout _ (by rw [codec_row]; exact List.mem_replicate.mpr ⟨by rw [m0, hP']; decide, rfl⟩), ?_⟩
    rw [msg0, msgx]
    rfl
  -- the codec traffic splits into block `f`'s stream and the other rows
  have hcod : (List.range (tr.height T_CODEC)).flatMap
      (fun x => rowTraffic (isAt T_CODEC) tr T_CODEC x pub B_VBYTES true) =
      codecV tr pub (List.range f) ++ stream ++
        codecV tr pub (List.range' (f + L) (tr.height T_CODEC - (f + L))) := by
    rw [← hsel]
    unfold codecV
    rw [range_split3 f L _ hfit, List.flatMap_append, List.flatMap_append]
  -- qv: the extracted parser records
  have hQ : TableLocal Qv.Candidates.KeyTrafficRepair.table tr T_QV pub :=
    tableLocal_of_holdsP hH (t := T_QV) rfl
  have hl := Qv.Candidates.KeyTrafficRepair.local_to_base hQ
  obtain ⟨q⟩ := Qv.Extract.walk_chain_exists hl
  obtain ⟨pc⟩ := Qv.Extract.parser_chain_exists hl q
  have hqv : (List.range (tr.height T_QV)).flatMap
      (fun x => rowTraffic (isAt T_QV) tr T_QV x pub B_VBYTES true) =
      pc.segs.flatMap (fun p => Qv.Extract.physicalRecordBytes tr T_QV p.1 p.2 pub) := by
    rw [← Qv.Extract.byte_all_physical hl q pc]
    apply flatMap_congr'
    intro x _
    exact Qv.Candidates.KeyTrafficRepair.other_bus _ _ _ _ _ (by decide) _
  -- the exact `VBYTES` balance
  let others : List (List Fp) :=
    (codecV tr pub (List.range f) ++ codecV tr pub (List.range' (f + L) (tr.height T_CODEC - (f + L)))) ++
      (acctV3Sends r.accts B_VBYTES).map Msg.toFp ++ (akeySends r.akeys B_VBYTES).map Msg.toFp ++
      pc.segs.flatMap (fun p => Qv.Extract.physicalRecordBytes tr T_QV p.1 p.2 pub)
  have v0 : valSends r.values B_VBYTES = [] := by simp [valSends, B_VBYTES, B_BYTES, B_ENT, B_SIZE]
  have a0 : acctRecvs r.accts B_VBYTES = [] := by simp [acctRecvs, B_VBYTES, B_MEM]
  have k0 : akeyRecvs r.akeys B_VBYTES = [] := by simp [akeyRecvs, B_AKC, B_VBYTES]
  have hbal : (stream ++ others).Perm ((valRecvs r.values B_VBYTES).map Msg.toFp) := by
    apply List.perm_iff_count.mpr
    intro M
    have h := bal_users hH (b := B_VBYTES) (U := [T_VAL, T_CODEC, T_ACCT, T_AKEY, T_QV]) (by decide)
      (by decide) (by decide +kernel) (by decide +kernel) M
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
    rw [val_count T _ _ _ (by decide +kernel), val_count T _ _ _ (by decide +kernel),
      show isAt T_ACCT = AcctV3.interactions from rfl, tcnt_of_traffic T.accts, tcnt_of_traffic T.accts,
      show isAt T_AKEY = AkeyV3.interactions from rfl, tcnt_of_traffic T.akeys, tcnt_of_traffic T.akeys,
      tableBusCount_noside (s := false) (is := isAt T_CODEC) (by decide +kernel),
      tableBusCount_noside (s := false) (is := isAt T_QV) (by decide +kernel),
      tableBusCount_eq (isAt T_CODEC), tableBusCount_eq (isAt T_QV), hcod, hqv] at h
    simp only [tcnt, ite_true, Bool.false_eq_true, ite_false, valTraffic, acctV3Traffic, akeyTraffic,
      v0, a0, k0, List.map_nil, List.count_nil, Nat.zero_add, Nat.add_zero] at h
    simp only [others, List.count_append] at h ⊢
    omega
  have hclosed : StartClosed others :=
    startClosed_append (startClosed_append (startClosed_append hothC (account_streams_closed r.accts))
      (access_key_streams_closed r.akeys)) (Qv.Extract.physical_records_closed hl q pc pc.segs (fun _ h => h))
  have hstart : ∃ x ∈ stream, byteKey x = (Fp.ofNat v, 0) :=
    ⟨Msg.toFp [v, 0, Chacha.cv tr T_CODEC (f + 0) Codec.bpre],
      List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩, rfl⟩
  have hselected : ∀ x ∈ stream, (byteKey x).1 = Fp.ofNat v := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    rfl
  have hnacct : ∀ a ∈ r.accts, a.k ≠ v := by
    intro a ha hk
    have hne := stream_other_id_ne byteKey (Fp.ofNat v) stream others _ hbal
      (value_byte_keys_unique W.values) hstart hclosed
    have hpre := (LinkVPost.acct_wf W ha).1
    refine hne (Msg.toFp [a.k, 0, a.pre.getD 0 0]) ?_ (by rw [hk]; rfl)
    simp only [others, List.mem_append]
    left; left; right
    apply List.mem_map_of_mem
    simp only [acctV3Sends, ite_true]
    exact List.mem_flatMap.mpr ⟨a, ha, by rw [emitAt_zero]; exact List.mem_map.mpr ⟨0, by simp [hpre], rfl⟩⟩
  have hiso := stream_isolate byteKey (Fp.ofNat v) stream others _ hbal
    (value_byte_keys_unique W.values) hstart hselected hclosed
  -- the record
  have h0mem : Msg.toFp [v, 0, Chacha.cv tr T_CODEC (f + 0) Codec.bpre] ∈ stream :=
    List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩
  have hmem := (List.mem_filter.mp (hiso.mem_iff.mp h0mem)).1
  obtain ⟨e, he, j, hj, hz, hid, -, -⟩ := value_byte_member W.values hmem
  have heid : e.vid = v := by
    have h0 : (Fp.ofNat v).toNat = v := by rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt hvP]
    exact hid.symm.trans h0
  have hb' : stream.Perm (valueRecordStream e) := by
    have hf := value_stream_filter W.values e he
    simpa only [byteKey, ← heid, hf] using hiso
  have heqlen : e.bytes.length = L := by
    have h := hb'.length_eq
    simpa [stream, valueRecordStream, hz] using h.symm
  have hLP : L < P := by unfold P; omega
  refine ⟨⟨e, he, hz, heid, ?_⟩, hnacct⟩
  apply List.ext_getElem
  · simp [heqlen]
  intro i hi hi'
  have hiL : i < L := by omega
  have hm : Msg.toFp [v, i, Chacha.cv tr T_CODEC (f + i) Codec.bpre] ∈ stream :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hiL, rfl⟩
  have hmem := hb'.mem_iff.mp hm
  simp only [valueRecordStream, hz, Bool.false_eq_true, ite_false] at hmem
  obtain ⟨j, hj, heq⟩ := List.mem_map.mp hmem
  have hj' := List.mem_range.mp hj
  simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq] at heq
  have hji : j = i := Link3.ofNat_eq (by omega) (by omega) heq.2.1
  subst j
  have hb1 : e.bytes.getD i 0 < P := by
    simpa [List.getD_eq_getElem?_getD, hi] using (W.values.canon e he).2.2.2 _ (List.getElem_mem hi)
  have hb2 := Link3.ofNat_eq hb1 (ZkFormal.Chacha.cv_lt _ _) heq.2.2.1
  simpa [List.getD_eq_getElem?_getD, hi] using hb2

end LinkVBytes

end ZkFormal.NearV3.Assembly
