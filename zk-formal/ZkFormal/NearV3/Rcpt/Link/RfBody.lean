import ZkFormal.NearV3.Rcpt.Link.PeoBytes
import ZkFormal.NearV3.Rcpt.Link.GasPub
import ZkFormal.Near.Link.Streams

/-!
# ZkFormal.NearV3.Rcpt.Link.RfBody — the refund stream is the public body (closes `ramtB`)

`rcptV3` sends every refund receipt's bytes as `BYTES (K_RF, bOffs q + i, encRefund_q[i])`; the
public bus receives `(K_RF, 8 + k, B[8 + k])` for `k < |B| − 8` (`bodyRecords`); the `RF` total is
`bOffs n = |B|` (`RcptV3Wf.body` + the header's `u32 |B|`).  Every public receive is matched by a
send (the `BYTES` balance); only the receipt `RF` streams have kind `K_RF` (`rf_isolate`,
`othersRC_kind`).  Hence (`Rcpt/Link/Body`'s argument, from `HoldsP`):

* **`rfStream_body`** — `rfStream r.lists = (p.body.drop 8).map UInt8.toNat`;
* **`ramtBytes`** — refund amounts are bytes (`ramt ⊆ encRefund`).
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Near.Link
  ZkFormal.NearV3.Assembly NearSpec NearSpecV3

/-- A receipt's refund bytes (empty without a refund). -/
def rfS (x : RcptE) : List Nat := if x.hr then x.encRefund else []

/-- The concatenated refund stream (body bytes after `u32 0 ‖ u32 nref`). -/
def rfStream (ls : RcptV3Vs) : List Nat := (flatR ls).flatMap rfS

theorem rfLen_eq (x : RcptE) : rfLen x = (rfS x).length := by
  unfold rfLen rfS; split <;> rfl

theorem bOffs_flat (xs : List RcptE) (q : Nat) : bOffs xs q = 8 + ((xs.take q).flatMap rfS).length := by
  unfold bOffs
  congr 1
  induction xs.take q with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, ih, rfLen_eq]

theorem bOffs_total (ls : RcptV3Vs) : bOffs (flatR ls) (flatR ls).length = 8 + (rfStream ls).length := by
  rw [bOffs_flat, List.take_length]; rfl

/-- Of a receipt's byte streams, only its refund stream has id `K_RF`. -/
theorem receipt_sends_rf {pub : List Fp} {xs : List RcptE} {j r off : Nat} {x : RcptE} {m : Msg}
    (hm : m ∈ rSends pub xs j r off x B_BYTES) (ha : m.head? = some K_RF) :
    x.hr = true ∧ m ∈ emitAt K_RF (bOffs xs r) x.encRefund := by
  simp only [rSends, ite_true, List.mem_append] at hm
  rcases hm with (((hm | hm) | hm) | hm) | hm
  · have hh := emitAt_head_eq hm ha
    exfalso; unfold msgId K_RC K_RF at hh; omega
  · split at hm
    · next hr => exact ⟨hr, hm⟩
    · simp at hm
  · have hh := emitAt_head_eq hm ha
    exfalso; unfold msgId K_PEO K_RF at hh; omega
  · have hh := emitAt_head_eq hm ha
    exfalso; unfold msgId K_LEAF K_RF at hh; omega
  · split at hm
    · have hh := emitAt_head_eq hm ha
      exfalso; unfold msgId K_RID K_RF at hh; omega
    · simp at hm

/-- **`RF` isolation**: the receipt `BYTES` messages with id `K_RF` are refund-stream bytes. -/
theorem rf_isolate {pub : List Fp} {ls : RcptV3Vs} {m : Msg}
    (hm : m ∈ rcptSends3 pub ls B_BYTES) (ha : m.head? = some K_RF) :
    ∃ q, ∃ hq : q < (flatR ls).length, (flatR ls)[q].hr = true ∧ ∃ i, i < (flatR ls)[q].encRefund.length ∧
      m = [K_RF, bOffs (flatR ls) q + i, (flatR ls)[q].encRefund.getD i 0] := by
  simp only [rcptSends3, ite_true, show B_BYTES ≠ B_RCL by decide, ite_false, List.append_nil] at hm
  obtain ⟨j, hj, hm⟩ := List.mem_flatMap.mp hm
  have hj := List.mem_range.mp hj
  rcases List.mem_append.mp hm with hm | hm
  · have hid := emitAt_head_eq hm ha
    exfalso; unfold msgId K_RC K_RF at hid; omega
  · obtain ⟨⟨q, off, x⟩, hpos, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨hr, hm⟩ := receipt_sends_rf hm ha
    obtain ⟨hq, hx⟩ := located_flat hj hpos
    refine ⟨q, hq, by rw [hx]; exact hr, ?_⟩
    rw [hx]
    obtain ⟨i, hi, rfl⟩ := ZkFormal.NearV3.Link3.mem_emitAt3.mp hm
    exact ⟨i, hi, rfl⟩

/-- The refund encoding's values are raw (canonical) or bytes. -/
theorem receipt_rf_values {x : RcptE} {r tok tok' : Nat} {gp : List Nat}
    (w : x.Wf r gp tok tok') : RawOrByte x.toRcptV x.encRefund := by
  obtain ⟨-, -, hs, -⟩ := w.ids
  have hs := (valid_length hs).2
  simp only [toBytes_length] at hs
  unfold RcptV.encRefund
  rob

/-- The refund stream at receipt `q`'s body offset. -/
theorem rfStream_at {ls : RcptV3Vs} {q : Nat} (hq : q < (flatR ls).length) (hr : (flatR ls)[q].hr = true)
    {i : Nat} (hi : i < (flatR ls)[q].encRefund.length) :
    bOffs (flatR ls) q - 8 + i < (rfStream ls).length ∧
      (rfStream ls).getD (bOffs (flatR ls) q - 8 + i) 0 = (flatR ls)[q].encRefund.getD i 0 := by
  have hi' : i < (rfS (flatR ls)[q]).length := by simp only [rfS, hr, ite_true]; exact hi
  obtain ⟨h1, h2⟩ := getD_flatMap_at rfS (flatR ls) q hq i hi'
  rw [bOffs_flat, Nat.add_sub_cancel_left]
  refine ⟨h1, ?_⟩
  unfold rfStream
  rw [h2]
  simp only [rfS, hr, ite_true]

/-- The public body length bytes. -/
theorem body_len_pub {p : Prep} {oh : Nat} (hr : ZkFormal.NearV3.Public.RootsSized p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P) :
    leN' (pubBytes (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) PH_BLEN 4) =
      p.body.length := by
  have hpb : pubBytes (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) PH_BLEN 4 =
      (u32 p.body.length).map UInt8.toNat := by
    apply List.ext_getElem (by simp [pubBytes, u32, leN_length])
    intro i h1 h2
    have hi : i < 4 := by simpa [pubBytes] using h1
    simp only [pubBytes, List.getElem_map, List.getElem_range]
    rw [pubNat_prepared, ZkFormal.NearV3.Public.prepared_header p oh hr (by unfold PH_BLEN; omega),
      ZkFormal.NearV3.Public.header_body_length p oh hr hi,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [u32, leN_length] using hi)]
    rfl
  have hlt : p.body.length < 2 ^ 32 := by
    have := ZkFormal.NearV3.Public.prepared_body_size_le p oh hr
    unfold ZkFormal.Algebra.P at hsz; omega
  rw [hpb, ZkFormal.Near.Link.leN'_eq]
  have : toBytes ((u32 p.body.length).map UInt8.toNat) = u32 p.body.length := by
    simp [toBytes, List.map_map, Function.comp_def]
  rw [this, u32, NearSpec.leNat_leN 4 _ hlt]

/-- **The refund stream is the public body after its first eight bytes.** -/
theorem rfStream_body {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    rfStream r.lists = (p.body.drop 8).map UInt8.toNat := by
  have hroots := prepD0_roots hp
  have hbody := ZkFormal.NearV3.Public.prepared_body_size_le p oh hroots
  have hlen : (rfStream r.lists).length = p.body.length - 8 := by
    have := W.lists.body (fun i _ => pubNat_pubOf_lt _ _)
    rw [bOffs_total, body_len_pub hroots hsz] at this
    omega
  apply List.ext_getElem (by simp [hlen])
  intro k hk hk'
  have hkB : 8 + k < p.body.length := by simp at hk'; omega
  -- the public receive `(K_RF, 8 + k, B[8 + k])`
  let M : Msg := [K_RF, 8 + k, (p.body.getD (8 + k) 0).toNat]
  have hpub : 0 < pubCount nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh))
      B_BYTES false M.toFp := by
    have hl256 : (ZkFormal.NearV3.Public.preparedBytes p oh).length < 256 ^ 4 := by unfold ZkFormal.Algebra.P at hsz; omega
    have hI := ZkFormal.NearV3.Public.prepared_receipt_index nearAirV3 p oh rfl hroots
      (prepD0_source_roots hp) hl256
    have hc := (ZkFormal.NearV3.Public.prepared_pubIdx nearAirV3 p oh rfl hroots
      (prepD0_source_roots hp) hl256).count B_BYTES false M.toFp
    rw [show B_BYTES = 0 from rfl, hI.2.2] at hc
    rw [show B_BYTES = 0 from rfl, hc]
    apply List.count_pos_iff.mpr
    apply List.mem_map.mpr
    refine ⟨M, ?_, rfl⟩
    simp only [ZkFormal.NearV3.Public.bodyRecords, List.mem_map, List.mem_range]
    exact ⟨k, by omega, rfl⟩
  -- so it is sent: by the receipt view or another sender
  have hbal := bytes_balance hH T M.toFp
  have e : cnt (rcptSends3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r.lists B_BYTES ++ LinkRidBytes.othersRC tr
      (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) M.toFp =
      cnt (nodeSends3 r.nodes B_BYTES ++ valSends r.values B_BYTES) M.toFp +
        (otherBytes tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r).count M.toFp := by
    unfold cnt LinkRidBytes.othersRC otherBytes otherRecBytes
    simp only [List.map_append, List.count_append, List.map_map]
    rw [show (Msg.toFp ∘ fun x : List Fp => x.map Fp.toNat) = id from funext toFp_map_toNat, List.map_id]
    omega
  have hsend : 0 < cnt (rcptSends3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r.lists B_BYTES ++ LinkRidBytes.othersRC tr
      (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) M.toFp := by omega
  obtain ⟨y, hy, hye⟩ := List.mem_map.mp (List.count_pos_iff.mp hsend)
  have hcnt := W.listsCount
  have hP2 : K_RF < ZkFormal.Algebra.P := by unfold K_RF ZkFormal.Algebra.P; omega
  cases y with
  | nil => simp [Msg.toFp, M] at hye
  | cons a ys =>
    have hhead : Fp.ofNat a = Fp.ofNat K_RF := by
      simp only [Msg.toFp, M, List.map_cons, List.cons.injEq] at hye; exact hye.1
    rcases List.mem_append.mp hy with hy | hy
    · have ha := receipt_bytes_ids hcnt.1 hcnt.2 hy rfl
      have := Near.Link.ofNat_inj ha hP2 hhead
      subst this
      obtain ⟨q, hq, hhr, i, hi, he⟩ := rf_isolate hy rfl
      rw [he] at hye
      simp only [Msg.toFp, M, List.map_cons, List.map_nil, List.cons.injEq] at hye
      obtain ⟨-, e1, e2, -⟩ := hye
      obtain ⟨hat, hav⟩ := rfStream_at hq hhr hi
      have hoff : bOffs (flatR r.lists) q + i = 8 + k := by
        apply Near.Link.ofNat_inj _ (by unfold ZkFormal.Algebra.P at hsz ⊢; omega) e1
        have := bOffs_total r.lists
        have hmono : bOffs (flatR r.lists) q - 8 + i < (rfStream r.lists).length := hat
        have h8 : 8 ≤ bOffs (flatR r.lists) q := by rw [bOffs_flat]; omega
        unfold ZkFormal.Algebra.P at hsz ⊢; omega
      have hval : (flatR r.lists)[q].encRefund.getD i 0 = (p.body.getD (8 + k) 0).toNat := by
        apply Near.Link.ofNat_inj _ (by have := (p.body.getD (8 + k) 0).toNat_lt; unfold ZkFormal.Algebra.P; omega) e2
        obtain ⟨toks, -, -, hwf, -⟩ := W.lists.toks
        have hw := hwf q hq
        rw [getD_eq_getElem' _ 0 hi]
        rcases receipt_rf_values hw _ (List.getElem_mem hi) with hv | hv
        · exact W.lists.canon.2 _ (List.getElem_mem hq) _ (by simp [RcptE.raw3, hv])
        · unfold ZkFormal.Algebra.P; omega
      have h8 : 8 ≤ bOffs (flatR r.lists) q := by rw [bOffs_flat]; omega
      have hk : bOffs (flatR r.lists) q - 8 + i = k := by omega
      rw [hk] at hav
      rw [List.getElem_eq_getD 0, hav, hval, List.getElem_map, List.getElem_drop,
        ← List.getElem_eq_getD (h := hkB) 0]
    · exfalso
      obtain ⟨hlt, hne⟩ := othersRC_kind (Or.inr (Or.inl rfl)) hp hsz hH T W _ hy a rfl
      have := Near.Link.ofNat_inj hlt hP2 hhead
      exact hne (by rw [this]; decide)

/-- **`ramtB`**: refund amounts are bytes. -/
theorem ramtBytes {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ∀ x ∈ flatR r.lists, x.hr = true → Bytes8 x.ramt := by
  intro x hx hr y hy
  have hm : y ∈ rfStream r.lists :=
    List.mem_flatMap.mpr ⟨x, hx, by simp only [rfS, hr, ite_true]; unfold RcptV.encRefund; simp [hy]⟩
  rw [rfStream_body hp hsz hH T W] at hm
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hm
  exact b.toNat_lt

end ZkFormal.NearV3.RcptLink
