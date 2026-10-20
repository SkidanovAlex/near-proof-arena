import ZkFormal.NearV3.D1.L.Assembly.LinkSha
import ZkFormal.NearV3.Assembly.LinkShaKinds
import ZkFormal.NearV3.D1.Extract.AkmProof

/-!
# `ZkFormal.NearV3.D1.Link.Kinds` — the `BYTES` kind registry of `nearAirV3D1` (L1)

Lane `v3-d1-phase2`, item L1.  D0a's `OthersKinds` (`Assembly/LinkShaKinds`): every `BYTES`
message sent by a table other than node / val has a canonical id of a kind other than `K_NPRE`,
`K_NPOST`, `K_VPRE`.  The D1 senders it adds:

* the receipt view's sends are `rcptV3D1`'s (`rcptSends3G` with the body offset `O0`): the same
  ids as D0a's (`rcptG_bytes_head`), so `rcptKindsG`;
* `akmV3` sends `VPOST(vid)` (kind `K_VPOST`), and `vid < 2^22`: an `akmV3` row that sends
  `BYTES` also sends `VSLOT (vid)`, which only node records receive (`vslot_bal_d1`), so `vid`
  is a value id (as D0a's `acct_slot_lt`);
* the public body-prefix sends have id `2` (`K_RF`; `pub_bytes_send_head`).

**`extraKinds`** covers `extraBytes` (`D1/Link/ShaExtra`).
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.D1
open ZkFormal.NearV3.Assembly

/-! ## The receipt view's sends -/

theorem rcptG_bytes_head {o0 t0 m0 : Nat} {pub : List Fp} {ls : RcptV3Vs} {x : Msg}
    (hx : x ∈ RcptD1.rcptSends3G o0 t0 m0 pub ls B_BYTES) :
    ∃ x' ∈ rcptSends3 pub ls B_BYTES, x'.head? = x.head? := by
  simp only [RcptD1.rcptSends3G, ite_true, show B_BYTES ≠ B_RCL by decide, ite_false,
    List.append_nil, List.mem_flatMap] at hx
  obtain ⟨j, hj, hx⟩ := hx
  have hin : ∀ y, y ∈ (emitAt (msgId K_RC j) 0 (hdrBytes pub (ls.getD j default)) ++
      (located ls j).flatMap fun (r, o, x) => rSends pub (flatR ls) j r o x B_BYTES) →
      y ∈ rcptSends3 pub ls B_BYTES := by
    intro y hy
    simp only [rcptSends3, ite_true, show B_BYTES ≠ B_RCL by decide, ite_false, List.append_nil,
      List.mem_flatMap]
    exact ⟨j, hj, hy⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact ⟨x, hin x (List.mem_append_left _ hx), rfl⟩
  · obtain ⟨⟨r, o, y⟩, hl, hx⟩ := List.mem_flatMap.mp hx
    have hin' : ∀ z, z ∈ rSends pub (flatR ls) j r o y B_BYTES → z ∈ rcptSends3 pub ls B_BYTES :=
      fun z hz => hin z (List.mem_append_right _ (List.mem_flatMap.mpr ⟨(r, o, y), hl, hz⟩))
    simp only [RcptD1.rSendsG, ite_true, List.mem_append] at hx
    rcases hx with (((hx | hx) | hx) | hx) | hx
    · exact ⟨x, hin' x (by simp only [rSends, ite_true, List.mem_append]; exact .inl (.inl (.inl (.inl hx)))), rfl⟩
    · split at hx
      · rename_i hr
        obtain ⟨i, hi, rfl⟩ := Link3.mem_emitAt3.mp hx
        refine ⟨[K_RF, bOffs (flatR ls) r + i, y.encRefund.getD i 0], hin' _ ?_, rfl⟩
        simp only [rSends, ite_true, List.mem_append, hr, ite_true]
        exact .inl (.inl (.inl (.inr (Link3.mem_emitAt3.mpr ⟨i, hi, rfl⟩))))
      · simp at hx
    · exact ⟨x, hin' x (by simp only [rSends, ite_true, List.mem_append]; exact .inl (.inl (.inr hx))), rfl⟩
    · exact ⟨x, hin' x (by simp only [rSends, ite_true, List.mem_append]; exact .inl (.inr hx)), rfl⟩
    · exact ⟨x, hin' x (by simp only [rSends, ite_true, List.mem_append]; exact .inr hx), rfl⟩

/-- `KindsOk` depends on the heads only. -/
theorem kindsOk_of_heads {l l' : List Msg} (h : KindsOk l)
    (hl : ∀ x ∈ l', ∃ x' ∈ l, x'.head? = x.head?) : KindsOk l' := by
  intro x hx a ha
  obtain ⟨x', hx', he⟩ := hl x hx
  exact h x' hx' a (he.trans ha)

theorem rcptKindsG {o0 t0 m0 : Nat} {pub : List Fp} {ls : RcptV3Vs}
    (hl : ls.length ≤ 2 ^ 22) (hr : (flatR ls).length ≤ 2 ^ 22) :
    KindsOk (RcptD1.rcptSends3G o0 t0 m0 pub ls B_BYTES) :=
  kindsOk_of_heads (rcptKinds hl hr) fun _ hx => rcptG_bytes_head hx

/-! ## `VSLOT` and `akmV3` -/

/-- **`VSLOT`** (D1): the node records' written value slots are the `acctV3` and `akmV3` slot
messages. -/
theorem vslot_bal_d1 {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3D1 pub tr)
    (T : BaseTrafficD1 pub tr r) (m : List Fp) :
    ((acctV3Sends r.accts B_VSLOT).map Msg.toFp).count m +
      tableBusCount AkmV3.interactions tr T_AKM pub B_VSLOT true m =
      ((nodeRecvs3 r.nodes B_VSLOT).map Msg.toFp).count m := by
  have h := bal_users_d1 hH (b := B_VSLOT) (U := [Assembly.T_NODE, Assembly.T_ACCT, 26]) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [node_count_d1 T _ _ _ (by decide +kernel), node_count_d1 T _ _ _ (by decide +kernel),
    show isAtD1 Assembly.T_ACCT = AcctV3.interactions from rfl, tcnt_of_traffic T.accts,
    tcnt_of_traffic T.accts,
    tableBusCount_noside (s := false) (is := isAtD1 26) (by decide +kernel),
    show isAtD1 26 = AkmV3.interactions from rfl] at h
  simp only [tcnt_unfold] at h
  have z1 : nodeSends3 r.nodes B_VSLOT = [] := by
    simp [nodeSends3, B_VSLOT, B_BYTES, B_PARENT, B_VPARENT, B_EDGE, B_BMAP, B_DIGS, B_ENT, B_SIZE, B_UPB]
  have z2 : acctRecvs r.accts B_VSLOT = [] := by
    simp [acctRecvs, B_VSLOT, B_MEM, B_FINAL, B_KEYNIB]
  rw [z1] at h
  simp only [tcnt, acctV3Traffic, ite_true, Bool.false_eq_true, ite_false, z2, List.map_nil,
    List.count_nil, Nat.zero_add, Nat.add_zero] at h
  rw [show T_AKM = 26 from rfl]
  omega

/-- A slot message `[k]` that the node records receive names a value id: `k < 2^22`. -/
theorem vslot_lt {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3D1 pub tr)
    (T : BaseTrafficD1 pub tr r) (W : BaseWfD1 pub r) {k : Nat} (hk : k < P)
    (hc : 0 < ((nodeRecvs3 r.nodes B_VSLOT).map Msg.toFp).count (Msg.toFp [k])) : k < 2 ^ 22 := by
  have hvb := vparentBal_of_d1 hH T
  obtain ⟨x, hx, he⟩ := List.mem_map.mp (List.count_pos_iff.mp hc)
  simp only [nodeRecvs3, show B_VSLOT ≠ B_DIGEST by decide,
    show B_VSLOT ≠ B_PARENT by decide, show B_VSLOT ≠ B_EDGE by decide,
    show B_VSLOT ≠ B_BMAP by decide, show B_VSLOT ≠ B_DUP by decide,
    show B_VSLOT ≠ B_ENT by decide, show B_VSLOT ≠ B_UPB by decide,
    ite_false, ite_true, List.mem_flatMap] at hx
  obtain ⟨⟨s, n⟩, hsn, hx⟩ := hx
  obtain ⟨hn, rfl⟩ := Link3.mem_zip_range hsn
  split at hx
  · rename_i i l pre po hv
    simp only [List.mem_singleton] at hx
    subst hx
    have hlen := Link3.vlen_le W.values
    obtain ⟨t, ht, -, hi, -, -⟩ := Link3.val_pos W.nodes W.values hvb hlen hn hv
    have hvt := Link3.vid_small W.values ht
    simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
    have := ZkFormal.Near.Link.ofNat_inj (by unfold P; omega) hk he
    omega
  · simp at hx

/-- **`akmV3`'s `BYTES` ids** are `VPOST(vid)` with `vid < 2^22`. -/
theorem akm_bytes_head {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3D1 pub tr)
    (T : BaseTrafficD1 pub tr r) (W : BaseWfD1 pub r) {m : List Fp}
    (hm : 0 < tableBusCount AkmV3.interactions tr T_AKM pub B_BYTES true m) :
    ∃ vid < 2 ^ 22, m.head? = some (Fp.ofNat (msgId K_VPOST vid)) := by
  obtain ⟨es, hw, hT⟩ := akm_view tr pub T_AKM (akmLocal hH)
  obtain ⟨v, hv, rfl⟩ := mem_of_count_pos hT hm
  simp only [ite_true, akmTraffic, akmSends, show B_BYTES ≠ B_VBYTES by decide,
    show B_BYTES ≠ B_AKMEM by decide, show B_BYTES ≠ B_VSLOT by decide, ite_false,
    List.mem_flatMap] at hv
  obtain ⟨e, he, hv⟩ := hv
  split at hv
  · rename_i hfa
    -- the row's `VSLOT (vid)` send
    have hs : [e.vid] ∈ (akmTraffic es).sends B_VSLOT := by
      simp only [akmTraffic, akmSends, show B_VSLOT ≠ B_VBYTES by decide,
        show B_VSLOT ≠ B_AKMEM by decide, ite_false, ite_true, List.mem_flatMap]
      exact ⟨e, he, by simp [hfa]⟩
    have hpos : 0 < tableBusCount AkmV3.interactions tr T_AKM pub B_VSLOT true (Msg.toFp [e.vid]) := by
      rw [(hT B_VSLOT _).1]
      exact List.count_pos_iff.mpr (List.mem_map.mpr ⟨_, hs, rfl⟩)
    have hb := vslot_bal_d1 hH T (Msg.toFp [e.vid])
    have hvid := vslot_lt hH T W (hw.segs e he).canon.1 (by omega)
    refine ⟨e.vid, hvid, ?_⟩
    have : ∀ y ∈ (List.range 8).map (fun j => [e.vpost, j, e.pb.getD j 0]) ++ [[e.vpost, 8, e.bytes.getD 8 0]],
        y.head? = some e.vpost := by
      intro y hy
      simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hy
      rcases hy with ⟨j, -, rfl⟩ | rfl <;> rfl
    have h1 := this v hv
    cases v with
    | nil => simp at h1
    | cons a vs =>
      simp only [List.head?_cons, Option.some.injEq] at h1
      subst h1
      rfl
  · simp at hv

/-! ## The public body-prefix sends -/

theorem segs_no_bytes_send :
    ZkFormal.NearV3.Public.preparedSegments.all (fun s => !(s.bus == B_BYTES && s.send == true)) = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
/-- A public `BYTES` send of the verifier's tape is a body-prefix record `(2, 8 + j, byte)`. -/
theorem pub_bytes_send_head (p : Public.PrepD1) (ov : Nat) (hr : ZkFormal.NearV3.Public.RootsSized p.base)
    (hs : ∀ s ∈ p.base.lists, s.root.length = 32) (hleaves : ∀ l ∈ p.leaves, l.length = 32)
    (hlen : (Public.preparedBytesD1 p ov).length < 256 ^ 4) {m : List Fp}
    (hpos : 0 < pubCount nearAirV3D1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p ov)) B_BYTES true m) :
    m.head? = some (Fp.ofNat K_RF) := by
  rw [Public.pubCountD1_split p ov hr hs hlen, pubCount_noside segs_no_bytes_send, Nat.zero_add] at hpos
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hpos
  rw [List.mem_filter, decide_eq_true_eq] at hx
  obtain ⟨hx, rfl⟩ := hx
  rw [Public.newMsgs_eq p ov hr hlen hleaves] at hx
  simp only [List.mem_append] at hx
  rcases hx with (((((h | h) | h) | h) | h) | h) <;> obtain ⟨j, hj, he⟩ := mem_tagged h <;>
    simp only [Prod.mk.injEq] at he
  · rw [he.2.2]
    simp [ZkFormal.NearV3.Public.recordValues, Public.bodyPrefixPlan, K_RF, natCast_eq]
  all_goals exact absurd he.1 (by decide)

/-! ## The registry of the extra senders -/

/-- **The extra `BYTES` senders' ids** (akm: `K_VPOST`, body prefix: `K_RF`) are canonical and of
kinds other than `K_NPRE`/`K_NPOST`/`K_VPRE`. -/
theorem extraKinds {cb : NearSpec.Bytes} {h : HintD1} {q : Public.PrepD1} {ov : Nat} {tr : Trace Fp} {r : V3Records}
    (hp : prepD1 cb h = .ok q) (hlen : (Public.preparedBytesD1 q ov).length < P)
    (hH : HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) tr)
    (T : BaseTrafficD1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) tr r)
    (W : BaseWfD1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) r) :
    ∀ y ∈ extraBytes tr (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)), ∀ a, y.head? = some a →
      a.toNat % 16 ≠ K_NPRE ∧ a.toNat % 16 ≠ K_NPOST ∧ a.toNat % 16 ≠ K_VPRE := by
  intro y hy a ha
  have hP : P < 256 ^ 4 := by unfold P; omega
  have hc : 0 < (extraBytes tr (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov))).count y :=
    List.count_pos_iff.mpr hy
  rw [extraBytes_count] at hc
  rcases Nat.eq_zero_or_pos (tableBusCount AkmV3.interactions tr T_AKM
      (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) B_BYTES true y) with h0 | h0
  · have hpub : 0 < pubCount nearAirV3D1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) B_BYTES true y := by
      omega
    have := pub_bytes_send_head q ov (prepD1_roots hp) (prepD1_source_roots hp) (prepD1_leaves hp)
      (by omega) hpub
    rw [this, Option.some.injEq] at ha
    subst ha
    simp [Fp.toNat_ofNat, K_RF, K_NPRE, K_NPOST, K_VPRE, P]
  · obtain ⟨vid, hv, he⟩ := akm_bytes_head hH T W h0
    rw [he, Option.some.injEq] at ha
    subst ha
    have : msgId K_VPOST vid < P := by unfold msgId K_VPOST P; omega
    rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt this]
    unfold msgId K_VPOST K_NPRE K_NPOST K_VPRE
    omega

/-! ## Node / head digest receives are not leaf ids -/

theorem head_toFp_digMsg (id l : Nat) (d : List Nat) :
    (Msg.toFp (digMsg id l d)).head? = some (Fp.ofNat id) := rfl

theorem digMsg_ne_plf {K n l : Nat} {d : List Nat} (hK : K < 16) (hne : K ≠ K_PLF) (hn : n < 2 ^ 22) :
    ∀ j < 8192, (Msg.toFp (digMsg (msgId K n) l d)).head? ≠ some (Fp.ofNat (K_PLF + 16 * j)) := by
  intro j hj
  rw [head_toFp_digMsg]
  intro he
  exact fp_kind_ne_plf hK hne (by unfold P; omega) hj (Option.some.inj he)

/-- **No node / head `DIGEST` receive has a leaf id** (`K_PLF + 16·j`): their ids are `msgId K n`
with `K ∈ {K_NPRE, K_NPOST, K_VPRE, K_VPOST}` and `n` a node or value id `< 2^22`. -/
theorem nodeHead_digest_nonleaf {pub : List Fp} {tr : Trace Fp} {r : V3Records}
    (hH : HoldsP nearAirV3D1 pub tr) (T : BaseTrafficD1 pub tr r) (W : BaseWfD1 pub r) :
    ∀ m, 0 < cnt (nodeRecvs3 r.nodes B_DIGEST ++ headRecvs r.heads B_DIGEST) m →
      ∀ j < 8192, m.head? ≠ some (Fp.ofNat (K_PLF + 16 * j)) := by
  intro m hm
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.count_pos_iff.mp hm)
  have hpb := parentBal_of_d1 hH T
  have hvb := vparentBal_of_d1 hH T
  have hcnt := W.nodes.count
  rcases List.mem_append.mp hx with hx | hx
  · simp only [nodeRecvs3, ite_true, List.mem_flatMap] at hx
    obtain ⟨⟨s, n⟩, hsn, hx⟩ := hx
    obtain ⟨hn, rfl⟩ := Link3.mem_zip_range hsn
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨⟨c, l, r', pre, po⟩, hk, hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨hc, -⟩ := Link3.kid_link W.nodes hpb hn hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact digMsg_ne_plf (by decide) (by decide) (by omega)
      · exact digMsg_ne_plf (by decide) (by decide) (by omega)
    · split at hx
      · rename_i i l pre po w hv
        have hlen := Link3.vlen_le W.values
        obtain ⟨t, ht, -, hi, -, -⟩ := Link3.val_pos W.nodes W.values hvb hlen hn hv
        have hvt := Link3.vid_small W.values ht
        have hi' : i < 2 ^ 22 := by omega
        rcases List.mem_append.mp hx with hx | hx
        · simp only [List.mem_singleton] at hx; subst hx
          exact digMsg_ne_plf (by decide) (by decide) hi'
        · split at hx
          · simp only [List.mem_singleton] at hx; subst hx
            exact digMsg_ne_plf (by decide) (by decide) hi'
          · simp at hx
      · simp at hx
  · simp only [headRecvs, ite_true, List.mem_flatMap] at hx
    obtain ⟨h, hh, hx⟩ := hx
    obtain ⟨hr, -⟩ := Link3.head_link W.nodes W.heads hpb hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact digMsg_ne_plf (by decide) (by decide) (by omega)
    · exact digMsg_ne_plf (by decide) (by decide) (by omega)

/-- `M0` on the verifier's tape is at most `2·NT0`. -/
theorem m0V_le {cb : NearSpec.Bytes} {h : HintD1} {q : Public.PrepD1} {ov : Nat} (hp : prepD1 cb h = .ok q) :
    RcptD1.m0V (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 q ov)) ≤ 2 ^ 22 := by
  have hm := (prepD1_m0_t0 hp).1
  unfold NearSpecV3.NT0 at hm
  rw [Public.m0V_prepared q ov (prepD1_roots hp) (by omega)]
  omega

end ZkFormal.NearV3.D1.Link
