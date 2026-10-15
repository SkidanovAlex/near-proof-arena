import ZkFormal.NearV3.D1.Link.RecordsDefs
import ZkFormal.NearV3.D1.Link.MemBound
import ZkFormal.NearV3.D1.M.View
import ZkFormal.NearV3.D1.Extract.AkmProof

/-!
# `ZkFormal.NearV3.D1.Link.Records` — every view of `nearAirV3D1` at once, and the balance (L1)

Lane `v3-d1-phase2`, item L1.  The D1 analogue of `Assembly.LinkV3`'s mechanical part:

* `busCount_nearAirV3D1_explicit`: `busCount nearAirV3D1` as the explicit sum over its 30
  tables (`rfl`);
* `d1Balance_of_holdsP`: `HoldsP.balance` and the exact traffic give `D1Balance`;
* `rcptD1_view_counts`: `rcptD1_view_prep` with D0a's count bounds (`≤ 2^22` lists and
  receipts);
* **`d1Records_of_holdsP`**: records of all viewed tables with their well-formedness and exact
  traffic, from `prepD1`, the tape bound and `HoldsP`;
* **`linkInputsD1_of_holdsP`**: the full link input bundle `LinkInputsD1`.
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpec NearSpecV3 ZkFormal.NearV3.D1
open ZkFormal.NearV3.D1.RcptD1 ZkFormal.NearV3.Assembly

theorem busCount_nearAirV3D1_explicit (tr : Trace Fp) (pub : List Fp) (b : Nat) (s : Bool)
    (m : List Fp) :
    busCount nearAirV3D1.toAir tr pub b s m =
      tableBusCount shaTable.interactions tr T_SHA_T pub b s m +
      (tableBusCount shaTable.interactions tr T_SHA_R pub b s m +
      (tableBusCount ZkFormal.NearV3.UnfoldA7.nodeA7.interactions tr T_NODE pub b s m +
      (tableBusCount ZkFormal.NearV3.HeadV3.interactions tr T_HEAD pub b s m +
      (tableBusCount ZkFormal.NearV3.UnfoldA7.valA7.interactions tr T_VAL pub b s m +
      (tableBusCount ZkFormal.NearV3.WalkV3.interactions tr T_WALK pub b s m +
      (tableBusCount ZkFormal.NearV3.Uniq.interactions tr T_UNIQ pub b s m +
      (tableBusCount ZkFormal.NearV3.UnfoldA7.upsA7.interactions tr T_UPS pub b s m +
      (tableBusCount (ZkFormal.Chacha.Table.table22 ZkFormal.NearV3.Sched.B_SCHACHA).interactions
        tr T_CHACHA pub b s m +
      (tableBusCount (ZkFormal.Chacha.Rng.Table.table22 ZkFormal.NearV3.Sched.B_SCHACHA
        ZkFormal.NearV3.Sched.B_SGEN).interactions tr T_RNG pub b s m +
      (tableBusCount (ZkFormal.Chacha.Shuffle.Table.table22 ZkFormal.NearV3.Sched.B_SSIN
        ZkFormal.NearV3.Sched.B_SSOUT ZkFormal.NearV3.Sched.B_SSMEM ZkFormal.NearV3.Sched.B_SGEN
        ZkFormal.NearV3.Sched.B_SSHUF).interactions tr T_SHUF pub b s m +
      (tableBusCount ZkFormal.NearV3.Sched.Codec.table.interactions tr T_CODEC pub b s m +
      (tableBusCount ZkFormal.NearV3.Sched.ScanDist.table.interactions tr T_SSD pub b s m +
      (tableBusCount ZkFormal.NearV3.Sched.Proc.tableB.interactions tr T_PROC pub b s m +
      (tableBusCount ZkFormal.NearV3.Sched.Mem.table.interactions tr T_MEM pub b s m +
      (tableBusCount (ZkFormal.NearV3.Sched.Cmp.table ZkFormal.NearV3.Sched.B_SCMP).interactions
        tr T_CMP pub b s m +
      (tableBusCount RcptD1.tableQD1.interactions tr 16 pub b s m +
      (tableBusCount ZkFormal.NearV3.AcctV3.interactions tr T_ACCT pub b s m +
      (tableBusCount ZkFormal.NearV3.AkeyV3.interactions tr T_AKEY pub b s m +
      (tableBusCount ZkFormal.NearV3.BndV3.interactions tr T_BND pub b s m +
      (tableBusCount ZkFormal.NearV3.Rcpt.Candidates.DedupTable.interactions tr T_SRCP pub b s m +
      (tableBusCount ZkFormal.NearV3.UnfoldA7.sizeA7.interactions tr T_SIZE pub b s m +
      (tableBusCount ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair.table.interactions
        tr T_QV pub b s m +
      (tableBusCount ZkFormal.NearV3.Candidates.MerkleEmpty.table.interactions tr T_MRK pub b s m +
      (tableBusCount sortTableV3.interactions tr T_SORT pub b s m +
      (tableBusCount TxV3.interactions tr T_TX pub b s m +
      (tableBusCount AkmV3.interactions tr T_AKM pub b s m +
      (tableBusCount KibV3.interactions tr T_KIB pub b s m +
      (tableBusCount PlfV3.interactions tr T_PLF pub b s m +
      (tableBusCount RidV3.interactions tr T_RID pub b s m +
        0))))))))))))))))))))))))))))) := rfl

theorem d1Balance_of_holdsP {pub : List Fp} {tr : Trace Fp} {r : D1Records}
    (hH : HoldsP nearAirV3D1 pub tr) (T : D1RecordsTraffic pub tr r) : D1Balance pub tr r := by
  intro b m
  have hb := hH.balance b m
  rw [busCount_nearAirV3D1_explicit, busCount_nearAirV3D1_explicit] at hb
  simp only [show ZkFormal.NearV3.UnfoldA7.nodeA7.interactions =
      ZkFormal.NearV3.NodeV3.interactions ++ ZkFormal.NearV3.UnfoldA7.Node.interactions from rfl,
    show ZkFormal.NearV3.UnfoldA7.valA7.interactions =
      ZkFormal.NearV3.ValV3.interactions ++ ZkFormal.NearV3.UnfoldA7.Val.interactions from rfl,
    show ZkFormal.NearV3.UnfoldA7.upsA7.interactions =
      ZkFormal.NearV3.UpsV3.interactions ++ ZkFormal.NearV3.UnfoldA7.Ups.interactions from rfl,
    show ZkFormal.NearV3.UnfoldA7.sizeA7.interactions =
      ZkFormal.NearV3.SizeV3.interactions ++ ZkFormal.NearV3.UnfoldA7.Size.interactions from rfl,
    tableBusCount_append] at hb
  rw [tcnt_of_traffic T.base.nodes, tcnt_of_traffic T.base.nodes, tcnt_of_traffic T.base.heads, tcnt_of_traffic T.base.heads, tcnt_of_traffic T.base.values, tcnt_of_traffic T.base.values,
    tcnt_of_traffic T.base.walks, tcnt_of_traffic T.base.walks, tcnt_of_traffic T.base.uniq, tcnt_of_traffic T.base.uniq, tcnt_of_traffic T.base.ups, tcnt_of_traffic T.base.ups,
    tcnt_of_traffic T.base.lists, tcnt_of_traffic T.base.lists, tcnt_of_traffic T.base.accts, tcnt_of_traffic T.base.accts, tcnt_of_traffic T.base.akeys, tcnt_of_traffic T.base.akeys,
    tcnt_of_traffic T.base.bnds, tcnt_of_traffic T.base.bnds, tcnt_of_traffic T.base.srcp, tcnt_of_traffic T.base.srcp, tcnt_of_traffic T.base.size, tcnt_of_traffic T.base.size,
    tcnt_of_traffic T.base.mrk, tcnt_of_traffic T.base.mrk, tcnt_of_traffic T.txs, tcnt_of_traffic T.txs,
    tcnt_of_traffic T.akms, tcnt_of_traffic T.akms, tcnt_of_traffic T.kibs, tcnt_of_traffic T.kibs,
    tcnt_of_traffic T.plfs, tcnt_of_traffic T.plfs, tcnt_of_traffic T.rids, tcnt_of_traffic T.rids] at hb
  unfold balSumD1 balSumBaseD1
  simp only [Nat.add_assoc, Nat.add_zero] at hb ⊢
  exact hb


/-- `rcptD1_view_prep` with the count bounds (`≤ 2^22` lists and receipts; D0a's
`rcptV3_view_counts`). -/
theorem rcptD1_view_counts {cb : Bytes} {h : HintD1} {p : Public.PrepD1} {ov : Nat} {tr : Trace Fp}
    (hp : prepD1 cb h = .ok p) (hlen : (Public.preparedBytesD1 p ov).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p ov)) tr) :
    ∃ ls, RcptV3WfD1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p ov)) ls ∧
      ZkFormal.Near.TableTraffic tableQD1.interactions tr 16 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p ov))
        (rcptTraffic3D1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p ov)) ls) ∧
      ls.length ≤ 2 ^ 22 ∧ (ZkFormal.NearV3.flatR ls).length ≤ 2 ^ 22 ∧
      ∀ x ∈ ZkFormal.NearV3.flatR ls, x.q < 128 := by
  open ZkFormal.NearV3.Assembly.ReceiptCandidateProof in
  open ZkFormal.NearV3.RcptV3Proof (ListBlock ListChain rcptOf) in
  have hx := Public.extOk_of_prepD1 hp ov hlen
  have hr := Public.prepD1_receipt_ranges hp ov hlen
  have hmem := rcptD1_mem_bound hp hlen hH
  have hL : LocalD1 tr 16 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p ov)) :=
    { local_K (rcptD1Local hH) with ext := hx }
  obtain ⟨bs, e, hc⟩ := extract_lists_d1 hL
  have ht := ListChain.view_traffic_d1 hL hc
  have hprov : ∀ B ∈ bs, ∀ y ∈ B.receipts, (rcptOf tr 16 y).tprev ≤ 2 ^ 25 := by
    intro B hB y hy
    have hx' : rcptOf tr 16 y ∈ ZkFormal.NearV3.flatR (bs.map (ListBlock.view tr 16)) := by
      rw [flat_views]
      exact List.mem_map.mpr ⟨y, List.mem_flatMap.mpr ⟨B, hB, hy⟩, rfl⟩
    let x := rcptOf tr 16 y
    let mm : ZkFormal.Near.Msg := [x.kslot, x.tprev, 0, x.bef.getD 0 0, x.lk.getD 0 0, x.st.getD 0 0]
    have hm : mm ∈ ZkFormal.NearV3.rcptRecvs3 (bs.map (ListBlock.view tr 16)) ZkFormal.Near.B_MEM := memory_version_read hx'
    have hp' : 0 < tableBusCount tableQD1.interactions tr 16 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p ov)) ZkFormal.Near.B_MEM false mm.toFp := by
      rw [recv_count_eq hx.1, (ht ZkFormal.Near.B_MEM mm.toFp).2]
      exact List.count_pos_iff.mpr (List.mem_map.mpr ⟨mm, hm, rfl⟩)
    have hb := hmem mm.toFp hp'
    have hc' := extracted_previous_canonical hx'
    simpa [mm, x, ZkFormal.Near.Msg.toFp, Fp.toNat_ofNat, Nat.mod_eq_of_lt hc'] using hb
  have hcnt : (bs.map (ListBlock.view tr 16)).length ≤ 2 ^ 22 ∧
      (ZkFormal.NearV3.flatR (bs.map (ListBlock.view tr 16))).length ≤ 2 ^ 22 := by
    have hlist := ReceiptCandidateProof.ListChain.length_le_rows hc
    have hreceipts := receipt_counts_le_rows bs
    have hrows := ReceiptCandidateProof.ListChain.rows hc
    have hlast := (ListChain.last_row_d1 hL hc).2.1
    have hheight := height_le_d1 hL
    simp only [List.length_map, flat_views_length]
    omega
  refine ⟨_, ListChain.view_wf_d1 hL hc ⟨hr.count, hr.body⟩ hprov, ?_, hcnt.1, hcnt.2, view_q_d1 hL hc⟩
  unfold rcptTraffic3D1
  rw [traffic3G_shift]
  exact traffic_shift hx.1 ht

theorem shaLocalD1 {pub : List Fp} {tr : Trace Fp} (hH : HoldsP nearAirV3D1 pub tr) {t : Nat}
    (ht : t = 0 ∨ t = 1) : ZkFormal.Sha.ShaLocal tr t pub := by
  rcases ht with rfl | rfl
  · exact shaLocal_of_tableLocal (tableLocalD1 hH (T := shaTable) rfl)
  · exact shaLocal_of_tableLocal (tableLocalD1 hH (T := shaTable) rfl)

/-- **All views of `nearAirV3D1` at once.** -/
theorem d1Records_of_holdsP {cb : Bytes} {h : HintD1} {p : Public.PrepD1} {ov : Nat} {tr : Trace Fp}
    (hp : prepD1 cb h = .ok p) (hlen : (Public.preparedBytesD1 p ov).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p ov)) tr) :
    ∃ r, D1RecordsWf (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p ov)) r ∧
      D1RecordsTraffic (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p ov)) tr r := by
  obtain ⟨vs, sN, wN, tN, aN⟩ := ZkFormal.NearV3.nodeA7_view tr _ T_NODE (tableLocalD1 hH (T := ZkFormal.NearV3.UnfoldA7.nodeA7) rfl)
  obtain ⟨hs, wH, tH⟩ := headViewD1 hH
  obtain ⟨es, sV, wV, tV, aV⟩ := ZkFormal.NearV3.valA7_view tr _ T_VAL (tableLocalD1 hH (T := ZkFormal.NearV3.UnfoldA7.valA7) rfl)
  obtain ⟨ws, wW, wS, tW⟩ := walkViewD1 hH
  obtain ⟨us, wU, tU⟩ := uniqViewD1 hH
  obtain ⟨u, wP, tP, aP, aPw⟩ := ZkFormal.NearV3.upsA7_view tr _ T_UPS (tableLocalD1 hH (T := ZkFormal.NearV3.UnfoldA7.upsA7) rfl)
  obtain ⟨ay, aYw, aY⟩ := ZkFormal.NearV3.A7SizeProof.sizeA7_view (tableLocalD1 hH (t := T_SIZE) (T := ZkFormal.NearV3.UnfoldA7.sizeA7) rfl)
  obtain ⟨ls, wR, tR, cR1, cR2, qR⟩ := rcptD1_view_counts hp hlen hH
  obtain ⟨as, wA, tA⟩ := acctViewD1 hH
  obtain ⟨ks, wK, tK⟩ := akeyViewD1 hH
  obtain ⟨bs, wB, tB⟩ := bndViewD1 hH
  obtain ⟨ss, eS, cS, wS', tS'⟩ := ZkFormal.NearV3.srcpDD_view (tableLocalD1 hH (T := ZkFormal.NearV3.SrcpDD.table) (t := T_SRCP) rfl)
  obtain ⟨sz, wZ, tZ⟩ := sizeViewD1 hH
  obtain ⟨me, mv, wM, tM⟩ := ZkFormal.NearV3.D1.MrkD1.mrkViewD1 hH
  obtain ⟨xs, wX, tX⟩ := tx_view tr _ T_TX (txLocal hH)
  obtain ⟨ms, wMs, tMs⟩ := akm_view tr _ T_AKM (akmLocal hH)
  obtain ⟨kb, wKb, tKb⟩ := kib_view tr _ T_KIB (kibLocal hH)
  obtain ⟨pl, wPl, tPl⟩ := plf_view tr _ T_PLF (plfLocal hH)
  obtain ⟨rd, wRd, tRd⟩ := rid_view tr _ T_RID (ridLocal hH)
  exact ⟨⟨⟨vs, hs, es, ws, us, u, ls, as, ks, bs, ss, sz, mv, me, sN, sV, ay, _⟩, xs, ms, kb, pl, rd⟩,
    ⟨⟨wN, wH, wV, wW, wS, wU, wP, wR, wA, wK, wB, wS', wS'.depth, wZ, wM, ⟨cR1, cR2⟩, qR, aYw, aPw⟩,
      wX, wMs, wKb, wPl, wRd⟩,
    ⟨⟨tN, tH, tV, tW, tU, tP, tR, tA, tK, tB, tS', tZ, tM, aN, aV, aP, aY, ⟨eS, cS, rfl⟩⟩,
      tX, tMs, tKb, tPl, tRd⟩⟩

/-- **The link input bundle from `HoldsP`** on the verifier's tape. -/
theorem linkInputsD1_of_holdsP {cb : Bytes} {h : HintD1} {p : Public.PrepD1} {tr : Trace Fp}
    (hp : prepD1 cb h = .ok p) (hlen : (Public.preparedBytesD1 p (txOverhead h)).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3D1 (pubD1 p h) tr) :
    ∃ r, LinkInputsD1 cb h p tr r := by
  obtain ⟨r, hw, ht⟩ := d1Records_of_holdsP hp hlen hH
  exact ⟨r, hp, hlen, hH, hw, ht, shaFactsAt tr _ T_SHA_T (shaLocalD1 hH (Or.inl rfl)),
    shaFactsAt tr _ T_SHA_R (shaLocalD1 hH (Or.inr rfl)), d1Balance_of_holdsP hH ht⟩

end ZkFormal.NearV3.D1.Link
