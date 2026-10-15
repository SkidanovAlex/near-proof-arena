/-
Hand-written deltas for the generated D1 link copies (`scripts/rcpt_d1_copy.py --profile link`,
lane v3-d1-phase2, L1).  Not a Lean module.  Format as `rcpt_d1_overrides.lean`:

* `-- @override <D0a constant>`: the following text replaces the copy of that declaration;
* `-- @patch <D0a constant>` with `<<<` old `===` new `>>>`: a textual replacement in the
  generated module of that declaration.

In the copies `p : Prep` stands for `q.base` (`q : PrepD1`); statements without a preparation
hypothesis take `q.base = p` as an auto-param (`d1_base`, `D1/Link/Base`).
-/

-- @override ZkFormal.NearV3.Public.prepared_header
/-- The D1 tape's header after the tag (`d1_hdr`: `26 ≤ j`) is D0a's header of `p = q.base`. -/
theorem prepared_header_d1 (p : Prep) {q : ZkFormal.NearV3.D1.Public.PrepD1} (witnessOverhead : Nat)
    (hr : RootsSized p) {j : Nat} (hj : j < 202) (h26 : 26 ≤ j := by d1_hdr)
    (hq : q.base = p := by d1_base) :
    (ZkFormal.NearV3.D1.Public.preparedBytesD1 q witnessOverhead).getD j 0 = (headerBytes p witnessOverhead).getD j 0 :=
  ZkFormal.NearV3.D1.Link.preparedD1_header_base p witnessOverhead hr hj h26 hq

-- @override ZkFormal.NearV3.Public.prepared_body_size_le
theorem prepared_body_size_le_d1 (p : Prep) {q : ZkFormal.NearV3.D1.Public.PrepD1} (witnessOverhead : Nat)
    (hr : RootsSized p) (hq : q.base = p := by d1_base) :
    p.body.length ≤ (ZkFormal.NearV3.D1.Public.preparedBytesD1 q witnessOverhead).length :=
  ZkFormal.NearV3.D1.Link.bodyD1_le p witnessOverhead hr hq

-- @override ZkFormal.NearV3.Public.prepared_segment_msgs
theorem prepared_segment_msgs_d1 (p : Prep) {q : ZkFormal.NearV3.D1.Public.PrepD1} (witnessOverhead : Nat)
    (hr : RootsSized p) (hs : ∀ s ∈ p.lists, s.root.length = 32)
    (hlen : (ZkFormal.NearV3.D1.Public.preparedBytesD1 q witnessOverhead).length < 256^4)
    (seg : PubSeg) (hseg : seg ∈ ZkFormal.NearV3.D1.Public.preparedSegmentsD1)
    (hq : q.base = p := by d1_base) (hleaves : ∀ l ∈ q.leaves, l.length = 32 := by d1_leaves) :
    seg.msgs (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q witnessOverhead)) =
      (ZkFormal.NearV3.D1.Link.preparedRecordsD1 q seg).map (·.map Fp.ofNat) := by
  subst hq
  exact ZkFormal.NearV3.D1.Link.preparedD1_segment_msgs q witnessOverhead hr hs hleaves hlen seg hseg

-- @override ZkFormal.NearV3.Public.prepared_pubIdx
/-- The public-bus index of the D1 tape (`ZkFormal.NearV3.D1.Link.preparedD1_pubIdx`). -/
def prepared_pubIdx_d1 (AP : AirP) (p : Prep) {q : ZkFormal.NearV3.D1.Public.PrepD1} (witnessOverhead : Nat)
    (hseg : AP.pubSegs = ZkFormal.NearV3.D1.Public.preparedSegmentsD1)
    (hr : RootsSized p) (hs : ∀ s ∈ p.lists, s.root.length = 32)
    (hlen : (ZkFormal.NearV3.D1.Public.preparedBytesD1 q witnessOverhead).length < 256^4)
    (hq : q.base = p := by d1_base) (hleaves : ∀ l ∈ q.leaves, l.length = 32 := by d1_leaves) :
    PubIdx AP (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q witnessOverhead)) Fp.ofNat :=
  ZkFormal.NearV3.D1.Link.preparedD1_pubIdx AP q witnessOverhead hseg (by rw [hq]; exact hr)
    (by rw [hq]; exact hs) hleaves hlen

-- @override ZkFormal.NearV3.Public.prepared_pubIdx_recs
/-- Off the six new `(bus, side)` pairs the D1 records are D0a's. -/
theorem prepared_pubIdx_recs_d1 (AP : AirP) (p : Prep) {q : ZkFormal.NearV3.D1.Public.PrepD1} (witnessOverhead : Nat)
    (hseg : AP.pubSegs = ZkFormal.NearV3.D1.Public.preparedSegmentsD1)
    (hr : RootsSized p) (hs : ∀ s ∈ p.lists, s.root.length = 32)
    (hlen : (ZkFormal.NearV3.D1.Public.preparedBytesD1 q witnessOverhead).length < 256^4) (bus : Nat) (side : Bool)
    (hq : q.base = p) (hleaves : ∀ l ∈ q.leaves, l.length = 32)
    (hb : (bus, side) ∉ ZkFormal.NearV3.D1.Link.newPairs) :
    (prepared_pubIdx_d1 AP p witnessOverhead hseg hr hs hlen hq hleaves).recs bus side = preparedOn p bus side := by
  subst hq
  exact ZkFormal.NearV3.D1.Link.preparedD1_pubIdx_recs AP q witnessOverhead hseg _ _ hleaves hlen bus side hb

-- @patch ZkFormal.NearV3.Public.prepared_receipt_index
<<<
  simp only [prepared_pubIdx_recs_d1]
===
  rw [prepared_pubIdx_recs_d1 AP p witnessOverhead hseg hr hs hlen B_SRC true hq_base hq_leaves (by decide),
    prepared_pubIdx_recs_d1 AP p witnessOverhead hseg hr hs hlen B_BNDP true hq_base hq_leaves (by decide),
    prepared_pubIdx_recs_d1 AP p witnessOverhead hseg hr hs hlen 0 false hq_base hq_leaves (by decide)]
>>>

-- @override ZkFormal.NearV3.Sched.prepD0_sched
theorem prepD0_sched_d1 {cb : Bytes} {hint : ZkFormal.NearV3.D1.HintD1} {p : Prep}
    {q : ZkFormal.NearV3.D1.Public.PrepD1} (h : (ZkFormal.NearV3.D1.prepD1 cb hint = .ok q ∧ q.base = p)) :
    ∀ sp ∈ p.sched, SchedPubOk sp := by
  obtain ⟨hp, rfl⟩ := h
  exact ZkFormal.NearV3.D1.prepD1_sched hp

-- @override ZkFormal.NearV3.Sched.prepD0_seed
theorem prepD0_seed_d1 {cb : Bytes} {hint : ZkFormal.NearV3.D1.HintD1} {p : Prep}
    {q : ZkFormal.NearV3.D1.Public.PrepD1} (h : (ZkFormal.NearV3.D1.prepD1 cb hint = .ok q ∧ q.base = p)) :
    ∀ sp ∈ p.sched, sp.seed.length = 32 := by
  obtain ⟨hp, rfl⟩ := h
  exact ZkFormal.NearV3.D1.prepD1_seed hp

-- @override ZkFormal.NearV3.Sched.prepD0_len
theorem prepD0_len_d1 {cb : Bytes} {hint : ZkFormal.NearV3.D1.HintD1} {p : Prep}
    {q : ZkFormal.NearV3.D1.Public.PrepD1} (h : (ZkFormal.NearV3.D1.prepD1 cb hint = .ok q ∧ q.base = p)) :
    p.sched.length ≤ 33 := by
  obtain ⟨hp, rfl⟩ := h
  exact ZkFormal.NearV3.D1.prepD1_len hp

-- @override ZkFormal.NearV3.Sched.prepD0_fwd_lt
theorem prepD0_fwd_lt_d1 {cb : Bytes} {hint : ZkFormal.NearV3.D1.HintD1} {p : Prep}
    {q : ZkFormal.NearV3.D1.Public.PrepD1} (h : (ZkFormal.NearV3.D1.prepD1 cb hint = .ok q ∧ q.base = p)) :
    ∀ x ∈ p.fwd, x.2 < 2 ^ 24 := by
  obtain ⟨hp, rfl⟩ := h
  exact ZkFormal.NearV3.D1.prepD1_fwd_lt hp

-- @override ZkFormal.NearV3.Sched.prepD0_fwd_links
/-- D1: the claim part is `prepClaimD1`'s. -/
theorem prepD0_fwd_links_d1 {cb : Bytes} {hint : ZkFormal.NearV3.D1.HintD1} {p : Prep}
    {q : ZkFormal.NearV3.D1.Public.PrepD1} (h : (ZkFormal.NearV3.D1.prepD1 cb hint = .ok q ∧ q.base = p)) :
    ∃ pc refunds, ZkFormal.NearV3.D1.prepClaimD1 cb = .ok pc ∧ p.fwd = fwdLinks pc.pc.ctxB2 refunds := by
  obtain ⟨hp, rfl⟩ := h
  exact ZkFormal.NearV3.D1.prepD1_fwd_links hp

-- @override ZkFormal.NearV3.RcptV3Proof.prepD0_count_bound
/-- D1: `PH_N = M0 + n ≤ 2·NT0 + 5000` (`Link/Count`; D0a: `n ≤ 5000`). -/
theorem prepD0_count_bound_d1 {cb : Bytes} {hint : ZkFormal.NearV3.D1.HintD1} {p : Prep}
    {q : ZkFormal.NearV3.D1.Public.PrepD1} (h : (ZkFormal.NearV3.D1.prepD1 cb hint = .ok q ∧ q.base = p)) :
    p.hdr.n ≤ 13192 ∧ p.hdr.n < Algebra.P := by
  obtain ⟨hp, rfl⟩ := h
  have := (ZkFormal.NearV3.D1.Link.prepD1_hdr_n hp).2
  exact ⟨this, by unfold Algebra.P; omega⟩

-- @override ZkFormal.NearV3.Assembly.LinkRcptWalk.flatR_le
/-- At most `W_AK` receipts: the view has the hint's `n ≤ 5000` receipts (`Link/Count`). -/
theorem flatR_le_d1 (hp : (ZkFormal.NearV3.D1.prepD1 cb h = .ok q ∧ q.base = p))
    (W : ZkFormal.NearV3.D1.Link.BaseWfD1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) r) :
    (flatR r.lists).length ≤ W_AK := by
  rw [ZkFormal.NearV3.D1.Link.rcpt_count_d1 hp.1 W.lists]
  have := ZkFormal.NearV3.D1.Link.prepD1_hn_le hp.1
  unfold W_AK; omega

-- @override ZkFormal.NearV3.RcptLink.flatR_le_WAK
/-- `|flatR| ≤ W_AK` (`= 8192`): `|flatR| = h.n ≤ 5000` (`Link/Count`). -/
theorem flatR_le_WAK_d1 {cb : NearSpec.Bytes} {h : ZkFormal.NearV3.D1.HintD1} {p : NearSpecV3.Prep}
    {q : ZkFormal.NearV3.D1.Public.PrepD1}
    (hp : (ZkFormal.NearV3.D1.prepD1 cb h = .ok q ∧ q.base = p)) {ls : RcptV3Vs} (hn : h.n = (flatR ls).length) :
    (flatR ls).length ≤ W_AK := by
  have := ZkFormal.NearV3.D1.Link.prepD1_hn_le hp.1
  have : W_AK = 8192 := rfl
  omega

-- @override ZkFormal.NearV3.Assembly.receiptCount_of_records
/-- **`receiptCount`**: the D1 receipt view counts `|flatR| + M0 = PH_N = M0 + n` (`Link/Count`). -/
theorem receiptCount_of_records_d1 {cb : Bytes} {h : ZkFormal.NearV3.D1.HintD1} {p : Prep}
    {q : ZkFormal.NearV3.D1.Public.PrepD1} {oh : Nat}
    {ls : ZkFormal.NearV3.RcptV3Vs} (hp : (ZkFormal.NearV3.D1.prepD1 cb h = .ok q ∧ q.base = p))
    (hw : ZkFormal.NearV3.D1.RcptD1.RcptV3WfD1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) ls)
    (x : ExtV3) (hx : x.receipts = ls) :
    h.n = x.applied.length := by
  rw [← ZkFormal.NearV3.D1.Link.rcpt_count_d1 hp.1 hw]
  simp only [ExtV3.applied, hx, ZkFormal.NearV3.flatR, List.length_flatMap, List.length_map]

-- @patch ZkFormal.NearV3.Public.prepared_scheduler_index
<<<
  simp only [prepared_pubIdx_recs_d1]
===
  rw [prepared_pubIdx_recs_d1 AP p witnessOverhead hseg hr hs hlen B_SPUBB true hp.2
      (ZkFormal.NearV3.D1.prepD1_leaves hp.1) (by decide),
    prepared_pubIdx_recs_d1 AP p witnessOverhead hseg hr hs hlen B_SPAR true hp.2
      (ZkFormal.NearV3.D1.prepD1_leaves hp.1) (by decide),
    prepared_pubIdx_recs_d1 AP p witnessOverhead hseg hr hs hlen B_SDL true hp.2
      (ZkFormal.NearV3.D1.prepD1_leaves hp.1) (by decide),
    prepared_pubIdx_recs_d1 AP p witnessOverhead hseg hr hs hlen B_SDL false hp.2
      (ZkFormal.NearV3.D1.prepD1_leaves hp.1) (by decide)]
>>>

-- @patch ZkFormal.NearV3.Assembly.prepClaim_root_endpoints
<<<
      have hi : w_22=i_3 := by
        have hh : List.findIdx? (fun b => match b.slots[w_20]? with
          | some (s,_) => s.heightIncluded == b.hdr.height
          | none => false) w_13=some w_22 := heq_1
        have hh' : List.findIdx? (fun b => match b.slots[w_20]? with
          | some (s,_) => s.heightIncluded == b.hdr.height
          | none => false) w_13=some i_3 := heq_6
        exact Option.some.inj (hh.symm.trans hh')
      have hs : w_30=p_1.2 := by
===
      have hi : w_21=i_3 := by
        have hh : List.findIdx? (fun b => match b.slots[w_19]? with
          | some (s,_) => s.heightIncluded == b.hdr.height
          | none => false) w_12=some w_21 := heq_1
        have hh' : List.findIdx? (fun b => match b.slots[w_19]? with
          | some (s,_) => s.heightIncluded == b.hdr.height
          | none => false) w_12=some i_3 := heq_6
        exact Option.some.inj (hh.symm.trans hh')
      have hs : w_29=p_1.2 := by
>>>

-- @patch ZkFormal.NearV3.Assembly.LinkPrepCtx.prepClaim_context_of
<<<
      have hb2 : w_23 = i_3 := by grind only
      have hslot : p_1.2 = w_31 := by
===
      have hb2 : w_22 = i_3 := by grind only
      have hslot : p_1.2 = w_30 := by
>>>

-- @override ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.prepD0_body_eq
-- (D1: the body is `u32 |newTxs| ‖ newTxs ‖ encodeReceipts outgoing`, not a hint field; the
-- semantic delta is hand-written, `D1/Link/Body`)

-- @override ZkFormal.NearV3.RcptLink.prepD0_fwd
-- (D1: the forwarding facts cover the outgoing receipts `fwd ++ local refunds ++ refunds`;
-- hand-written delta)

-- @patch ZkFormal.NearV3.Public.prepared_root_index
<<<
  simp only [prepared_pubIdx_recs_d1]
===
  rw [prepared_pubIdx_recs_d1 AP p witnessOverhead hseg _ hs hlen B_ROOT true hp.2
      (ZkFormal.NearV3.D1.prepD1_leaves hp.1) (by decide),
    prepared_pubIdx_recs_d1 AP p witnessOverhead hseg _ hs hlen B_ROOT false hp.2
      (ZkFormal.NearV3.D1.prepD1_leaves hp.1) (by decide)]
>>>

-- @patch ZkFormal.NearV3.RcptLink.gasPrice_pub
<<<
    rw [pubNat_prepared_d1, prepared_gasPrice_byte_d1 p oh i hroots hi,
===
    rw [pubNat_prepared_d1 p (q := q) oh (PH_GP + i), prepared_gasPrice_byte_d1 p oh i hroots hi,
>>>

-- @patch ZkFormal.NearV3.Assembly.walkD0_of_prepClaim
<<<
    simp only [mapError_ok_iff', pure, Except.pure, Except.ok.injEq] at hs_1 hs_2 hs_6 hs_14 hs_21 hs_23 hs_24 hs_27 hs_30 hs_31
    subst hs_21; subst hs_23; subst hs_24; subst hs_27; subst hs_30; subst hs_31
    have h20 := check_ok hs_20
    have h32 := check_ok hs_32
    have h34 := check_ok hs_34
    have h35 := check_ok hs_35
    have h37 := check_ok hs
    unfold walkD0
    simp only [hs_1, hs_2, hs_6, hs_14, heq, bind, Except.bind, pure, Except.pure]
===
    simp only [mapError_ok_iff', pure, Except.pure, Except.ok.injEq] at hs_1 hs_2 hs_6 hs_13 hs_20 hs_22 hs_23 hs_26 hs_29 hs_30
    subst hs_20; subst hs_22; subst hs_23; subst hs_26; subst hs_29; subst hs_30
    have h20 := check_ok hs_19
    have h32 := check_ok hs_31
    have h35 := check_ok hs_33
    have h37 := check_ok hs
    unfold walkD0
    simp only [hs_1, hs_2, hs_6, hs_13, heq, bind, Except.bind, pure, Except.pure]
>>>

-- @patch ZkFormal.NearV3.Assembly.walkD0_of_prepClaim
<<<
        refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · simpa only [beq_iff_eq] using h34
        · simpa only [Bool.and_eq_true, beq_iff_eq, and_assoc] using h35
===
        refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
        · simpa only [Bool.and_eq_true, beq_iff_eq, and_assoc] using h35
>>>

-- @override ZkFormal.NearV3.Assembly.goodV3_of_parts
-- (D1: the top of the chain is `GoodD1Core`, hand-written)

-- @override ZkFormal.NearV3.Assembly.goodV3_of_ext
-- (D1: the top of the chain is `GoodD1Core`, hand-written)

-- @override ZkFormal.NearV3.Assembly.LinkV3Stmt
-- (D1: replaced by `D1/Link/RecordsDefs`, `Records`, `Statements`)

-- @override ZkFormal.NearV3.Assembly.LinkCoreV3Stmt
-- (D1: replaced by `D1/Link/RecordsDefs`, `Records`, `Statements`)

-- @override ZkFormal.NearV3.Assembly.balSum
-- (D1: replaced by `D1/Link/RecordsDefs`, `Records`, `Statements`)

-- @override ZkFormal.NearV3.Assembly.busCount_nearAirV3_explicit
-- (D1: replaced by `D1/Link/RecordsDefs`, `Records`, `Statements`)

-- @override ZkFormal.NearV3.Assembly.extractV3_of_link
-- (D1: replaced by `D1/Link/RecordsDefs`, `Records`, `Statements`)

-- @override ZkFormal.NearV3.Assembly.linkV3_of_core
-- (D1: replaced by `D1/Link/RecordsDefs`, `Records`, `Statements`)

-- @override ZkFormal.NearV3.Assembly.v3Balance_of_holdsP
-- (D1: replaced by `D1/Link/RecordsDefs`, `Records`, `Statements`)

-- @override ZkFormal.NearV3.Assembly.v3Records_of_holdsP
-- (D1: replaced by `D1/Link/RecordsDefs`, `Records`, `Statements`)

-- @patch ZkFormal.NearV3.Assembly.busCount_users
<<<
(hUn : ∀ t ∈ U, t < 25)
===
(hUn : ∀ t ∈ U, t < 30)
>>>

-- @patch ZkFormal.NearV3.Assembly.bal_users
<<<
(hUn : ∀ t ∈ U, t < 25)
===
(hUn : ∀ t ∈ U, t < 30)
>>>

-- @override ZkFormal.NearV3.Assembly.digest_users_eq
/-- **D1: the SHA union and `plfV3` provide every `DIGEST` message received elsewhere** (`plfV3`
sends the public outcome leaves, `D1/Link/PlfIds`). -/
theorem digest_users_eq_d1 {pub : List Fp} {tr : Trace Fp} (hH : HoldsP ZkFormal.NearV3.D1.nearAirV3D1 pub tr)
    (m : List Fp) :
    shaU tr pub true B_DIGEST m +
      tableBusCount ZkFormal.NearV3.D1.PlfV3.interactions tr ZkFormal.NearV3.D1.T_PLF pub B_DIGEST true m =
      (digestRecvTables.map fun t => tableBusCount (ZkFormal.NearV3.D1.Link.isAtD1 t) tr t pub B_DIGEST false m).sum := by
  have h := hH.balance B_DIGEST m
  rw [pubCount_nobus_d1 (by decide +kernel), pubCount_nobus_d1 (by decide +kernel),
    busCount_users_d1 (U := [T_SHA_T, T_SHA_R, T_NODE, T_HEAD, T_UPS, T_CODEC, T_RCPT, T_SRCP, T_MRK, 28])
      (by decide) (by decide) (by decide +kernel),
    busCount_users_d1 (U := [T_SHA_T, T_SHA_R, T_NODE, T_HEAD, T_UPS, T_CODEC, T_RCPT, T_SRCP, T_MRK, 28])
      (by decide) (by decide) (by decide +kernel)] at h
  have r0 : tableBusCount (ZkFormal.NearV3.D1.Link.isAtD1 T_SHA_T) tr T_SHA_T pub B_DIGEST false m = 0 :=
    (shaFactsAt tr pub T_SHA_T (shaLocal_of_tableLocal (tableLocal_of_holdsP hH getElem?_sha_t_d1))).recvs_only_bytes
      B_DIGEST m (by decide)
  have r1 : tableBusCount (ZkFormal.NearV3.D1.Link.isAtD1 T_SHA_R) tr T_SHA_R pub B_DIGEST false m = 0 :=
    (shaFactsAt tr pub T_SHA_R (shaLocal_of_tableLocal (tableLocal_of_holdsP hH getElem?_sha_r_d1))).recvs_only_bytes
      B_DIGEST m (by decide)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [r0, r1,
    tableBusCount_noside (is := ZkFormal.NearV3.D1.Link.isAtD1 T_NODE) (by decide +kernel),
    tableBusCount_noside (is := ZkFormal.NearV3.D1.Link.isAtD1 T_HEAD) (by decide +kernel),
    tableBusCount_noside (is := ZkFormal.NearV3.D1.Link.isAtD1 T_UPS) (by decide +kernel),
    tableBusCount_noside (is := ZkFormal.NearV3.D1.Link.isAtD1 T_CODEC) (by decide +kernel),
    tableBusCount_noside (is := ZkFormal.NearV3.D1.Link.isAtD1 T_RCPT) (by decide +kernel),
    tableBusCount_noside (is := ZkFormal.NearV3.D1.Link.isAtD1 T_SRCP) (by decide +kernel),
    tableBusCount_noside (is := ZkFormal.NearV3.D1.Link.isAtD1 T_MRK) (by decide +kernel),
    tableBusCount_noside (s := false) (is := ZkFormal.NearV3.D1.Link.isAtD1 28) (by decide +kernel)] at h
  rw [shaU_eq, show ZkFormal.NearV3.Assembly.isAt T_SHA_T = ZkFormal.NearV3.D1.Link.isAtD1 T_SHA_T from rfl,
    show ZkFormal.NearV3.Assembly.isAt T_SHA_R = ZkFormal.NearV3.D1.Link.isAtD1 T_SHA_R from rfl,
    show ZkFormal.NearV3.D1.PlfV3.interactions = ZkFormal.NearV3.D1.Link.isAtD1 28 from rfl,
    show ZkFormal.NearV3.D1.T_PLF = 28 from rfl]
  simp only [digestRecvTables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

-- @override ZkFormal.NearV3.Assembly.digest_provided
/-- D1: a received `DIGEST` message whose id is not a leaf id (`K_PLF + 16·j`) is a SHA output. -/
theorem digest_provided_d1 {pub : List Fp} {tr : Trace Fp} (hH : HoldsP ZkFormal.NearV3.D1.nearAirV3D1 pub tr)
    (hS : ZkFormal.NearV3.D1.Link.PlfSmall pub tr)
    {t : Nat} (ht : t ∈ digestRecvTables) {m : List Fp}
    (hk : ∀ j < 8192, m.head? ≠ some (Fp.ofNat (ZkFormal.NearV3.D1.K_PLF + 16 * j)))
    (hm : 0 < tableBusCount (ZkFormal.NearV3.D1.Link.isAtD1 t) tr t pub B_DIGEST false m) :
    0 < shaU tr pub true B_DIGEST m := by
  have h := digest_users_eq_d1 hH m
  have h0 : tableBusCount ZkFormal.NearV3.D1.PlfV3.interactions tr ZkFormal.NearV3.D1.T_PLF pub B_DIGEST true m = 0 := by
    rcases Nat.eq_zero_or_pos (tableBusCount ZkFormal.NearV3.D1.PlfV3.interactions tr ZkFormal.NearV3.D1.T_PLF pub
      B_DIGEST true m) with h0 | h0
    · exact h0
    · obtain ⟨j, hj, he⟩ := hS m h0
      exact absurd he (hk j hj)
  have := Nat.lt_of_lt_of_le hm (nat_le_sum_of_mem (List.mem_map.mpr ⟨t, ht, rfl⟩) :
    tableBusCount (ZkFormal.NearV3.D1.Link.isAtD1 t) tr t pub B_DIGEST false m ≤
      (digestRecvTables.map fun t => tableBusCount (ZkFormal.NearV3.D1.Link.isAtD1 t) tr t pub B_DIGEST false m).sum)
  omega

-- @override ZkFormal.NearV3.Assembly.otherBytes
/-- All `BYTES` sends other than node / val, as field messages (D1: with `akmV3` and the public
body-prefix sends, `D1/Link/ShaExtra`). -/
def otherBytes_d1 (tr : Trace Fp) (pub : List Fp) (r : ZkFormal.NearV3.Assembly.V3Records) : List (List Fp) :=
  (otherRecBytes_d1 pub r).map Msg.toFp ++ codecBytes tr pub ++ ZkFormal.NearV3.D1.Link.extraBytes tr pub

-- @override ZkFormal.NearV3.Assembly.bytes_balance
/-- **The `BYTES` balance** (D1): SHA receives + public body receives = all `BYTES` sends. -/
theorem bytes_balance_d1 {pub : List Fp} {tr : Trace Fp} {r : ZkFormal.NearV3.Assembly.V3Records}
    (hH : HoldsP ZkFormal.NearV3.D1.nearAirV3D1 pub tr)
    (T : ZkFormal.NearV3.D1.Link.BaseTrafficD1 pub tr r) (m : List Fp) :
    shaU tr pub false B_BYTES m + pubCount ZkFormal.NearV3.D1.nearAirV3D1 pub B_BYTES false m =
      cnt (ZkFormal.NearV3.nodeSends3 r.nodes B_BYTES ++ ZkFormal.NearV3.valSends r.values B_BYTES) m +
        (otherBytes_d1 tr pub r).count m := by
  have h := hH.balance B_BYTES m
  have U : [T_SHA_T, T_SHA_R, T_NODE, T_VAL, T_UPS, T_CODEC, T_RCPT, T_ACCT, T_SRCP, T_MRK, 26].Nodup := by decide
  rw [busCount_users_d1 U (by decide) (by decide +kernel), busCount_users_d1 U (by decide) (by decide +kernel)] at h
  have s0 : tableBusCount (ZkFormal.NearV3.D1.Link.isAtD1 T_SHA_T) tr T_SHA_T pub B_BYTES true m = 0 :=
    (shaFactsAt tr pub T_SHA_T (shaLocal_of_tableLocal (tableLocal_of_holdsP hH getElem?_sha_t_d1))).sends_only_digest
      B_BYTES m (by decide)
  have s1 : tableBusCount (ZkFormal.NearV3.D1.Link.isAtD1 T_SHA_R) tr T_SHA_R pub B_BYTES true m = 0 :=
    (shaFactsAt tr pub T_SHA_R (shaLocal_of_tableLocal (tableLocal_of_holdsP hH getElem?_sha_r_d1))).sends_only_digest
      B_BYTES m (by decide)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [s0, s1,
    tableBusCount_noside (s := false) (is := ZkFormal.NearV3.D1.Link.isAtD1 T_NODE) (by decide +kernel),
    tableBusCount_noside (s := false) (is := ZkFormal.NearV3.D1.Link.isAtD1 T_VAL) (by decide +kernel),
    tableBusCount_noside (s := false) (is := ZkFormal.NearV3.D1.Link.isAtD1 T_UPS) (by decide +kernel),
    tableBusCount_noside (s := false) (is := ZkFormal.NearV3.D1.Link.isAtD1 T_CODEC) (by decide +kernel),
    tableBusCount_noside (s := false) (is := ZkFormal.NearV3.D1.Link.isAtD1 T_RCPT) (by decide +kernel),
    tableBusCount_noside (s := false) (is := ZkFormal.NearV3.D1.Link.isAtD1 T_ACCT) (by decide +kernel),
    tableBusCount_noside (s := false) (is := ZkFormal.NearV3.D1.Link.isAtD1 T_SRCP) (by decide +kernel),
    tableBusCount_noside (s := false) (is := ZkFormal.NearV3.D1.Link.isAtD1 T_MRK) (by decide +kernel),
    tableBusCount_noside (s := false) (is := ZkFormal.NearV3.D1.Link.isAtD1 26) (by decide +kernel),
    node_count_d1 T _ _ _ (by decide +kernel), val_count_d1 T _ _ _ (by decide +kernel),
    ups_count_d1 T _ _ _ (by decide +kernel),
    show ZkFormal.NearV3.D1.Link.isAtD1 T_RCPT = ZkFormal.NearV3.D1.RcptD1.tableQD1.interactions from rfl,
    show T_RCPT = 16 from rfl, tcnt_of_traffic T.lists,
    show ZkFormal.NearV3.D1.Link.isAtD1 T_ACCT = ZkFormal.NearV3.AcctV3.interactions from rfl, tcnt_of_traffic T.accts,
    show ZkFormal.NearV3.D1.Link.isAtD1 T_SRCP = ZkFormal.NearV3.Rcpt.Candidates.DedupTable.interactions from rfl,
    tcnt_of_traffic T.srcp,
    show ZkFormal.NearV3.D1.Link.isAtD1 T_MRK = ZkFormal.NearV3.Candidates.MerkleEmpty.table.interactions from rfl,
    tcnt_of_traffic T.mrk, tableBusCount_eq (ZkFormal.NearV3.D1.Link.isAtD1 T_CODEC),
    show ZkFormal.NearV3.D1.Link.isAtD1 26 = ZkFormal.NearV3.D1.AkmV3.interactions from rfl] at h
  rw [shaU_eq, show ZkFormal.NearV3.Assembly.isAt T_SHA_T = ZkFormal.NearV3.D1.Link.isAtD1 T_SHA_T from rfl,
    show ZkFormal.NearV3.Assembly.isAt T_SHA_R = ZkFormal.NearV3.D1.Link.isAtD1 T_SHA_R from rfl]
  simp only [otherBytes_d1, otherRecBytes_d1, codecBytes, cnt, List.map_append, List.count_append,
    ZkFormal.NearV3.D1.Link.extraBytes_count, ZkFormal.NearV3.D1.RcptD1.rcptTraffic3D1,
    show ZkFormal.NearV3.D1.T_AKM = 26 from rfl]
  rw [show ZkFormal.NearV3.Assembly.isAt T_CODEC = ZkFormal.NearV3.D1.Link.isAtD1 T_CODEC from rfl]
  simp only [tcnt, ZkFormal.NearV3.nodeTraffic3, ZkFormal.NearV3.valTraffic, ZkFormal.NearV3.D1.RcptD1.rcptTraffic3D1,
    ZkFormal.NearV3.acctV3Traffic, ite_true] at h
  omega

-- @override ZkFormal.NearV3.Assembly.shaHyp_of
/-- **`ShaHyp` of the trie tables** (D1): as D0a's, given that `plfV3`'s leaf ids are small
(`PlfSmall`) and that no node / head digest receive has a leaf id (`hN`). -/
theorem shaHyp_of_d1 {pub : List Fp} {tr : Trace Fp} {r : ZkFormal.NearV3.Assembly.V3Records}
    (hH : HoldsP ZkFormal.NearV3.D1.nearAirV3D1 pub tr)
    (T : ZkFormal.NearV3.D1.Link.BaseTrafficD1 pub tr r) (hK : OthersKinds_d1 tr pub r) (hB : BodyOk_d1 pub r)
    (hS : ZkFormal.NearV3.D1.Link.PlfSmall pub tr)
    (hN : ∀ m, 0 < cnt (ZkFormal.NearV3.nodeRecvs3 r.nodes B_DIGEST ++ ZkFormal.NearV3.headRecvs r.heads B_DIGEST) m →
      ∀ j < 8192, m.head? ≠ some (Fp.ofNat (ZkFormal.NearV3.D1.K_PLF + 16 * j))) :
    ZkFormal.NearV3.Link3.ShaHyp r.nodes r.heads r.values (othersBytes_d1 tr pub r)
      (shaU tr pub true) (shaU tr pub false) := by
  refine ⟨shaU_facts_d1 hH, ?_, ?_, ?_⟩
  · intro m
    have h := bytes_balance_d1 hH T m
    have hc : cnt (othersBytes_d1 tr pub r) m = (otherBytes_d1 tr pub r).count m - pubCount ZkFormal.NearV3.D1.nearAirV3D1 pub B_BYTES false m := by
      unfold cnt othersBytes_d1
      rw [List.map_map, show (Msg.toFp ∘ fun x : List Fp => x.map Fp.toNat) = id from
        funext toFp_map_toNat, List.map_id, count_eraseAll, count_pubList_d1]
    rw [show ZkFormal.NearV3.nodeSends3 r.nodes B_BYTES ++ ZkFormal.NearV3.valSends r.values B_BYTES ++
        othersBytes_d1 tr pub r = (ZkFormal.NearV3.nodeSends3 r.nodes B_BYTES ++
          ZkFormal.NearV3.valSends r.values B_BYTES) ++ othersBytes_d1 tr pub r from rfl]
    have hca : cnt ((ZkFormal.NearV3.nodeSends3 r.nodes B_BYTES ++ ZkFormal.NearV3.valSends r.values B_BYTES) ++
        othersBytes_d1 tr pub r) m = cnt (ZkFormal.NearV3.nodeSends3 r.nodes B_BYTES ++
          ZkFormal.NearV3.valSends r.values B_BYTES) m + cnt (othersBytes_d1 tr pub r) m := by
      unfold cnt; rw [List.map_append, List.count_append]
    rw [hca, hc]
    rcases Nat.eq_zero_or_pos (pubCount ZkFormal.NearV3.D1.nearAirV3D1 pub B_BYTES false m) with h0 | h0
    · omega
    · have := hB m h0; omega
  · intro y hy a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have hx' := (eraseAll_sublist _ _).subset hx
    cases hxh : x.head? with
    | none => simp [List.head?_map, hxh] at ha
    | some e =>
      simp only [List.head?_map, hxh, Option.map_some, Option.some.injEq] at ha
      subst ha
      exact ⟨Fp.toNat_lt e, hK x hx' e hxh⟩
  · intro m hm
    have hk := hN m hm
    unfold cnt at hm
    rw [List.map_append, List.count_append] at hm
    rcases Nat.eq_zero_or_pos (((ZkFormal.NearV3.nodeRecvs3 r.nodes B_DIGEST).map Msg.toFp).count m) with h0 | h0
    · rw [h0, Nat.zero_add] at hm
      apply digest_provided_d1 hH hS (t := T_HEAD) (by decide) hk
      rw [head_count_d1 T]; exact hm
    · apply digest_provided_d1 hH hS (t := T_NODE) (by decide) hk
      rw [node_count_d1 T _ _ _ (by decide +kernel)]; exact h0

-- @override ZkFormal.NearV3.Assembly.otherRecBytes
/-- The record-form `BYTES` sends of the viewed tables other than node / val (D1: the receipt
view's sends are `rcptV3D1`'s, with the body offset `O0`). -/
def otherRecBytes_d1 (pub : List Fp) (r : ZkFormal.NearV3.Assembly.V3Records) : List Msg :=
  (ZkFormal.NearV3.upsTraffic r.ups).sends B_BYTES ++
    (ZkFormal.NearV3.D1.RcptD1.rcptTraffic3D1 pub r.lists).sends B_BYTES ++
    ZkFormal.NearV3.acctV3Sends r.accts B_BYTES ++ (ZkFormal.NearV3.ddTraffic r.srcp r.srcpRep).sends B_BYTES ++
    (mrkTrafficE pub r.mrkE r.mrk).sends B_BYTES

-- @override ZkFormal.NearV3.Assembly.othersKinds_of
/-- **`OthersKinds` from the per-sender registries** (D1: the receipt view's sends are
`rcptV3D1`'s; `hE` covers `akmV3` and the public body-prefix sends, `D1/Link/Kinds`). -/
theorem othersKinds_of_d1 {tr : Trace Fp} {pub : List Fp} {r : ZkFormal.NearV3.Assembly.V3Records}
    (hU : KindsOk ((ZkFormal.NearV3.upsTraffic r.ups).sends B_BYTES))
    (hR : KindsOk ((ZkFormal.NearV3.D1.RcptD1.rcptTraffic3D1 pub r.lists).sends B_BYTES))
    (hA : KindsOk (ZkFormal.NearV3.acctV3Sends r.accts B_BYTES))
    (hS : KindsOk ((ZkFormal.NearV3.ddTraffic r.srcp r.srcpRep).sends B_BYTES))
    (hM : KindsOk ((mrkTrafficE pub r.mrkE r.mrk).sends B_BYTES))
    (hC : ∀ y ∈ codecBytes tr pub, ∀ a, y.head? = some a →
      a.toNat % 16 ≠ K_NPRE ∧ a.toNat % 16 ≠ K_NPOST ∧ a.toNat % 16 ≠ K_VPRE)
    (hE : ∀ y ∈ ZkFormal.NearV3.D1.Link.extraBytes tr pub, ∀ a, y.head? = some a →
      a.toNat % 16 ≠ K_NPRE ∧ a.toNat % 16 ≠ K_NPOST ∧ a.toNat % 16 ≠ K_VPRE) :
    OthersKinds_d1 tr pub r := by
  intro y hy
  simp only [otherBytes_d1, otherRecBytes_d1, List.mem_append, List.mem_map] at hy
  rcases hy with (⟨x, hx, rfl⟩ | hy) | hy
  · apply kindOk_toFp
    rcases hx with ((((hx | hx) | hx) | hx) | hx)
    · exact hU x hx
    · exact hR x hx
    · exact hA x hx
    · exact hS x hx
    · exact hM x hx
  · exact hC y hy
  · exact hE y hy

-- @override ZkFormal.NearV3.Assembly.rcptKinds_of
/-- The receipt registry (D1: `rcptV3D1`'s sends have D0a's ids, `D1/Link/Kinds`). -/
theorem rcptKinds_of_d1 {pub : List Fp} {r : ZkFormal.NearV3.Assembly.V3Records}
    (W : ZkFormal.NearV3.D1.Link.BaseWfD1 pub r) :
    KindsOk ((ZkFormal.NearV3.D1.RcptD1.rcptTraffic3D1 pub r.lists).sends B_BYTES) :=
  ZkFormal.NearV3.D1.Link.rcptKindsG W.listsCount.1 W.listsCount.2

-- @override ZkFormal.NearV3.Assembly.vslot_bal
/-- **`VSLOT`** (D1): node records' written value slots = `acctV3`'s + `akmV3`'s slot messages. -/
theorem vslot_bal_d1 {pub : List Fp} {tr : Trace Fp} {r : ZkFormal.NearV3.Assembly.V3Records}
    (hH : HoldsP ZkFormal.NearV3.D1.nearAirV3D1 pub tr)
    (T : ZkFormal.NearV3.D1.Link.BaseTrafficD1 pub tr r) (m : List Fp) :
    ((ZkFormal.NearV3.acctV3Sends r.accts B_VSLOT).map Msg.toFp).count m +
      tableBusCount ZkFormal.NearV3.D1.AkmV3.interactions tr ZkFormal.NearV3.D1.T_AKM pub B_VSLOT true m =
      ((ZkFormal.NearV3.nodeRecvs3 r.nodes B_VSLOT).map Msg.toFp).count m :=
  ZkFormal.NearV3.D1.Link.vslot_bal_d1 hH T m

-- @patch ZkFormal.NearV3.Assembly.acct_slot_lt
<<<
  rw [vslot_bal_d1 hH T] at hc
===
  replace hc : 0 < ((ZkFormal.NearV3.nodeRecvs3 r.nodes B_VSLOT).map Msg.toFp).count (Msg.toFp [a.k]) := by
    have := vslot_bal_d1 hH T (Msg.toFp [a.k]); omega
>>>

-- @override ZkFormal.NearV3.Assembly.mrk_n_le
/-- The mrk node count (D1): `v.n` is the public `n = M0 + |receipts|`, so `≤ 2^23` given
`M0 ≤ 2^22`. -/
theorem mrk_n_le_d1 {pub : List Fp} {r : ZkFormal.NearV3.Assembly.V3Records} (W : ZkFormal.NearV3.D1.Link.BaseWfD1 pub r)
    (hpb : ∀ i, pubNat pub i < 256) (hm0 : ZkFormal.NearV3.D1.RcptD1.m0V pub ≤ 2 ^ 22) (he : r.mrkE = false) :
    r.mrk.n ≤ 2 ^ 23 := by
  have hw : MrkWf (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic pub) r.mrk := by
    have := W.mrk; simpa [MrkWfE, he] using this
  have hb : ∀ x, x < 4 → pubNat (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic pub) (PV_N + x) < 256 :=
    fun x hx => by rw [alias_n pub x hx]; exact hpb _
  have hc := W.lists.count (fun i _ => hpb _)
  have hpe : pubBytes (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic pub) PV_N 4 =
      pubBytes pub ZkFormal.NearV3.PH_N 4 := by
    unfold pubBytes
    apply List.map_congr_left
    intro j hj
    exact alias_n pub j (List.mem_range.mp hj)
  have hn := ZkFormal.Near.Link.nPubNat_eq _ hb
  rw [hpe, ← hc] at hn
  have hlt := W.listsCount.2
  rw [hw.nfix hb (by rw [hn]; unfold P; omega), hn]
  omega

-- @override ZkFormal.NearV3.Assembly.mrkKindIn
theorem mrkKindIn_d1 {pub : List Fp} {r : ZkFormal.NearV3.Assembly.V3Records} (W : ZkFormal.NearV3.D1.Link.BaseWfD1 pub r)
    (hpb : ∀ i, pubNat pub i < 256) (hm0 : ZkFormal.NearV3.D1.RcptD1.m0V pub ≤ 2 ^ 22) :
    ∀ x ∈ (mrkTrafficE pub r.mrkE r.mrk).sends B_BYTES, KindIn [K_MRK] x := by
  cases he : r.mrkE
  · have hn := mrk_n_le_d1 W hpb hm0 he
    have hw : MrkWf (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic pub) r.mrk := by
      have := W.mrk; simpa [MrkWfE, he] using this
    have hl : r.mrk.nodes.length ≤ 2 ^ 24 := by
      rw [hw.shape.1]
      have := mrkLevels_length2 (r.mrk.n + 1) 1 r.mrk.n
      unfold mrkShape; omega
    intro x hx
    simp only [mrkTrafficE, Bool.false_eq_true, ite_false, mrkTraffic, mrkSends, ite_true,
      List.mem_flatMap] at hx
    obtain ⟨⟨nd, q⟩, hq, hx⟩ := hx
    obtain ⟨hql, -⟩ := ZkFormal.NearV3.Link3.mem_zip_range hq
    cases nd with
    | promoted => simp at hx
    | hashed lI lL l rI rL rr =>
      obtain ⟨j, -, rfl⟩ := ZkFormal.NearV3.Link3.mem_emitAt3.mp hx
      have := ZkFormal.Near.Link.hashedBefore_le r.mrk.nodes q
      dsimp only
      exact kindIn_msgId (by decide) (by unfold msgId K_MRK P; omega)
  · intro x hx
    simp [mrkTrafficE] at hx

-- @override ZkFormal.NearV3.Assembly.mrkKinds
theorem mrkKinds_d1 {pub : List Fp} {r : ZkFormal.NearV3.Assembly.V3Records} (W : ZkFormal.NearV3.D1.Link.BaseWfD1 pub r)
    (hpb : ∀ i, pubNat pub i < 256) (hm0 : ZkFormal.NearV3.D1.RcptD1.m0V pub ≤ 2 ^ 22) :
    KindsOk ((mrkTrafficE pub r.mrkE r.mrk).sends B_BYTES) :=
  kindsOk_of_kindIn (mrkKindIn_d1 W hpb hm0) (by decide)

-- @patch ZkFormal.NearV3.Assembly.othersKinds_holds
<<<
    (mrkKinds_d1 W (pubNat_pubOf_lt _)) (codecKinds_d1 hp hsz hH)
===
    (mrkKinds_d1 W (pubNat_pubOf_lt _) (ZkFormal.NearV3.D1.Link.m0V_le hp.1)) (codecKinds_d1 hp hsz hH)
    (ZkFormal.NearV3.D1.Link.extraKinds hp.1 hsz hH T W)
>>>

-- @patch ZkFormal.NearV3.Assembly.shaHyp_holds
<<<
  shaHyp_of_d1 hH T (othersKinds_holds_d1 hp hsz hH T W) (bodyOk_of_d1 hp hsz W)
===
  shaHyp_of_d1 hH T (othersKinds_holds_d1 hp hsz hH T W) (bodyOk_of_d1 hp hsz W)
    (ZkFormal.NearV3.D1.Link.plfSmall_of hp.1 hsz hH) (ZkFormal.NearV3.D1.Link.nodeHead_digest_nonleaf hH T W)
>>>

-- @override ZkFormal.NearV3.Assembly.LinkRids.rids_bal
/-- **`RIDS`** (D1: users rcpt, sort and `ridV3`; `D1/Link/Rids`). -/
theorem rids_bal_d1 {pub : List Fp} {tr : Trace Fp} {r : ZkFormal.NearV3.Assembly.V3Records}
    {es : List ZkFormal.NearV3.D1.RidE} (hH : HoldsP ZkFormal.NearV3.D1.nearAirV3D1 pub tr)
    (T : ZkFormal.NearV3.D1.Link.BaseTrafficD1 pub tr r)
    (hT : TableTraffic ZkFormal.NearV3.D1.RidV3.interactions tr ZkFormal.NearV3.D1.T_RID pub
      (ZkFormal.NearV3.D1.ridTraffic es)) :
    (rcptSends3 pub r.lists B_RIDS = [] ∧ ZkFormal.NearV3.D1.ridSends es B_RIDS = []) ∨
      ∃ ids, SortWf ids ∧ ((rcptSends3 pub r.lists B_RIDS ++ ZkFormal.NearV3.D1.ridSends es B_RIDS).map
        Msg.toFp).Perm (((sortTraffic ids).recvs B_RIDS).map Msg.toFp) :=
  ZkFormal.NearV3.D1.Link.ridsBalD1 hH T hT

-- @override ZkFormal.NearV3.Assembly.LinkRids.receiptIds_of_ridBytes
open ZkFormal.Near.Link in
/-- **`receiptIds`** (D1): the local ids (`q.rids`) followed by the incoming receipts' ids are
pairwise distinct (`D1/Link/Rids`, with the `ridV3` range interface `RidLRange`). -/
theorem receiptIds_of_ridBytes_d1 {cb : NearSpec.Bytes} {h : ZkFormal.NearV3.D1.HintD1}
    {q : _root_.ZkFormal.NearV3.D1.Public.PrepD1} {ov : Nat} {tr : Trace Fp} {r : ZkFormal.NearV3.Assembly.V3Records}
    {es : List ZkFormal.NearV3.D1.RidE} (hp : ZkFormal.NearV3.D1.prepD1 cb h = .ok q)
    (hlen : (ZkFormal.NearV3.D1.Public.preparedBytesD1 q ov).length < P)
    (hH : HoldsP ZkFormal.NearV3.D1.nearAirV3D1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q ov)) tr)
    (T : ZkFormal.NearV3.D1.Link.BaseTrafficD1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q ov)) tr r)
    (W : ZkFormal.NearV3.D1.Link.BaseWfD1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q ov)) r)
    (hW : ZkFormal.NearV3.D1.RidWf es)
    (hT : TableTraffic ZkFormal.NearV3.D1.RidV3.interactions tr ZkFormal.NearV3.D1.T_RID
      (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q ov)) (ZkFormal.NearV3.D1.ridTraffic es))
    (hl : ZkFormal.NearV3.D1.Link.RidLRange es)
    (hrid : ∀ x ∈ flatR r.lists, Bytes8 x.rid) (hrs : (flatR r.lists).length ≤ ZkFormal.NearV3.D1.W_LOC) :
    (q.rids ++ (flatR r.lists).map fun x => x.toRcptV.toReceipt.receiptId).Nodup :=
  ZkFormal.NearV3.D1.Link.receiptIdsD1 hp hlen hH T W hW hT hl hrid hrs

-- @override ZkFormal.NearV3.Assembly.LinkRids.receiptIds_ext
/-- **`MainExecutionD1.distinctIds`** for the reconstruction whose receipts are the receipt view's
lists (with `localIds = q.rids`). -/
theorem receiptIds_ext_d1 {cb : NearSpec.Bytes} {h : ZkFormal.NearV3.D1.HintD1}
    {q : _root_.ZkFormal.NearV3.D1.Public.PrepD1} {ov : Nat} {tr : Trace Fp} {r : ZkFormal.NearV3.Assembly.V3Records}
    {es : List ZkFormal.NearV3.D1.RidE} (hp : ZkFormal.NearV3.D1.prepD1 cb h = .ok q)
    (hlen : (ZkFormal.NearV3.D1.Public.preparedBytesD1 q ov).length < P)
    (hH : HoldsP ZkFormal.NearV3.D1.nearAirV3D1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q ov)) tr)
    (T : ZkFormal.NearV3.D1.Link.BaseTrafficD1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q ov)) tr r)
    (W : ZkFormal.NearV3.D1.Link.BaseWfD1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q ov)) r)
    (hW : ZkFormal.NearV3.D1.RidWf es)
    (hT : TableTraffic ZkFormal.NearV3.D1.RidV3.interactions tr ZkFormal.NearV3.D1.T_RID
      (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q ov)) (ZkFormal.NearV3.D1.ridTraffic es))
    (hl : ZkFormal.NearV3.D1.Link.RidLRange es)
    (hrid : ∀ x ∈ flatR r.lists, Bytes8 x.rid) (hrs : (flatR r.lists).length ≤ ZkFormal.NearV3.D1.W_LOC)
    (x : ExtV3) (hx : x.receipts = r.lists) :
    (q.rids ++ x.applied.map NearSpec.Receipt.receiptId).Nodup := by
  have h := receiptIds_of_ridBytes_d1 hp hlen hH T W hW hT hl hrid hrs
  simp only [ExtV3.applied, hx, List.map_flatMap, List.map_map]
  simp only [flatR, List.map_flatMap] at h
  exact h

-- @override ZkFormal.NearV3.Assembly.LinkRidBytes.othersRC
/-- The `BYTES` senders other than rcpt (D1: with `akmV3` and the public body-prefix sends). -/
def othersRC_d1 (tr : Trace Fp) (pub : List Fp) (r : ZkFormal.NearV3.Assembly.V3Records) : List Msg :=
  nodeSends3 r.nodes B_BYTES ++ valSends r.values B_BYTES ++ (upsTraffic r.ups).sends B_BYTES ++
    acctV3Sends r.accts B_BYTES ++ (ddTraffic r.srcp r.srcpRep).sends B_BYTES ++
    (mrkTrafficE pub r.mrkE r.mrk).sends B_BYTES ++ (codecBytes tr pub).map (fun x => x.map Fp.toNat) ++
    (ZkFormal.NearV3.D1.Link.extraBytes tr pub).map fun x => x.map Fp.toNat

-- @override ZkFormal.NearV3.Assembly.LinkRidBytes.sha_le_rc
/-- D1: the SHA union's `BYTES` receives are covered by `rcptV3D1`'s sends and the others. -/
theorem sha_le_rc_d1 {pub : List Fp} {tr : Trace Fp} {r : ZkFormal.NearV3.Assembly.V3Records}
    (hH : HoldsP ZkFormal.NearV3.D1.nearAirV3D1 pub tr)
    (T : ZkFormal.NearV3.D1.Link.BaseTrafficD1 pub tr r) (m : List Fp) :
    shaU tr pub false B_BYTES m ≤ cnt (ZkFormal.NearV3.D1.RcptD1.rcptSends3G (ZkFormal.NearV3.D1.RcptD1.o0V pub)
      (ZkFormal.NearV3.D1.RcptD1.t0V pub) (ZkFormal.NearV3.D1.RcptD1.m0V pub) pub r.lists B_BYTES ++
        othersRC_d1 tr pub r) m := by
  have h := bytes_balance_d1 hH T m
  have e : cnt (ZkFormal.NearV3.D1.RcptD1.rcptSends3G (ZkFormal.NearV3.D1.RcptD1.o0V pub)
      (ZkFormal.NearV3.D1.RcptD1.t0V pub) (ZkFormal.NearV3.D1.RcptD1.m0V pub) pub r.lists B_BYTES ++
        othersRC_d1 tr pub r) m =
      cnt (nodeSends3 r.nodes B_BYTES ++ valSends r.values B_BYTES) m + (otherBytes_d1 tr pub r).count m := by
    unfold cnt othersRC_d1 otherBytes_d1 otherRecBytes_d1
    simp only [List.map_append, List.count_append, List.map_map, ZkFormal.NearV3.D1.RcptD1.rcptTraffic3D1,
      ZkFormal.NearV3.D1.RcptD1.rcptTraffic3G]
    rw [show (Msg.toFp ∘ fun x : List Fp => x.map Fp.toNat) = id from funext toFp_map_toNat]
    simp only [List.map_id]
    omega
  omega

-- @override ZkFormal.NearV3.Assembly.LinkRidBytes.othersRC_kinds
/-- No other `BYTES` sender uses an id of kind `K_RC` (D1: with the extra senders). -/
theorem othersRC_kinds_d1 {cb : NearSpec.Bytes} {h : ZkFormal.NearV3.D1.HintD1} {p : NearSpecV3.Prep}
    {q : ZkFormal.NearV3.D1.Public.PrepD1} {oh : Nat}
    {tr : Trace Fp} {r : ZkFormal.NearV3.Assembly.V3Records} (hp : (ZkFormal.NearV3.D1.prepD1 cb h = .ok q ∧ q.base = p))
    (hsz : (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh).length < P)
    (hH : HoldsP ZkFormal.NearV3.D1.nearAirV3D1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) tr)
    (T : ZkFormal.NearV3.D1.Link.BaseTrafficD1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) tr r)
    (W : ZkFormal.NearV3.D1.Link.BaseWfD1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) r) :
    ∀ m ∈ othersRC_d1 tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) r, ∀ a,
      m.head? = some a → a < P ∧ a % 16 ≠ K_RC := by
  have kin : ∀ {K : Nat} {x : Msg}, KindIn [K] x → K ≠ K_RC → ∀ a, x.head? = some a →
      a < P ∧ a % 16 ≠ K_RC := by
    intro K x hk hK a ha
    obtain ⟨h1, h2⟩ := hk a ha
    rw [List.mem_singleton] at h2
    exact ⟨h1, h2 ▸ hK⟩
  have nv : ∀ {K n : Nat}, (K = K_NPRE ∨ K = K_NPOST ∨ K = K_VPRE) → n < 2 ^ 22 →
      msgId K n < P ∧ msgId K n % 16 ≠ K_RC := by
    intro K n hK hn
    unfold msgId P
    rcases hK with rfl | rfl | rfl <;> simp only [K_NPRE, K_NPOST, K_VPRE, K_RC] <;> omega
  intro m hm a ha
  simp only [othersRC_d1, List.mem_append] at hm
  rcases hm with ((((((hm | hm) | hm) | hm) | hm) | hm) | hm) | hm
  · obtain ⟨K, n, hh, hK, hn⟩ := nodeVal_bytes_head W.nodes W.values (List.mem_append_left _ hm)
    rw [ha, Option.some.injEq] at hh; subst hh
    exact nv hK hn
  · obtain ⟨K, n, hh, hK, hn⟩ := nodeVal_bytes_head W.nodes W.values (List.mem_append_right _ hm)
    rw [ha, Option.some.injEq] at hh; subst hh
    exact nv hK hn
  · exact kin (upsKindIn_of_d1 hp hsz hH T W m hm) (by decide) a ha
  · exact kin (acctKindIn_d1 hH T W m hm) (by decide) a ha
  · exact kin (ddKindIn W.srcp m hm) (by decide) a ha
  · exact kin (mrkKindIn_d1 W (pubNat_pubOf_lt _) (ZkFormal.NearV3.D1.Link.m0V_le hp.1) m hm) (by decide) a ha
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
    cases hyh : y.head? with
    | none => simp [List.head?_map, hyh] at ha
    | some e =>
      simp only [List.head?_map, hyh, Option.map_some, Option.some.injEq] at ha
      subst ha
      have := codecKindIn_d1 hp hsz hH y hy e hyh
      exact ⟨Fp.toNat_lt e, by rw [this]; decide⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
    cases hyh : y.head? with
    | none => simp [List.head?_map, hyh] at ha
    | some e =>
      simp only [List.head?_map, hyh, Option.map_some, Option.some.injEq] at ha
      subst ha
      exact ⟨Fp.toNat_lt e, ZkFormal.NearV3.D1.Link.extraKinds_rc hp.1 hsz hH T W y hy e hyh⟩

-- @patch ZkFormal.NearV3.Assembly.LinkRidBytes.rcl_block
<<<
  rw [show ZkFormal.NearV3.D1.Link.isAtD1 T_RCPT = RcptV3.interactions from rfl, tcnt_of_traffic T.lists, tcnt_of_traffic T.lists,
===
  rw [show ZkFormal.NearV3.D1.Link.isAtD1 T_RCPT = ZkFormal.NearV3.D1.RcptD1.tableQD1.interactions from rfl,
    show T_RCPT = 16 from rfl, tcnt_of_traffic T.lists, tcnt_of_traffic T.lists,
>>>

-- @patch ZkFormal.NearV3.Assembly.LinkRidBytes.rcl_block
<<<
    simp only [tcnt, ite_true, ZkFormal.NearV3.D1.RcptD1.rcptTraffic3D1]
    exact List.count_pos_iff.mpr (List.mem_map_of_mem hs)
  simp only [tcnt, ite_true, Bool.false_eq_true, ite_false, ZkFormal.NearV3.D1.RcptD1.rcptTraffic3D1, r0, s0, List.map_nil,
===
    simp only [tcnt, ite_true, ZkFormal.NearV3.D1.RcptD1.rcptTraffic3D1, ZkFormal.NearV3.D1.RcptD1.rcptTraffic3G,
      ZkFormal.NearV3.D1.Link.rcptSends3G_rcl]
    exact List.count_pos_iff.mpr (List.mem_map_of_mem hs)
  simp only [tcnt, ite_true, Bool.false_eq_true, ite_false, ZkFormal.NearV3.D1.RcptD1.rcptTraffic3D1,
    ZkFormal.NearV3.D1.RcptD1.rcptTraffic3G, r0, s0, List.map_nil,
>>>

-- @patch ZkFormal.NearV3.Assembly.LinkRidBytes.encBytes
<<<
    apply digest_provided_d1 hH (t := T_SRCP) (by decide)
===
    have hj22 : j < 2 ^ 22 := by have := W.listsCount.1; omega
    apply digest_provided_d1 hH (ZkFormal.NearV3.D1.Link.plfSmall_of hp.1 hsz hH) (t := T_SRCP) (by decide)
      (ZkFormal.NearV3.D1.Link.digMsg_ne_plf (by decide) (by decide) hj22)
>>>

-- @patch ZkFormal.NearV3.Assembly.LinkRidBytes.encBytes
<<<
  obtain ⟨hb8, -⟩ := RcptLink.list_sha_digest_d1 W.lists W.listsCount.1 W.listsCount.2 hsha
===
  obtain ⟨hb8, -⟩ := ZkFormal.NearV3.D1.Link.list_sha_digest_G W.lists W.listsCount.1 W.listsCount.2 hsha
>>>

-- @override ZkFormal.NearV3.Assembly.LinkRidBytes.receiptIds_of
/-- **`MainExecutionD1.distinctIds`** for the reconstruction whose receipts are the receipt view's
lists (D1: local ids `q.rids` first; the `ridV3` range interface `RidLRange`). -/
theorem receiptIds_of_d1 {cb : NearSpec.Bytes} {h : ZkFormal.NearV3.D1.HintD1} {p : NearSpecV3.Prep}
    {q : ZkFormal.NearV3.D1.Public.PrepD1} {oh : Nat}
    {tr : Trace Fp} {r : ZkFormal.NearV3.Assembly.V3Records} {es : List ZkFormal.NearV3.D1.RidE}
    (hp : (ZkFormal.NearV3.D1.prepD1 cb h = .ok q ∧ q.base = p))
    (hsz : (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh).length < P)
    (hH : HoldsP ZkFormal.NearV3.D1.nearAirV3D1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) tr)
    (T : ZkFormal.NearV3.D1.Link.BaseTrafficD1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) tr r)
    (W : ZkFormal.NearV3.D1.Link.BaseWfD1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) r)
    (hW : ZkFormal.NearV3.D1.RidWf es)
    (hT : TableTraffic ZkFormal.NearV3.D1.RidV3.interactions tr ZkFormal.NearV3.D1.T_RID
      (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) (ZkFormal.NearV3.D1.ridTraffic es))
    (hl : ZkFormal.NearV3.D1.Link.RidLRange es)
    (x : ExtV3) (hx : x.receipts = r.lists) :
    (q.rids ++ x.applied.map NearSpec.Receipt.receiptId).Nodup := by
  have hn := ZkFormal.NearV3.D1.Link.rcpt_count_d1 hp.1 W.lists
  have h5 := ZkFormal.NearV3.D1.Link.prepD1_hn_le hp.1
  exact LinkRids.receiptIds_ext_d1 hp.1 hsz hH T W hW hT hl (ridBytes_d1 hp hsz hH T W)
    (by unfold ZkFormal.NearV3.D1.W_LOC; omega) x hx

-- @override ZkFormal.NearV3.Assembly.LinkKeynib.keynib_bal
/-- **`KEYNIB`** (D1): walk receives = rcpt sends + qv sends + `kibV3` sends (`D1/Link/Keynib`). -/
theorem keynib_bal_d1 {pub : List Fp} {tr : Trace Fp} {r : ZkFormal.NearV3.Assembly.V3Records}
    (hH : HoldsP ZkFormal.NearV3.D1.nearAirV3D1 pub tr)
    (T : ZkFormal.NearV3.D1.Link.BaseTrafficD1 pub tr r) (m : List Fp) :
    ((walkRecvs3 r.walks B_KEYNIB).map Msg.toFp).count m =
      ((rcptSends3 pub r.lists B_KEYNIB).map Msg.toFp).count m + (qvKeys tr pub).count m +
        (ZkFormal.NearV3.D1.Link.kibKeys tr pub).count m := by
  have h := bal_users_d1 hH (b := B_KEYNIB) (U := [T_WALK, T_RCPT, T_QV, 27]) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [walk_count_d1 T, walk_count_d1 T,
    show ZkFormal.NearV3.D1.Link.isAtD1 T_RCPT = ZkFormal.NearV3.D1.RcptD1.tableQD1.interactions from rfl,
    show T_RCPT = 16 from rfl, tcnt_of_traffic T.lists, tcnt_of_traffic T.lists,
    tableBusCount_noside (s := false) (is := ZkFormal.NearV3.D1.Link.isAtD1 T_QV) (by decide +kernel),
    tableBusCount_eq (ZkFormal.NearV3.D1.Link.isAtD1 T_QV),
    tableBusCount_noside (s := false) (is := ZkFormal.NearV3.D1.Link.isAtD1 27) (by decide +kernel),
    tableBusCount_eq (ZkFormal.NearV3.D1.Link.isAtD1 27)] at h
  have w0 : walkSends3 r.walks B_KEYNIB = [] := by
    simp [walkSends3, B_KEYNIB, B_EDGE, B_BMAP, B_FINAL]
  have r0 : rcptRecvs3 r.lists B_KEYNIB = [] := by
    simp [rcptRecvs3, rRecvs, B_DIGEST, B_FINAL, B_MEM, B_KEYNIB, B_SREC, B_AKC, B_BND]
  simp only [tcnt, ite_true, Bool.false_eq_true, ite_false, walkTraffic3,
    ZkFormal.NearV3.D1.RcptD1.rcptTraffic3D1, ZkFormal.NearV3.D1.RcptD1.rcptTraffic3G,
    ZkFormal.NearV3.D1.Link.rcptSends3G_keynib, w0, r0,
    List.map_nil, List.count_nil, Nat.zero_add, Nat.add_zero] at h
  unfold qvKeys ZkFormal.NearV3.D1.Link.kibKeys
  rw [show isAt T_QV = ZkFormal.NearV3.D1.Link.isAtD1 T_QV from rfl,
    show ZkFormal.NearV3.D1.T_KIB = 27 from rfl]
  omega

-- @patch ZkFormal.NearV3.Assembly.LinkKeynib.qvKeys_syms
<<<
  rw [qvKeys, show ZkFormal.NearV3.D1.Link.isAtD1 T_QV = Qv.Candidates.KeyTrafficRepair.interactions from rfl,
===
  rw [qvKeys, show isAt T_QV = Qv.Candidates.KeyTrafficRepair.interactions from rfl,
>>>

-- @override ZkFormal.NearV3.Assembly.LinkKeynib.keynibOk_of
/-- **`KeynibOk`** of the walks (D1: providers = rcpt + qv + `kibV3` `KEYNIB` sends). -/
theorem keynibOk_of_d1 {cb : NearSpec.Bytes} {h : ZkFormal.NearV3.D1.HintD1} {p : NearSpecV3.Prep} {q : ZkFormal.NearV3.D1.Public.PrepD1} {oh : Nat}
    {tr : Trace Fp} {r : ZkFormal.NearV3.Assembly.V3Records} (hp : (ZkFormal.NearV3.D1.prepD1 cb h = .ok q ∧ q.base = p))
    (hsz : (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh).length < P)
    (hH : HoldsP ZkFormal.NearV3.D1.nearAirV3D1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) tr)
    (T : ZkFormal.NearV3.D1.Link.BaseTrafficD1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) tr r)
    (W : ZkFormal.NearV3.D1.Link.BaseWfD1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) r) :
    Link3.KeynibOk r.walks
      (rcptSends3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) r.lists B_KEYNIB ++
        (qvKeys tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh))).map
          (fun x => x.map Fp.toNat) ++
        (ZkFormal.NearV3.D1.Link.kibKeys tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh))).map
          fun x => x.map Fp.toNat) := by
  have henc := LinkRidBytes.encBytes_d1 hp hsz hH T W
  obtain ⟨toks, -, -, hwf, -⟩ := W.lists.toks
  refine ⟨?_, ?_⟩
  · intro m hm
    have hc : 0 < ((walkRecvs3 r.walks B_KEYNIB).map Msg.toFp).count (Msg.toFp m) :=
      List.count_pos_iff.mpr (List.mem_map_of_mem hm)
    rw [keynib_bal_d1 hH T] at hc
    rw [List.map_append, List.map_append, List.map_map, List.map_map,
      show (Msg.toFp ∘ fun x : List Fp => x.map Fp.toNat) = id from funext toFp_map_toNat]
    simp only [List.map_id, List.mem_append]
    rcases Nat.eq_zero_or_pos (((rcptSends3 _ r.lists B_KEYNIB).map Msg.toFp).count (Msg.toFp m)) with h0 | h0
    · rcases Nat.eq_zero_or_pos ((qvKeys tr _).count (Msg.toFp m)) with h1 | h1
      · right; rw [h0, h1] at hc; exact List.count_pos_iff.mp (by omega)
      · left; right; exact List.count_pos_iff.mp h1
    · left; left; exact List.count_pos_iff.mp h0
  · have sym_ok : ∀ y, y < 16 ∨ y = SYM_END → y < P ∧ (y < 16 ∨ y = SYM_END) := by
      intro y hy; refine ⟨?_, hy⟩; rcases hy with hy | hy
      · unfold P; omega
      · rw [hy]; decide
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    rotate_left
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
      obtain ⟨k, -, t, sym, last, rfl, hs⟩ := ZkFormal.NearV3.D1.Link.kibKeys_entry hp.1 hsz hH y hy
      apply sym_ok
      have hsP : sym < P := by
        rcases hs with hs | hs
        · unfold P; omega
        · rw [hs]; decide
      simp only [Msg.toFp, List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero,
        Fp.toNat_ofNat, Nat.mod_eq_of_lt hsP]
      exact hs
    rcases List.mem_append.mp hm with hm | hm
    · apply sym_ok
      rw [rcptSends3_keynib] at hm
      obtain ⟨⟨x, q⟩, hxq, hm⟩ := List.mem_flatMap.mp hm
      have hx : x ∈ flatR r.lists := (List.of_mem_zip (LinkRids.zipIdx_zero (flatR r.lists) ▸ hxq)).1
      obtain ⟨qq, hqq, hxe⟩ := List.getElem_of_mem hx
      have hW := hwf qq hqq
      rw [hxe] at hW
      rcases List.mem_append.mp hm with hm | hm
      · have hs := keyMsgs_sym hm
        simp only [RcptV.keySyms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with (hs | hs) | hs
        · left; rcases hs with hs | hs <;> rw [hs] <;> decide
        · left; exact nibbles_ok _ hW.ids.2.2.2.2.1 _ hs
        · right; exact hs
      · split at hm
        · have hs := keyMsgs_sym hm
          simp only [RcptE.akSyms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with hs | hs
          · left
            apply nibbles_ok _ _ _ hs
            intro c hc
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with ((((hc | hc) | hc) | hc) | hc)
            · omega
            · exact hW.ids.2.2.2.2.2 c hc
            · omega
            · have := hW.lens.2.2.1; omega
            · exact henc x hx c (by simp [RcptV.enc, hc])
          · right; exact hs
        · simp at hm
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
      have hq := qvKeys_syms_d1 hH y hy
      have z0 : (0 : Nat) = Fp.toNat 0 := by
        have := Fp.toNat_ofNat 0
        rw [Nat.zero_mod] at this
        exact this.symm
      have e : (y.map Fp.toNat).getD 2 0 = (y.getD 2 0).toNat := by
        match y with
        | [] => exact z0
        | [_] => exact z0
        | [_, _] => exact z0
        | _ :: _ :: c :: _ => rfl
      rw [e]
      exact sym_ok _ hq

-- @override ZkFormal.NearV3.RcptLink.othersRC_kind
/-- No other `BYTES` sender uses an id of the receipt-stream kinds `K_PEO` or `K_RID` (D1: the public
body prefix uses `K_RF`, so the D0a `K_RF` case is false in D1 and dropped). -/
theorem othersRC_kind_d1 {K : Nat} (hK : K = K_PEO ∨ K = K_RID) {cb : NearSpec.Bytes} {h : ZkFormal.NearV3.D1.HintD1} {p : NearSpecV3.Prep} {q : ZkFormal.NearV3.D1.Public.PrepD1} {oh : Nat}
    {tr : Trace Fp} {r : ZkFormal.NearV3.Assembly.V3Records} (hp : (ZkFormal.NearV3.D1.prepD1 cb h = .ok q ∧ q.base = p))
    (hsz : (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh).length < P)
    (hH : HoldsP ZkFormal.NearV3.D1.nearAirV3D1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) tr)
    (T : ZkFormal.NearV3.D1.Link.BaseTrafficD1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) tr r)
    (W : ZkFormal.NearV3.D1.Link.BaseWfD1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) r) :
    ∀ m ∈ LinkRidBytes.othersRC_d1 tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) r, ∀ a,
      m.head? = some a → a < P ∧ a % 16 ≠ K := by
  have kin : ∀ {K' : Nat} {x : Msg}, KindIn [K'] x → K' ≠ K → ∀ a, x.head? = some a →
      a < P ∧ a % 16 ≠ K := by
    intro K' x hk hK' a ha
    obtain ⟨h1, h2⟩ := hk a ha
    rw [List.mem_singleton] at h2
    exact ⟨h1, h2 ▸ hK'⟩
  have nv : ∀ {K' n : Nat}, (K' = K_NPRE ∨ K' = K_NPOST ∨ K' = K_VPRE) → n < 2 ^ 22 →
      msgId K' n < P ∧ msgId K' n % 16 ≠ K := by
    intro K' n hK' hn
    unfold msgId P
    rcases hK with rfl | rfl <;>
    rcases hK' with rfl | rfl | rfl <;> simp only [K_NPRE, K_NPOST, K_VPRE, K_PEO, K_RF, K_RID] <;> omega
  intro m hm a ha
  simp only [LinkRidBytes.othersRC_d1, List.mem_append] at hm
  rcases hm with ((((((hm | hm) | hm) | hm) | hm) | hm) | hm) | hm
  · obtain ⟨K, n, hh, hK, hn⟩ := nodeVal_bytes_head W.nodes W.values (List.mem_append_left _ hm)
    rw [ha, Option.some.injEq] at hh; subst hh
    exact nv hK hn
  · obtain ⟨K, n, hh, hK, hn⟩ := nodeVal_bytes_head W.nodes W.values (List.mem_append_right _ hm)
    rw [ha, Option.some.injEq] at hh; subst hh
    exact nv hK hn
  · exact kin (upsKindIn_of_d1 hp hsz hH T W m hm) (by rcases hK with rfl | rfl <;> decide) a ha
  · exact kin (acctKindIn_d1 hH T W m hm) (by rcases hK with rfl | rfl <;> decide) a ha
  · exact kin (ddKindIn W.srcp m hm) (by rcases hK with rfl | rfl <;> decide) a ha
  · exact kin (mrkKindIn_d1 W (pubNat_pubOf_lt _) (ZkFormal.NearV3.D1.Link.m0V_le hp.1) m hm) (by rcases hK with rfl | rfl <;> decide) a ha
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
    cases hyh : y.head? with
    | none => simp [List.head?_map, hyh] at ha
    | some e =>
      simp only [List.head?_map, hyh, Option.map_some, Option.some.injEq] at ha
      subst ha
      have := codecKindIn_d1 hp hsz hH y hy e hyh
      exact ⟨Fp.toNat_lt e, by rw [this]; rcases hK with rfl | rfl <;> decide⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
    cases hyh : y.head? with
    | none => simp [List.head?_map, hyh] at ha
    | some e =>
      simp only [List.head?_map, hyh, Option.map_some, Option.some.injEq] at ha
      subst ha
      exact ⟨Fp.toNat_lt e, ZkFormal.NearV3.D1.Link.extraKinds_peo_rid hp.1 hsz hH T W hK y hy e hyh⟩

-- @override ZkFormal.NearV3.RcptLink.peoBytes
/-- **`PEO` preimages are bytes.** -/
theorem peoBytes_d1 {cb : NearSpec.Bytes} {h : ZkFormal.NearV3.D1.HintD1} {p : NearSpecV3.Prep} {q : ZkFormal.NearV3.D1.Public.PrepD1} {oh : Nat}
    {tr : Trace Fp} {r : ZkFormal.NearV3.Assembly.V3Records} (hp : (ZkFormal.NearV3.D1.prepD1 cb h = .ok q ∧ q.base = p))
    (hsz : (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh).length < P)
    (hH : HoldsP ZkFormal.NearV3.D1.nearAirV3D1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) tr)
    (T : ZkFormal.NearV3.D1.Link.BaseTrafficD1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) tr r)
    (W : ZkFormal.NearV3.D1.Link.BaseWfD1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) r) :
    ∀ x ∈ flatR r.lists, Bytes8 x.peo := by
  intro x hx
  obtain ⟨L, hL, hxL⟩ := List.mem_flatMap.mp hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hL
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hxL
  have hloc : (baseR r.lists j + k, lOffs r.lists[j].rs k, r.lists[j].rs[k]) ∈ located r.lists j := by
    simp only [located, getD_eq_getElem' r.lists default hj, List.mem_map, List.mem_range]
    exact ⟨k, hk, by rw [getD_eq_getElem' _ default hk]⟩
  obtain ⟨hq, hxq⟩ := located_flat hj hloc
  generalize hxe : r.lists[j].rs[k] = x at hloc hxq
  generalize hqe : baseR r.lists j + k = qi at hloc hq hxq
  have hcnt := W.listsCount
  -- the digest receive
  have hdig : 0 < shaU tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) true B_DIGEST
      (digMsg (msgId K_PEO qi) x.peo.length x.peoh).toFp := by
    have hq22 : qi < 2 ^ 22 := by have := hcnt.2; omega
    apply digest_provided_d1 hH (ZkFormal.NearV3.D1.Link.plfSmall_of hp.1 hsz hH) (t := Assembly.T_RCPT) (by decide)
      (ZkFormal.NearV3.D1.Link.digMsg_ne_plf (by decide) (by decide) hq22)
    rw [show ZkFormal.NearV3.D1.Link.isAtD1 Assembly.T_RCPT = ZkFormal.NearV3.D1.RcptD1.tableQD1.interactions from rfl,
      show Assembly.T_RCPT = 16 from rfl, tcnt_of_traffic T.lists]
    simp only [tcnt, Bool.false_eq_true, ite_false, ZkFormal.NearV3.D1.RcptD1.rcptTraffic3D1,
      ZkFormal.NearV3.D1.RcptD1.rcptTraffic3G]
    apply List.count_pos_iff.mpr
    apply List.mem_map_of_mem
    simp only [rcptRecvs3, List.mem_flatMap, List.mem_range]
    refine ⟨j, hj, _, hloc, ?_⟩
    simp [rRecvs]
  have hsha := LinkRidBytes.shaFacts_cover (shaU_facts_d1 hH) _ (LinkRidBytes.sha_le_rc_d1 hH T)
  obtain ⟨toks, -, -, hwf, -⟩ := W.lists.toks
  have hw := hwf qi hq
  rw [hxq] at hw
  have hxm : x ∈ flatR r.lists := hxq ▸ List.getElem_mem hq
  have hid : msgId K_PEO qi < P := by unfold msgId K_PEO P; omega
  have hcan : ∀ y ∈ x.raw3, y < P := W.lists.canon.2 x hxm
  have hpeoc : ∀ y ∈ x.peo, y < P := by
    intro y hy
    rcases receipt_peo_values hw y hy with hy | hy
    · exact hcan y (by simp [RcptE.raw3, hy])
    · unfold P; omega
  have hplen : x.peo.length < P := by
    have := (Rcpt.Candidates.receipt_sha_lengths
      (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) _ hw).2.1
    unfold P; omega
  refine (sha_core hsha _ (fun m => rfl) hid hpeoc hplen
    (fun y hy => hcan y (by simp [RcptE.raw3, RcptV.raw, hy])) ?_ hdig).1
  intro m hm a ha he
  rcases List.mem_append.mp hm with hm | hm
  · rcases ZkFormal.NearV3.D1.Link.rcptG_bytes_mem hm with hm | hm0
    rotate_left
    · rw [hm0, Option.some.injEq] at ha
      subst ha
      have heq := Near.Link.ofNat_inj (by unfold K_RF P; omega) hid he
      unfold msgId K_PEO K_RF at heq; omega
    have hc := receipt_bytes_ids hcnt.1 hcnt.2 hm ha
    have heq := Near.Link.ofNat_inj hc hid he
    subst a
    obtain ⟨hq', k', hk', rfl⟩ := peo_isolate hm ha
    simp only [hxq] at hk' ⊢
    exact ⟨k', hk', rfl⟩
  · have hh := othersRC_kind_d1 (Or.inl rfl) hp hsz hH T W m hm a ha
    have heq := Near.Link.ofNat_inj hh.1 hid he
    have hk : msgId K_PEO qi % 16 = K_PEO := by simp [msgId, K_PEO, Nat.add_mod]
    exact False.elim (hh.2 (heq ▸ hk))

-- @override ZkFormal.NearV3.Assembly.LinkUps.noUpsBytes
/-- The `BYTES` sends of the viewed tables other than node / val / ups, plus the codec (D1:
`rcptV3D1`'s sends and the extra senders `akmV3` / public body prefix). -/
def noUpsBytes_d1 (tr : Trace Fp) (pub : List Fp) (r : ZkFormal.NearV3.Assembly.V3Records) : List (List Fp) :=
  ((ZkFormal.NearV3.D1.RcptD1.rcptTraffic3D1 pub r.lists).sends B_BYTES ++ acctV3Sends r.accts B_BYTES ++
    (ddTraffic r.srcp r.srcpRep).sends B_BYTES ++
    (mrkTrafficE pub r.mrkE r.mrk).sends B_BYTES).map Msg.toFp ++ codecBytes tr pub ++
    ZkFormal.NearV3.D1.Link.extraBytes tr pub

-- @override ZkFormal.NearV3.Assembly.LinkUps.noUps_kinds
/-- Kinds of `noUpsBytes`: rcpt 1–5, acct 10, srcp 13, mrk 6, codec 11, akm 10, body prefix 2 —
never `K_VUPS`. -/
theorem noUps_kinds_d1 {cb : NearSpec.Bytes} {h : ZkFormal.NearV3.D1.HintD1} {p : NearSpecV3.Prep} {q : ZkFormal.NearV3.D1.Public.PrepD1} {oh : Nat}
    {tr : Trace Fp} {r : ZkFormal.NearV3.Assembly.V3Records} (hp : (ZkFormal.NearV3.D1.prepD1 cb h = .ok q ∧ q.base = p))
    (hsz : (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh).length < P)
    (hH : HoldsP ZkFormal.NearV3.D1.nearAirV3D1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) tr)
    (T : ZkFormal.NearV3.D1.Link.BaseTrafficD1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) tr r)
    (W : ZkFormal.NearV3.D1.Link.BaseWfD1 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) r) :
    ∀ y ∈ noUpsBytes_d1 tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 q oh)) r, ∀ a,
      y.head? = some a → a.toNat % 16 ≠ K_VUPS := by
  have kin : ∀ {ks : List Nat} {x : Msg}, KindIn ks x → (∀ k ∈ ks, k ≠ K_VUPS) →
      ∀ a, x.toFp.head? = some a → a.toNat % 16 ≠ K_VUPS := by
    intro ks x hk hks a ha
    cases x with
    | nil => simp [Msg.toFp] at ha
    | cons b xs =>
      simp only [Msg.toFp, List.map_cons, List.head?_cons, Option.some.injEq] at ha
      subst ha
      obtain ⟨h1, h2⟩ := hk b rfl
      rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt h1]
      exact hks _ h2
  intro y hy a ha
  simp only [noUpsBytes_d1, List.mem_append, List.map_append] at hy
  rcases hy with ((((hy | hy) | hy) | hy) | hy) | hy
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact kin (ZkFormal.NearV3.D1.Link.rcptKindInG W.listsCount.1 W.listsCount.2 x hx) (by decide) a ha
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact kin (acctKindIn_d1 hH T W x hx) (by decide) a ha
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact kin (ddKindIn W.srcp x hx) (by decide) a ha
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact kin (mrkKindIn_d1 W (pubNat_pubOf_lt _) (ZkFormal.NearV3.D1.Link.m0V_le hp.1) x hx) (by decide) a ha
  · rw [codecKindIn_d1 hp hsz hH y hy a ha]; decide
  · rcases ZkFormal.NearV3.D1.Link.extraHeads hp.1 hsz hH T W y hy a ha with h1 | h1 <;> rw [h1] <;> decide
