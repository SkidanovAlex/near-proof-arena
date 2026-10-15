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
