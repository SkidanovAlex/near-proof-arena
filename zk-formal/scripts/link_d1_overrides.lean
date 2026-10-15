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
