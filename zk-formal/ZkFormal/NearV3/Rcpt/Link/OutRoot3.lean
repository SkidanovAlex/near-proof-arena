import ZkFormal.NearV3.Rcpt.Link.OutLeaf3
import ZkFormal.NearV3.Rcpt.Link.OutCore3
import ZkFormal.NearV3.Candidates.MerkleRender.Public
import ZkFormal.Near.Render.Proof.DigMrk

/-!
# ZkFormal.NearV3.Rcpt.Link.OutRoot3 — the claim's outcome root is the model's (`RunHdr.outcomeRoot`)

* `mrk_iso` — the `MRK(i)` messages of the `BYTES` senders are the `i`-th hashed node's;
* `rcpt_mpos_*`, `mpos_bal` — the `MPOS` traffic of the receipt view and the exact `MPOS` balance
  (users rcpt 16, mrk 23);
* `outCore_holds` — `OutCore` for the nonempty mrk view (`mrkE = false`);
* `outRoot_empty` — the empty mrk view forces `n = 0` and a zero public root;
* **`outcomeRoot_holds`** — `k.H.prevOutcomeRoot = outcomeRoot (mainOut).outcomes`;
* **`runHdr_holds`** — `LinkHdr.RunHdr k h out` for every main-run output `out`.
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Near.Link
  ZkFormal.NearV3.Assembly NearSpec NearSpec.TransferV1 NearSpecV3

/-! ## `MPOS` traffic -/

theorem rcpt_mpos_recvs (ls : RcptV3Vs) : rcptRecvs3 ls B_MPOS = [] := by
  simp [rcptRecvs3, rRecvs, B_MPOS, B_DIGEST, B_FINAL, B_MEM, B_SREC, B_AKC, B_BND]

theorem rcpt_mpos_mem {pub : List Fp} {ls : RcptV3Vs} {m : Msg} (hm : m ∈ rcptSends3 pub ls B_MPOS) :
    ∃ q, q < (flatR ls).length ∧ m = [0, q, msgId K_LEAF q, 68] := by
  simp only [rcptSends3, show B_MPOS ≠ B_BYTES by decide, show B_MPOS ≠ B_RCL by decide, ite_false,
    List.nil_append, List.mem_flatMap, List.mem_range] at hm
  obtain ⟨j, hj, ⟨r, o, x⟩, hpos, hm⟩ := hm
  obtain ⟨hq, -⟩ := located_flat hj hpos
  simp [rSends, B_MPOS, B_BYTES, B_KEYNIB, B_MEM, B_RIDS] at hm
  exact ⟨r, hq, hm⟩

theorem mpos_bal {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (m : List Fp) :
    ZkFormal.Near.cnt (rcptSends3 pub r.lists B_MPOS) m +
        ZkFormal.Near.cnt ((mrkTrafficE pub r.mrkE r.mrk).sends B_MPOS) m =
      ZkFormal.Near.cnt ((mrkTrafficE pub r.mrkE r.mrk).recvs B_MPOS) m := by
  have h := bal_users hH (b := B_MPOS) (U := [Assembly.T_RCPT, Assembly.T_MRK]) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [show isAt Assembly.T_RCPT = RcptV3.interactions from rfl, tcnt_of_traffic T.lists,
    tcnt_of_traffic T.lists,
    show isAt Assembly.T_MRK = ZkFormal.NearV3.Candidates.MerkleEmpty.table.interactions from rfl,
    tcnt_of_traffic T.mrk, tcnt_of_traffic T.mrk] at h
  simp only [tcnt, ite_true, Bool.false_eq_true, ite_false, rcptTraffic3, rcpt_mpos_recvs,
    List.map_nil, List.count_nil, Nat.zero_add] at h
  unfold ZkFormal.Near.cnt
  omega

/-! ## `MRK` isolation -/

theorem othersRC_mrk {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ∀ m ∈ LinkRidBytes.othersRC tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r, ∀ a,
      m.head? = some a → a < ZkFormal.Algebra.P ∧ (a % 16 ≠ K_MRK ∨
        m ∈ (mrkTrafficE (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r.mrkE r.mrk).sends B_BYTES) := by
  have kin : ∀ {K' : Nat} {x : Msg}, KindIn [K'] x → K' ≠ K_MRK → ∀ a, x.head? = some a →
      a < ZkFormal.Algebra.P ∧ a % 16 ≠ K_MRK := by
    intro K' x hk hK' a ha
    obtain ⟨h1, h2⟩ := hk a ha
    rw [List.mem_singleton] at h2
    exact ⟨h1, h2 ▸ hK'⟩
  have nv : ∀ {K' n : Nat}, (K' = K_NPRE ∨ K' = K_NPOST ∨ K' = K_VPRE) → n < 2 ^ 22 →
      msgId K' n < ZkFormal.Algebra.P ∧ msgId K' n % 16 ≠ K_MRK := by
    intro K' n hK' hn
    unfold msgId ZkFormal.Algebra.P
    rcases hK' with rfl | rfl | rfl <;> simp only [K_NPRE, K_NPOST, K_VPRE, K_MRK] <;> omega
  intro m hm a ha
  simp only [LinkRidBytes.othersRC, List.mem_append] at hm
  rcases hm with (((((hm | hm) | hm) | hm) | hm) | hm) | hm
  · obtain ⟨K, n, hh, hK, hn⟩ := nodeVal_bytes_head W.nodes W.values (List.mem_append_left _ hm)
    rw [ha, Option.some.injEq] at hh; subst hh
    exact ⟨(nv hK hn).1, .inl (nv hK hn).2⟩
  · obtain ⟨K, n, hh, hK, hn⟩ := nodeVal_bytes_head W.nodes W.values (List.mem_append_right _ hm)
    rw [ha, Option.some.injEq] at hh; subst hh
    exact ⟨(nv hK hn).1, .inl (nv hK hn).2⟩
  · have := kin (upsKindIn_of hp hsz hH T W m hm) (by decide) a ha; exact ⟨this.1, .inl this.2⟩
  · have := kin (acctKindIn hH T W m hm) (by decide) a ha; exact ⟨this.1, .inl this.2⟩
  · have := kin (ddKindIn W.srcp m hm) (by decide) a ha; exact ⟨this.1, .inl this.2⟩
  · exact ⟨(mrkKindIn W (pubNat_pubOf_lt _) m hm a ha).1, .inr hm⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
    cases hyh : y.head? with
    | none => simp [List.head?_map, hyh] at ha
    | some e =>
      simp only [List.head?_map, hyh, Option.map_some, Option.some.injEq] at ha
      subst ha
      have := codecKindIn hp hsz hH y hy e hyh
      exact ⟨Fp.toNat_lt e, .inl (by rw [this]; decide)⟩

/-- **`MRK(i)` isolation** (nonempty mrk view). -/
theorem mrk_iso {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (he : r.mrkE = false) (hml : r.mrk.nodes.length ≤ 2 ^ 23) (i : Nat) (enc : List Nat)
    (hi : (mrkMsgs r.mrk)[i]? = some enc) :
    Iso (rcptSends3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r.lists B_BYTES ++
      LinkRidBytes.othersRC tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
      (msgId K_MRK i) enc := by
  have hil : i < (mrkMsgs r.mrk).length := by
    rcases Nat.lt_or_ge i (mrkMsgs r.mrk).length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hi; cases hi
  have hml' : (mrkMsgs r.mrk).length ≤ r.mrk.nodes.length := by
    rw [mrkMsgs_eq]; exact List.length_filterMap_le _ _
  have hid : msgId K_MRK i < ZkFormal.Algebra.P := by unfold msgId K_MRK ZkFormal.Algebra.P; omega
  have hk : msgId K_MRK i % 16 = K_MRK := by simp [msgId, K_MRK, Nat.add_mod]
  intro m hm a ha hae
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨h1, h2⟩ := rcptKindIn W.listsCount.1 W.listsCount.2 m hm a ha
    have heq := Near.Link.ofNat_inj h1 hid hae
    subst heq
    rw [hk] at h2
    simp [K_MRK, K_RC, K_RF, K_PEO, K_LEAF, K_RID] at h2
  · obtain ⟨h1, h2⟩ := othersRC_mrk hp hsz hH T W m hm a ha
    have heq := Near.Link.ofNat_inj h1 hid hae
    subst heq
    rcases h2 with h2 | hx
    · exact absurd hk h2
    simp only [mrkTrafficE, he, Bool.false_eq_true, ite_false, mrkTraffic, mrkSends, ite_true,
      List.mem_flatMap] at hx
    obtain ⟨⟨nd, q⟩, hq, hx⟩ := hx
    obtain ⟨hql, hnd⟩ := mem_zip_range.mp hq
    cases nd with
    | promoted => simp at hx
    | hashed lI lL l rI rL rr =>
      dsimp only at hx
      have hb := hashedBefore_le r.mrk.nodes q
      have hh := emitAt_head_eq hx ha
      have hbi : hashedBefore r.mrk.nodes q = i := by unfold msgId at hh; omega
      have hmsg := mrkMsgs_at r.mrk q hql hnd
      rw [hbi, hi, Option.some.injEq] at hmsg
      obtain ⟨k, hk', rfl⟩ := ZkFormal.NearV3.Link3.mem_emitAt3.mp hx
      subst hmsg
      exact ⟨k, hk', by rw [hbi]; simp⟩

/-! ## The nonempty mrk view: `OutCore` -/

theorem mrk_n_eq {pub : List Fp} {r : V3Records} (W : V3RecordsWf pub r)
    (hpb : ∀ i, pubNat pub i < 256) (he : r.mrkE = false) : r.mrk.n = (flatR r.lists).length := by
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
  rw [hw.nfix hb (by rw [hn]; unfold ZkFormal.Algebra.P; omega), hn]

/-- The model's outcome leaves. -/
def leavesM (M : RunModel) (ctx : ApplyCtx) (n : Nat) : List Bytes :=
  (List.range n).map fun q => (M.outcomeOf ctx q).leaf

theorem outCore_holds {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (H : RecHyp (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r.lists r.accts)
    {pc : PrepC} (hc : prepClaim cb = .ok pc) (hb : prepBody pc h = .ok p)
    (hgp : pc.ctxB2.gasPrice =
      leN' (pubBytes (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) PH_GP 16))
    (base : Nat → NearSpec.Bytes) (Tf : (Nat → NearSpec.Bytes) → PTrie) (he : r.mrkE = false) :
    OutCore (rcptSends3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r.lists B_BYTES ++
        LinkRidBytes.othersRC tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
      (shaU tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) true)
      (fun b m => if b = B_BYTES then ZkFormal.Near.cnt
          (rcptSends3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r.lists B_BYTES ++
            LinkRidBytes.othersRC tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) m
        else shaU tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) false b m)
      (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic
        (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh))) r.mrk
      (rcptSends3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r.lists B_MPOS)
      (flatR r.lists).length (leavesM (recModel r.lists r.accts base Tf) pc.ctxB2 (flatR r.lists).length) := by
  have hw : MrkWf (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic
      (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh))) r.mrk := by
    have := W.mrk; simpa [MrkWfE, he] using this
  have hnv := mrk_n_eq W (pubNat_pubOf_lt _) he
  have hnle := W.listsCount.2
  have hml : r.mrk.nodes.length ≤ 2 ^ 23 := by
    rw [hw.shape.1]
    have := mrkLevels_length2 (r.mrk.n + 1) 1 r.mrk.n
    unfold mrkShape; omega
  refine
    { hsha := LinkRidBytes.shaFacts_cover (shaU_facts hH) _ (LinkRidBytes.sha_le_rc hH T)
      hbytes := fun m => rfl
      dig := ?_
      bal := fun m => by
        have := mpos_bal hH T m
        simpa [mrkTrafficE, he, mrkTraffic] using this
      rs := fun m hm => rcpt_mpos_mem hm
      wf := hw
      nv := hnv
      nle := hnle
      leaf := ?_
      mrk := mrk_iso hp hsz hH T W he hml
      len := by simp [leavesM] }
  · intro m hm
    apply digest_provided hH (t := Assembly.T_MRK) (by decide)
    rw [show isAt Assembly.T_MRK = ZkFormal.NearV3.Candidates.MerkleEmpty.table.interactions from rfl,
      tcnt_of_traffic T.mrk]
    simp only [tcnt, Bool.false_eq_true, ite_false, mrkTrafficE, he, mrkTraffic]
    exact List.count_pos_iff.mpr (List.mem_map_of_mem hm)
  · intro q hq
    obtain ⟨hB, hS⟩ := leaf_hash3 hp hsz hH T W H hc hb hgp base Tf hq
    obtain ⟨toks, -, -, hwf, -⟩ := W.lists.toks
    have w := hwf q hq
    obtain ⟨l1, -, -, -, -, -, -, -, -, -, -, -, l13, -⟩ := w.lens
    refine ⟨(flatR r.lists)[q].leaf, ?_, fun y hy => by have := hB y hy; unfold ZkFormal.Algebra.P; omega,
      leaf_iso hp hsz hH T W hq, ?_⟩
    · simp [RcptV.leaf, l1, l13]
    · rw [hS]
      simp [leavesM, List.getD_eq_getElem?_getD, List.getElem?_range hq]

/-! ## The outcome root -/

/-- **`RunHdr.outcomeRoot`**: the claim's outcome root is the model's. -/
theorem outcomeRoot_holds {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {k : NearSpecV3.WalkD0} (hw : NearSpecV3.walkD0 cb = .ok k)
    {block previous : NearSpecV3.Blk} (hmb : k.blks[k.b2i]? = some block)
    (hmp : k.blks[k.b2i + 1]? = some previous)
    (pc : PrepC) (hc : prepClaim cb = .ok pc) (base : Nat → NearSpec.Bytes) (Tf : (Nat → NearSpec.Bytes) → PTrie) :
    k.H.prevOutcomeRoot = outcomeRoot ((recModel r.lists r.accts base Tf).mainOut pc.ctxB2).outcomes := by
  obtain ⟨pc', hc', hb, hgp⟩ := gasPrice_pub oh hp
  rw [hc] at hc'; cases hc'
  have H := recHyp_of hp hsz hH T W (shaHyp_holds hp hsz hH T W)
  have hroots := ZkFormal.NearV3.Assembly.prepD0_roots hp
  have C0 := LinkPrepCtx.prepClaim_context_of
    (m := ⟨block, previous, [], LinkImplicit.Fpre r 0, (recModel r.lists r.accts base Tf).mainOut pc.ctxB2⟩)
    (stateWitnessOfV3 k ⟨[], [], [], [], []⟩) hc hw hmb hmp
  have hO : k.H.prevOutcomeRoot = p.hdr.outcomeRoot := by
    rw [RcptSkeleton.prepBody_outcomeRoot hb, RcptSkeleton.prepClaim_outcomeRoot hc, C0.header]
  have hpubO : ∀ j, j < 32 →
      pubNat (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) (PH_OUT + j) =
        (p.hdr.outcomeRoot.getD j 0).toNat := by
    intro j hj
    rw [pubNat_prepared, RcptSkeleton.prepared_outcome_byte p oh j hroots hj]
  have hlen32 : p.hdr.outcomeRoot.length = 32 := hroots.2.2
  have hout : ((recModel r.lists r.accts base Tf).mainOut pc.ctxB2).outcomes.map Outcome.leaf =
      leavesM (recModel r.lists r.accts base Tf) pc.ctxB2 (flatR r.lists).length := by
    simp only [RunModel.mainOut, RunModel.accAt, recModel_length, leavesM, List.map_map]; rfl
  rw [hO, outcomeRoot, hout]
  cases he : r.mrkE
  · have R := root_of_core (outCore_holds hp hsz hH T W H hc hb hgp base Tf he)
    have e : ((List.range 32).map fun j => pubNat (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic
        (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh))) (PV_OUT + j)) =
        p.hdr.outcomeRoot.map UInt8.toNat := by
      apply List.ext_getElem (by simp [hlen32])
      intro j h1 h2
      have hj : j < 32 := by simpa using h1
      simp only [List.getElem_map, List.getElem_range]
      rw [alias_pubNat _ (by unfold PV_OUT; omega),
        show ZkFormal.NearV3.Candidates.MerklePublic.publicIndex (PV_OUT + j) = PH_OUT + j from
          ZkFormal.NearV3.Candidates.MerklePublic.root_index ⟨j, hj⟩,
        hpubO j hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl
    rw [e, toBytes_map_toNat'] at R
    exact R
  · have hE := W.mrk
    simp only [MrkWfE, he, ite_true] at hE
    obtain ⟨hcount, hzero⟩ := hE
    -- no receipts
    have hn0 : (flatR r.lists).length = 0 := by
      have hpb := pubNat_pubOf_lt (ZkFormal.NearV3.Public.preparedBytes p oh)
      have hc4 := W.lists.count (fun i _ => hpb _)
      have hb : ∀ x, x < 4 → pubNat (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic
          (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh))) (PV_N + x) < 256 :=
        fun x hx => by rw [alias_n _ x hx]; exact hpb _
      have hpe : pubBytes (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic
          (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh))) PV_N 4 =
          pubBytes (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) ZkFormal.NearV3.PH_N 4 := by
        unfold pubBytes
        apply List.map_congr_left
        intro j hj
        exact alias_n _ j (List.mem_range.mp hj)
      have hn := ZkFormal.Near.Link.nPubNat_eq _ hb
      rw [hpe, ← hc4] at hn
      have b0 := hb 0 (by decide); have b1 := hb 1 (by decide)
      have b2 := hb 2 (by decide); have b3 := hb 3 (by decide)
      simp only [nPubNat, List.range, List.range.loop, List.foldr, alias_n _ _ (show 0 < 4 by decide),
        alias_n _ _ (show 1 < 4 by decide), alias_n _ _ (show 2 < 4 by decide),
        alias_n _ _ (show 3 < 4 by decide)] at hn
      rw [alias_n _ _ (by decide)] at b0; rw [alias_n _ _ (by decide)] at b1
      rw [alias_n _ _ (by decide)] at b2; rw [alias_n _ _ (by decide)] at b3
      have hlt := W.listsCount.2
      have hcE := ZkFormal.NearV3.Candidates.MerkleRender.public_count tr Assembly.T_MRK 0
        (flatR r.lists).length (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh))
        (by omega) (by
          intro i hi
          rw [← Fp.ofNat_toNat ((ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)).getD
            (ZkFormal.NearV3.PH_N + i) 0)]
          congr 1
          change pubNat _ _ = _
          rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
            simp only [Nat.add_zero] at * <;> omega)
      rw [hcount] at hcE
      have := congrArg Fp.toNat hcE
      rw [Fp.toNat_zero, Fp.toNat_ofNat, Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P; omega)] at this
      exact this.symm
    -- a zero public root
    have hz : p.hdr.outcomeRoot = zeroHash := by
      rw [show zeroHash = List.replicate 32 (0 : UInt8) from by decide]
      apply List.ext_getElem (by simp [hlen32])
      intro j h1 h2
      have hj : j < 32 := by omega
      have hpz := hpubO j hj
      have h0 := hzero j hj
      unfold pubNat at hpz
      rw [h0, Fp.toNat_zero, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] at hpz
      simp only [Option.getD_some] at hpz
      rw [List.getElem_replicate]
      exact UInt8.toNat_inj.mp (by rw [← hpz]; rfl)
    rw [hz, hn0]
    rfl

/-- **`RunHdr`** for every main-run output: lane v3-link's `hrun`, from `HoldsP`. -/
theorem runHdr_holds {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    {oh : Nat} {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {k : NearSpecV3.WalkD0} (hw : NearSpecV3.walkD0 cb = .ok k) (hn : h.n = (flatR r.lists).length)
    {x : ExtV3} (hxr : x.receipts = r.lists)
    {block previous : NearSpecV3.Blk} (hmb : k.blks[k.b2i]? = some block)
    (hmp : k.blks[k.b2i + 1]? = some previous) (out : MainOut)
    (ha : NearSpecV3.applyNewChunk NearSpecV3.prims
        (NearSpecV3.blockCtx k.L k.H.shardId k.slotB2.gasLimit block previous.hdr.nextGasPrice)
        (LinkImplicit.Fpre r 0) x.applied = .ok out) :
    LinkHdr.RunHdr k h out :=
  runHdr_of hp hsz hH T W hw hn hxr hmb hmp
    (fun pc hc base Tf => outcomeRoot_holds hp hsz hH T W hw hmb hmp pc hc base Tf) out ha

/-- **`executions`** from `HoldsP` alone (lane v3-link's `LinkHdr.executions_run` with `hroute`
and `hrun` discharged). -/
theorem executions_holdsP {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    {oh : Nat} {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {k : NearSpecV3.WalkD0} (hw : NearSpecV3.walkD0 cb = .ok k)
    (hn : h.n = (flatR r.lists).length)
    {x : ExtV3} (hxn : x.nodes = r.nodes) (hxv : x.values = r.values)
    (hxh : x.heads = LinkImplicit.xHeads (r.ups.map ZkFormal.NearV3.UpsRows.upsE)) (hxr : x.receipts = r.lists)
    {block previous : NearSpecV3.Blk} (hmb : k.blks[k.b2i]? = some block)
    (hmp : k.blks[k.b2i + 1]? = some previous) :
    ∃ m last, m.Valid k x ∧ ImplicitRunV3 k x 1 m.result.trie.hashOf k.implicitBlks last ∧
      HeaderSemanticsV3 k h p m last :=
  LinkHdr.executions_run hp hsz hH T W hw hn hxn hxv hxh hxr hmb hmp (hroute_holds hp hsz hH T W)
    (fun _ out _ ha => runHdr_holds hp hsz hH T W hw hn hxr hmb hmp out ha)

end ZkFormal.NearV3.RcptLink
