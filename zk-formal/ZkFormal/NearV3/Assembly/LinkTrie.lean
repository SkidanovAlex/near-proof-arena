import ZkFormal.NearV3.Assembly.LinkChain

/-!
# ZkFormal.NearV3.Assembly.LinkTrie — the per-instance trie facts of the records

All bus-level hypotheses of the `Link/` trie layer, derived from `HoldsP nearAirV3` and the
views (`TrieLink`, `trieLink_of`), and their first consequences for every head `h`
(instance `h.tau`, root record `h.rid`), with `R = recsOf (vpos (vid0 es)) vs`,
`V = valsOf3 vs es`:

* `rootDigest_of` — `digest R V h.rid = toB h.pre` (`root_tau`);
* `storeHF_of` — the witness store of the instance is hash-functional (`store_hashFunctional`);
* `recBytes_of` — every node record's pre serialization is bytes (`rec_bytes`).
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

/-- The record-level bus facts of the trie tables. -/
structure TrieLink (pub : List Fp) (tr : Trace Fp) (r : V3Records) (K : Nat) (r0 rK : List Nat) : Prop where
  parent : ZkFormal.NearV3.Link3.ParentBal r.nodes r.heads
  vparent : ZkFormal.NearV3.Link3.VParentBal r.nodes r.values
  ent : ZkFormal.NearV3.Link3.EntBal r.nodes r.values
  dup : ZkFormal.NearV3.Link3.DupBal r.uniq r.nodes r.values
  digs : ZkFormal.NearV3.Link3.DigsBal r.nodes r.heads r.uniq
  edge : ZkFormal.NearV3.UpsRows.WalkBal r.nodes r.heads r.walks r.ups B_EDGE
  bmap : ZkFormal.NearV3.UpsRows.WalkBal r.nodes r.heads r.walks r.ups ZkFormal.NearV3.B_BMAP
  upb : ZkFormal.NearV3.UpsRows.UpbBal r.nodes r.ups
  sha : ZkFormal.NearV3.Link3.ShaHyp r.nodes r.heads r.values (othersBytes tr pub r)
    (shaU tr pub true) (shaU tr pub false)
  chain : ZkFormal.NearV3.RootChain r.heads (r.ups.map ZkFormal.NearV3.UpsRows.upsE) K r0 rK

/-- **The trie bus facts from `HoldsP`.** -/
theorem trieLink_of {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    TrieLink (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r p.hdr.K
      (p.hdr.prevStateRoot.map UInt8.toNat) (p.hdr.postStateRoot.map UInt8.toNat) where
  parent := parentBal_of hH T
  vparent := vparentBal_of hH T
  ent := entBal_of hH T
  dup := dupBal_of hH T
  digs := digsBal_of hH T
  edge := walkBal_of hH T (.inl rfl)
  bmap := walkBal_of hH T (.inr rfl)
  upb := upbBal_of hH T
  sha := shaHyp_holds hp hsz hH T W
  chain := rootChain_of hp hsz hH T W

section
variable {pub : List Fp} {tr : Trace Fp} {r : V3Records} {K : Nat} {r0 rK : List Nat}

theorem recBytes_of (W : V3RecordsWf pub r) (L : TrieLink pub tr r K r0 rK) :
    ∀ s ∈ r.nodes, ∀ x ∈ s.v.ser false, x < 256 :=
  ZkFormal.NearV3.Link3.rec_bytes W.nodes W.heads W.values L.parent L.sha

/-- **Root of an instance**: the record tree under a head hashes to the head's pre root. -/
theorem rootDigest_of (W : V3RecordsWf pub r) (L : TrieLink pub tr r K r0 rK)
    {h : ZkFormal.NearV3.HeadE} (hh : h ∈ r.heads) :
    digest (ZkFormal.NearV3.Link3.recsOf (ZkFormal.NearV3.Link3.vpos (ZkFormal.NearV3.Link3.vid0 r.values)) r.nodes)
      (ZkFormal.NearV3.Link3.valsOf3 r.nodes r.values) h.rid = ZkFormal.NearV3.Link3.toB h.pre :=
  ZkFormal.NearV3.Link3.root_tau W.nodes W.heads W.values L.parent L.vparent L.sha hh

/-- **The witness store of an instance is hash-functional.** -/
theorem storeHF_of (W : V3RecordsWf pub r) (L : TrieLink pub tr r K r0 rK)
    {h : ZkFormal.NearV3.HeadE} (hh : h ∈ r.heads) :
    HashFunctional (storeOf (ZkFormal.NearV3.Link3.recsOf
      (ZkFormal.NearV3.Link3.vpos (ZkFormal.NearV3.Link3.vid0 r.values)) r.nodes)
      (ZkFormal.NearV3.Link3.valsOf3 r.nodes r.values) h.tau) :=
  ZkFormal.NearV3.Link3.store_hashFunctional W.nodes W.heads W.values W.uniq L.parent L.vparent L.sha
    L.digs L.dup L.ent hh

end

/-- **`MEMD`** (only `upsV3` touches it): the ups segments' `MEMD` sends are a permutation of their
receives (the `hmemd` hypothesis of `upsV3_linkB`). -/
theorem memdBal_of {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) :
    (((ZkFormal.NearV3.upsTraffic r.ups).sends ZkFormal.NearV3.B_MEMD).map Msg.toFp).Perm
      (((ZkFormal.NearV3.upsTraffic r.ups).recvs ZkFormal.NearV3.B_MEMD).map Msg.toFp) := by
  apply List.perm_iff_count.mpr
  intro m
  have h := bal_users hH (b := ZkFormal.NearV3.B_MEMD) (U := [T_UPS]) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [ups_count T _ _ _ (by decide +kernel), ups_count T _ _ _ (by decide +kernel)] at h
  exact h

/-- **Walk back to a representative** (step 3 of the `mainStoreBytes` plan): every `uniq` entry
has an earlier-or-equal entry with `eq = 0`, the same instance and the same message bytes. -/
theorem uniq_walkback {vs : List ZkFormal.NearV3.NodeS3} {es : List ZkFormal.NearV3.ValE}
    {us : List ZkFormal.NearV3.UniqE} (hw : ZkFormal.NearV3.NodeWf3 vs) (hvw : ZkFormal.NearV3.ValWf es)
    (huw : ZkFormal.NearV3.UniqWf us) (hDUP : ZkFormal.NearV3.Link3.DupBal us vs es)
    (hENT : ZkFormal.NearV3.Link3.EntBal vs es) :
    ∀ t (ht : t < us.length), ∃ t0, ∃ h0 : t0 < us.length, t0 ≤ t ∧ us[t0].eq = 0 ∧
      ZkFormal.NearV3.Link3.bOf vs es us[t0].eid = ZkFormal.NearV3.Link3.bOf vs es us[t].eid ∧
      us[t0].tau = us[t].tau := by
  intro t
  induction t with
  | zero =>
    intro ht
    refine ⟨0, ht, Nat.le_refl 0, huw.first _ ?_, rfl, rfl⟩
    cases us with
    | nil => simp at ht
    | cons a l => rfl
  | succ t ih =>
    intro ht
    have hc := huw.canon _ (List.getElem_mem ht)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hc.2.2.2.2.1 with he | he
    · exact ⟨t + 1, ht, Nat.le_refl _, he, rfl, rfl⟩
    · obtain ⟨t0, h0, hle, heq, hb, hτ⟩ := ih (by omega)
      have hd := ZkFormal.NearV3.Link3.dup_bytes hw hvw huw hDUP hENT t ht he
      obtain ⟨-, hτ1, heq1, -⟩ := huw.link t ht
      have hst := (heq1 he).1
      have hct := (huw.canon _ (List.getElem_mem (show t < us.length by omega))).2.2.1
      simp only [hst, Nat.add_zero, Nat.mod_eq_of_lt hct] at hτ1
      exact ⟨t0, h0, by omega, heq, by rw [hb, hd], by rw [hτ, hτ1]⟩

end ZkFormal.NearV3.Assembly
