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

end ZkFormal.NearV3.Assembly
