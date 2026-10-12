import ZkFormal.NearV3.Rcpt.Link.QvPrem
import ZkFormal.NearV3.Rcpt.Link.QvCodec
import ZkFormal.NearV3.Rcpt.Link.QvBal

/-!
# ZkFormal.NearV3.Rcpt.Link.QvAssemble — the main queue reads from `HoldsP`

`assemble_sub`: `Qv.Extract.assemble_native_queue_reads` with the walk hypothesis `G` over a
**superset** `ws` of the walk records `ws0` that carry the `KEYNIB` / `FINAL` balances (the trie
link's `WalkHyp` is over `allWalks r.walks r.ups`; the ups-derived walks use neither bus).

**`queue_reads_holdsP`**: from `HoldsP` + views, the trie link's `ShaHyp` (for `Bytes8` of the
value records), `RootChain` and `WalkHyp` (lane v3-link), there are a walk chain `q` and a shard list
`ss` with `(queueMainValues r.nodes r.values tr T_QV q ss).Valid` and its three main reads on
`queueTree r.nodes r.values r.heads 0` (and the implicit reads).
-/

namespace ZkFormal.NearV3.Qv.Extract.QvRc

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

/-- `assemble_native_queue_reads` with the walk hypothesis over a superset of the balanced walks. -/
theorem assemble_sub {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal Candidates.KeyTrafficRepair.table tr tt pub) (q : WalkChain tr tt)
    (vs : List NodeS3) (es : List ValE) (hs : List HeadE) {ws0 ws : List WalkR}
    {us : List UpsE} {K : Nat} {r0 rK : List Nat}
    (C : RootChain hs us K r0 rK)
    (G : Walk3.WalkHyp (Link3.vpos (Link3.vid0 es)) vs (Link3.valsOf3 vs es) hs ws)
    (hW0 : WalkWf3 ws0) (hsub : ∀ w ∈ ws0, w ∈ ws)
    (hv : ValWf es) (ls : RcptV3Vs) (hn : (flatR ls).length≤W_AK)
    (hK : (kPublic.eval tr tt 0 pub).toNat<64)
    (ss : List Nat) (htau : Fp) (hlen : ss.length<P)
    (hj : 1<q.segs.length) (hc : cv tr tt (q.segs[1]'hj).1 Candidates.ValueTable.count=ss.length)
    (hrequests : ∀ m∈(List.range (segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic interactions tr tt r pub B_QSH false), m∈Parser.nativeShardMessages htau ss)
    (others : List (List Fp))
    (hkey : ((List.range (tr.height tt)).flatMap
      (fun r => rowTraffic Candidates.KeyTrafficRepair.interactions tr tt r pub B_KEYNIB true) ++
      (rcptSends3 pub ls B_KEYNIB).map Msg.toFp).Perm ((walkRecvs3 ws0 B_KEYNIB).map Msg.toFp))
    (hfinal : ((walkSends3 ws0 B_FINAL).map Msg.toFp).Perm
      ((List.range (tr.height tt)).flatMap
        (fun r => rowTraffic Candidates.KeyTrafficRepair.interactions tr tt r pub B_FINAL false) ++ others))
    (he : ∀ j∈[0,2], cv tr tt (q.segs.getD j (0,0)).1 absent=0 →
      ∃ e∈es, e.vid=cv tr tt (q.segs.getD j (0,0)).1 Candidates.ValueTable.vid ∧
        EmptyQueue (some (toBytes e.bytes)))
    (hb : cv tr tt (q.segs.getD 1 (0,0)).1 absent=0 →
      ∃ e∈es, e.vid=cv tr tt (q.segs.getD 1 (0,0)).1 Candidates.ValueTable.vid ∧
        BufferedValue (some (toBytes e.bytes)) ss)
    (ha : cv tr tt (q.segs.getD 1 (0,0)).1 absent≠0 → ss=[]) :
    (queueMainValues vs es tr tt q ss).Valid ∧
    (queueMainValues vs es tr tt q ss).Reads
      (queueTree vs es hs 0) (queueTree vs es hs 0) (queueTree vs es hs 0) ∧
    (∀ t, 1≤t → t≤(kPublic.eval tr tt 0 pub).toNat →
      (missingRequest (queueTree vs es hs t)).Holds (queueTree vs es hs t)) := by
  have hL := Candidates.KeyTrafficRepair.local_to_base h
  have hread : ∀ i (hi : i<q.segs.length),
      (queueTree vs es hs (cv tr tt (q.segs[i]'hi).1 Candidates.ValueTable.tau)).find
        (NearSpec.nibbles (physicalWalkBytes tr tt (q.segs[i]'hi)))=
        some (queueValue vs es tr tt (q.segs[i]'hi).1) := by
    intro i hi
    obtain ⟨w,hw,hk,hf⟩ := balanced_queue_lookup h q i hi ls hn hK hW0 others hkey hfinal
    exact queue_root_read hL q i hi C G (hsub w hw) hk hf
  exact ⟨main_queue_valid vs hv tr tt q ss he hb ha,
    main_queue_reads hL q vs es hs ss htau hlen hj hc hrequests hread,
    implicit_queue_reads hL q vs es hs hread⟩

end ZkFormal.NearV3.Qv.Extract.QvRc

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Assembly
  ZkFormal.NearV3.Qv.Extract

/-- `|flatR| ≤ W_AK` (`= 8192`): `|flatR| = h.n = p.hdr.n ≤ 5000`. -/
theorem flatR_le_WAK {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hp : NearSpecV3.prepD0 cb h = .ok p) {ls : RcptV3Vs} (hn : h.n = (flatR ls).length) :
    (flatR ls).length ≤ W_AK := by
  obtain ⟨pc, -, hb⟩ := ZkFormal.NearV3.Sched.bind_ok hp
  have h1 := (ZkFormal.NearV3.RcptV3Proof.prepBody_count_guard hb).1
  have h2 := (ZkFormal.NearV3.RcptV3Proof.prepD0_count_bound hp).1
  have : W_AK = 8192 := rfl
  omega

/-- **The main queue reads from `HoldsP`.**  Inputs from lane v3-link: the trie link's `ShaHyp`
(`shaHyp_holds`), a `RootChain` of the heads (`rootChain_of`) and a `WalkHyp` over walks `ws`
containing `r.walks` (e.g. `allWalks r.walks r.ups`). -/
theorem queue_reads_holdsP {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (hn : h.n = (flatR r.lists).length) {others : List Msg}
    (S : Link3.ShaHyp r.nodes r.heads r.values others
      (shaU tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) true)
      (shaU tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) false))
    {ws : List WalkR} {us : List UpsE} {K : Nat} {r0 rK : List Nat}
    (C : RootChain r.heads us K r0 rK)
    (G : Walk3.WalkHyp (Link3.vpos (Link3.vid0 r.values)) r.nodes (Link3.valsOf3 r.nodes r.values)
      r.heads ws)
    (hsub : ∀ w ∈ r.walks, w ∈ ws) :
    ∃ (q : WalkChain tr T_QV) (ss : List Nat),
      (queueMainValues r.nodes r.values tr T_QV q ss).Valid ∧
      (queueMainValues r.nodes r.values tr T_QV q ss).Reads
        (queueTree r.nodes r.values r.heads 0) (queueTree r.nodes r.values r.heads 0)
        (queueTree r.nodes r.values r.heads 0) := by
  have hQ : TableLocal Qv.Candidates.KeyTrafficRepair.table tr T_QV
      (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) :=
    tableLocal_of_holdsP hH (t := T_QV) rfl
  have hl := Qv.Candidates.KeyTrafficRepair.local_to_base hQ
  obtain ⟨q⟩ := walk_chain_exists hl
  obtain ⟨pc⟩ := parser_chain_exists hl q
  obtain ⟨ss, htau, hlen, ⟨hj, hc⟩, hreq, he, hb, ha⟩ :=
    QvRc.queue_premises hl q pc W.values (recComplete_holdsP hH T W q pc) (bytes8_holdsP hH T W S)
      (qsh_holdsP hH) (qvc_holdsP hH)
  obtain ⟨hV, hR, -⟩ := QvRc.assemble_sub hQ q r.nodes r.values r.heads C G W.walks hsub W.values
    r.lists (flatR_le_WAK hp hn) (qv_hK hp oh tr T_QV 0) ss htau hlen hj hc hreq
    ((rcptRecvs3 r.lists B_FINAL).map Msg.toFp) (qv_hkey hH T) (qv_hfinal hH T) he hb ha
  exact ⟨q, ss, hV, hR⟩

end ZkFormal.NearV3.RcptLink
