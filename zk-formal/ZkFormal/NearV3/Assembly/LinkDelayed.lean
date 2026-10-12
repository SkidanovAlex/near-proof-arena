import ZkFormal.NearV3.Rcpt.Link.QvMain
import ZkFormal.NearV3.Assembly.LinkRcptWalk

/-!
# ZkFormal.NearV3.Assembly.LinkDelayed — `DelayedCovered` from `HoldsP`

The qv assembly (`Qv.Extract.QvRc.assemble_sub`, as in lane v3-rcpt-sound's
`RcptLink.queue_reads_holdsP`, keeping its third conclusion) gives, for every implicit instance
`1 ≤ t ≤ kPublic`, the missing-chunk read of `keyDelayedIdx` on `queueTree … t = Fpre r t`;
`kPublic = p.hdr.K` (`ProcessRepairQueuePublic.queue_count`).  Hence **`delayedCovered_holds`**.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkDelayed

open ZkFormal.NearV3 ZkFormal.NearV3.RcptLink ZkFormal.NearV3.Qv.Extract

/-- **`DelayedCovered`**: the delayed-receipts index is determined in every implicit instance. -/
theorem delayedCovered_holds {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    {oh : Nat} {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    LinkImplicit.DelayedCovered p.hdr.K r := by
  have L := trieLink_of hp hsz hH T W
  have S := shaHyp_holds hp hsz hH T W
  have hQ : TableLocal Qv.Candidates.KeyTrafficRepair.table tr T_QV
      (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) :=
    tableLocal_of_holdsP hH (t := T_QV) rfl
  have hl := Qv.Candidates.KeyTrafficRepair.local_to_base hQ
  obtain ⟨q⟩ := walk_chain_exists hl
  obtain ⟨pc⟩ := parser_chain_exists hl q
  obtain ⟨ss, htau, hlen, ⟨hj, hc⟩, hreq, he, hb, ha⟩ :=
    QvRc.queue_premises hl q pc W.values (recComplete_holdsP hH T W q pc) (bytes8_holdsP hH T W S)
      (qsh_holdsP hH) (qvc_holdsP hH)
  obtain ⟨-, -, hI⟩ := QvRc.assemble_sub hQ q r.nodes r.values r.heads L.chain
    (walkHyp_holdsP hp hsz hH T W) W.walks (fun w hw => List.mem_append_left _ hw) W.values
    r.lists (LinkRcptWalk.flatR_le hp W) (qv_hK hp oh tr T_QV 0) ss htau hlen hj hc hreq
    ((rcptRecvs3 r.lists B_FINAL).map Msg.toFp) (qv_hkey hH T) (qv_hfinal hH T) he hb ha
  intro τ h1 hK
  have hk := (Candidates.ProcessRepairQueuePublic.queue_count hp oh tr T_QV 0).1
  obtain ⟨hf, -⟩ := hI τ h1 (by rw [hk]; exact hK)
  simp only [Qv.missingRequest] at hf
  show (queueTree r.nodes r.values r.heads τ).find NearSpecV3.keyDelayedIdx ≠ none
  rw [hf]; simp

end LinkDelayed

end ZkFormal.NearV3.Assembly
