import ZkFormal.NearV3.Candidates.ProcessRepairKeyBalance
import ZkFormal.NearV3.Candidates.ProcessRepairKeyView
import ZkFormal.NearV3.Qv.Extract.KeyProviderIds
import ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeyOwnerCore
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeyOwner
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open Qv.Extract

theorem walk_messages {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_KEYNIB)
    {bs:List RcptV3Proof.ListBlock} {e:Nat}
    (hc:RcptV3Proof.ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e)
    (hn:(flatR (bs.map (RcptV3Proof.ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).length≤W_AK)
    {ws:List WalkR} (hWT:TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws))
    {w:WalkR} (hw:w∈ws)
    (hr:w.w<(flatR (bs.map (RcptV3Proof.ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0))).length):
    ∀j,1≤j→j<w.steps.length→
      (Msg.toFp [w.w,j-1,(w.step j).sym,if j+1=w.steps.length then 1 else 0])∈
      (RcptE.keyMsgs w.w ((flatR (bs.map (RcptV3Proof.ListBlock.view
        (ProcPriorRoutedReceiptView.receipt tr) 0))).getD w.w default).keySyms).map Msg.toFp:=by
  intro j hj hj'
  let ls:=bs.map (RcptV3Proof.ListBlock.view (ProcPriorRoutedReceiptView.receipt tr) 0)
  let m:Msg:=[w.w,j-1,(w.step j).sym,if j+1=w.steps.length then 1 else 0]
  have hm:m∈walkRecvs3 ws B_KEYNIB:=by
    unfold walkRecvs3
    rw [if_neg (by decide),if_neg (by decide),if_pos rfl,List.mem_flatMap]
    refine ⟨w,hw,List.mem_map.mpr ⟨j-1,List.mem_range.mpr (by omega),?_⟩⟩
    simp only [m,show j-1+1=j by omega,show j-1+2=j+1 by omega]
  have hbal:=ProcessRepairKeyBalance.balance view hpub hc hWT
  have hsend:=hbal.mem_iff.mpr (List.mem_map.mpr ⟨m,hm,rfl⟩)
  rcases List.mem_append.mp hsend with hq|hs
  · have hL:=ProcessRepairKeyView.local_key view
    obtain ⟨q⟩:=walk_chain_exists (Qv.Candidates.KeyTrafficRepair.local_to_base hL)
    have hphysical:(List.range (tr.height 0)).flatMap (fun r=>rowTraffic
        Qv.Candidates.KeyTrafficRepair.interactions (ProcPriorRoutedKeyView.key tr) 0 r pub B_KEYNIB true)=
        q.segs.flatMap (fun p=>repairedKeyTraffic (Qv.Candidates.CombinedTable.wid.eval
          (ProcPriorRoutedKeyView.key tr) 0 p.1 pub) (physicalWalkBytes (ProcPriorRoutedKeyView.key tr) 0 p)):=
      repaired_key_physical hL q
    rw [hphysical] at hq
    obtain ⟨p,hp,hpmsg⟩:=List.mem_flatMap.mp hq
    obtain ⟨i,hi,hpi⟩:=List.getElem_of_mem hp
    subst p
    have hid:=repaired_key_owner _ _ hpmsg
    obtain ⟨n,hn0,hnP,he⟩:=queue_walk_id_range (Qv.Candidates.KeyTrafficRepair.local_to_base hL) q i hi
    rw [he] at hid
    change Fp.ofNat w.w=Fp.ofNat n at hid
    have hwP:w.w<P:=by unfold W_AK P at *;omega
    have hh:=Link.ofNat_inj hwP hnP hid
    unfold W_AK W_QV at *
    omega
  · obtain ⟨mr,hmr,he⟩:=List.mem_map.mp hs
    have hrange:=receipt_key_id_range hn hmr
    have hid:=congrArg (fun xs:List Fp=>xs.getD 0 0) he
    change (mr.map Fp.ofNat).getD 0 (Fp.ofNat 0)=Fp.ofNat w.w at hid
    rw [Link3.getD_map'] at hid
    have hidNat:mr.getD 0 0=w.w:=Link.ofNat_inj (by unfold W_QV P at *;omega)
      (by unfold W_AK P at *;omega) hid
    exact List.mem_map.mpr ⟨mr,account_owner hn hr hmr hidNat,he⟩
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeyOwner

