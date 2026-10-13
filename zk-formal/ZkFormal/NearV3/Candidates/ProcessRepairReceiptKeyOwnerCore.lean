import ZkFormal.NearV3.Rcpt.Extract.RcptView

/-! Declarations of `ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeyOwner` split out (unchanged names and statements) so that
  importers needing only these do not pull in the rest of the module (certificate pruning). -/
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeyOwner
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near


theorem flat_lookup (ls:RcptV3Vs) {j:Nat} (hj:j<ls.length) (k:Nat) (hk:k<ls[j].rs.length):
    (flatR ls).getD (baseR ls j+k) default=ls[j].rs.getD k default:=by
  induction ls generalizing j with
  | nil=>simp at hj
  | cons L ls ih=>
    cases j with
    | zero=>
      simp only [baseR,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add,
        flatR,List.flatMap_cons,List.getElem_cons_zero]
      have hk0:k<L.rs.length:=hk
      simp [List.getD_eq_getElem?_getD,List.getElem?_append,hk0]
    | succ j=>
      have hj':j<ls.length:=by simpa using hj
      have hk':k<ls[j].rs.length:=hk
      have h:=ih hj' hk'
      simp only [baseR,List.take_succ_cons,List.map_cons,List.sum_cons,
        flatR,List.flatMap_cons,List.getElem_cons_succ]
      simpa only [flatR,baseR,List.getD_eq_getElem?_getD,List.getElem?_append,
        Nat.add_assoc,Nat.not_lt_of_ge (Nat.le_add_right _ _),ite_false,Nat.add_sub_cancel_left] using h

theorem message_id (r:Nat) (ss:List Nat) {m:Msg} (hm:m∈RcptE.keyMsgs r ss):m.getD 0 0=r:=by
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hm
  rfl

theorem account_owner {pub:List Fp} {ls:RcptV3Vs}
    (hn:(flatR ls).length≤W_AK) {r:Nat} (hr:r<(flatR ls).length)
    {m:Msg} (hm:m∈rcptSends3 pub ls B_KEYNIB) (hid:m.getD 0 0=r):
    m∈RcptE.keyMsgs r ((flatR ls).getD r default).keySyms:=by
  simp only [rcptSends3,show B_KEYNIB≠B_BYTES by decide,show B_KEYNIB≠B_RCL by decide,
    ite_false,List.nil_append] at hm
  obtain ⟨j,hj,hm⟩:=List.mem_flatMap.mp hm
  have hj:=List.mem_range.mp hj
  obtain ⟨⟨r',off,x⟩,hp,hm⟩:=List.mem_flatMap.mp hm
  have hget:ls.getD j default=ls[j]:=by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
  simp only [located,hget,List.mem_map,List.mem_range] at hp
  obtain ⟨k,hk,hp⟩:=hp
  cases hp
  simp only [rSends,show B_KEYNIB≠B_BYTES by decide,ite_false,ite_true,List.mem_append] at hm
  rcases hm with hm|hm
  · have he:baseR ls j+k=r:=(message_id _ _ hm).symm.trans hid
    rw [←he,flat_lookup ls hj k hk]
    exact hm
  · split at hm
    · have he:W_AK+(baseR ls j+k)=r:=(message_id _ _ hm).symm.trans hid
      omega
    · simp at hm

end ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeyOwner
