import ZkFormal.NearV3.Rcpt.Extract.RcptView
import ZkFormal.Near.Link.Walks

/-! Declarations of `ZkFormal.NearV3.Candidates.ProcessRepairReceiptReceiverShape` split out (unchanged names and statements) so that
  importers needing only these do not pull in the rest of the module (certificate pruning). -/
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptReceiverShape
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near


theorem native_key (x:RcptE) (hb:Bytes8 x.v) (hn:x.v.length≤64):
    x.keySyms.length<P ∧ (∀a∈x.keySyms,a<P) ∧
      x.keySyms.take (x.keySyms.length-1)=NearSpec.accountKeyPath (toBytes x.v):=by
  have he:=Link.keySyms_eq x.toRcptV hb
  have hlen:=Link.keySyms_length x.toRcptV
  refine ⟨by unfold P;omega,?_,?_⟩
  · exact Link.keySyms_lt x.toRcptV (fun a ha=>Nat.lt_trans (hb a ha) (by decide))
  · rw [he]
    simp only [List.length_append,List.length_cons,List.length_nil,Nat.add_sub_cancel]
    simp
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptReceiverShape
