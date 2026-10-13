import ZkFormal.NearV3.Public.Prepared

/-! Declarations of `ZkFormal.NearV3.Assembly.RcptCandidateFamilyPublicMemory` split out (unchanged names and statements) so that
  importers needing only these do not pull in the rest of the module (certificate pruning). -/

namespace ZkFormal.NearV3.Assembly.ReceiptFamilyMemory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2


/-- The actual prepared public plans never open or close account memory. -/
theorem prepared_no_mem (s : PubSeg) (hs : s∈Public.preparedSegments) : s.bus≠B_MEM := by
  have hall : Public.preparedSegments.all (fun s=>decide (s.bus≠B_MEM))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

theorem prepared_mem_count_zero (AP : AirP) (hs : AP.pubSegs=Public.preparedSegments)
    (pub : List Fp) (sd : Bool) (msg : List Fp) : pubCount AP pub B_MEM sd msg=0 := by
  unfold pubCount
  suffices ((pubMsgs AP pub).filter (fun x=>decide (x=(B_MEM,sd,msg))))=[] by rw [this];rfl
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  have hn : x≠(B_MEM,sd,msg) := by
    intro he
    subst x
    simp only [pubMsgs,List.mem_flatMap,List.mem_map] at hx
    obtain ⟨s,hseg,m,hm,he⟩ := hx
    have hb := congrArg (fun x : Nat×Bool×List Fp=>x.1) he
    exact prepared_no_mem s (hs ▸ hseg) hb
  simp [hn]

end ZkFormal.NearV3.Assembly.ReceiptFamilyMemory
