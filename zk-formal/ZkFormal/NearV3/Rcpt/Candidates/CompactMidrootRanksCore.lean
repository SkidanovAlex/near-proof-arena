import ZkFormal.NearV3.Rcpt.Candidates.UpsPhysicalPrefix

/-! Declarations of `ZkFormal.NearV3.Rcpt.Candidates.CompactMidrootRanks` split out (unchanged names and statements) so that
  importers needing only these do not pull in the rest of the module (certificate pruning). -/

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen UpsRows

theorem prefix_midroot_records (p : List WStep3) (Is : List UpsInst) :
    (physicalPrefixUps p Is).map (fun I=>[I.tau,I.rid]++I.mid)=Is.map (fun I=>[I.tau,I.rid]++I.mid) := by
  induction Is generalizing p with
  | nil=>rfl
  | cons I Is ih=>
    simpa only [physicalPrefixUps,rankUpsList,List.map_cons,syncUps,rankUps] using congrArg
      (List.cons ([I.tau,I.rid]++I.mid)) (ih (p++fourSteps I))

theorem prefix_mid_digests (p : List WStep3) (Is : List UpsInst) :
    (physicalPrefixUps p Is).map UpsInst.mid=Is.map UpsInst.mid := by
  induction Is generalizing p with
  | nil=>rfl
  | cons I Is ih=>
    simpa only [physicalPrefixUps,rankUpsList,List.map_cons,syncUps,rankUps] using congrArg
      (List.cons I.mid) (ih (p++fourSteps I))

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
