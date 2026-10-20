import NearCompression.SelectedGKREvidence
import NearCompression.SelectedBranchTransfer
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra ArenaCore.Security

/-- Both numeric local budgets are derived from semantic selected-table/GKR
evidence. Only the valid-auxiliary bus and final shared PCS estimates remain
numeric inputs. Neither table receives its own numerical PCS error budget. -/
theorem two_table_selected_gkr_composition {A : Type}
    (sample : List Fp8) (distinct : sample.Nodup) (earlier : List A)
    (layout : GKRJointLayout) (earlierRounds : List Nat) (queries n0 n1 : Nat)
    (branch : A → Option Bool)
    (accept failure : A → LocalChallengePrefix Fp8 → LocalChallengePrefix Fp8 →
      (Fp8 × (List (GKRBlock Fp8) × (List Fp8 × (List Fp8 × List Nat)))) → Prop)
    (busBudget jointBudget : Nat) :
    let first := decodedLocalPrefixes sample (n0+1)
    let second := decodedLocalPrefixes sample (n1+1)
    let later := twoTablePCSContinuations sample layout earlierRounds queries
    let chosen0 := earlier.filter (fun a=>@decide (branch a=some false) (Classical.propDecidable _))
    let chosen1 := earlier.filter (fun a=>@decide (branch a=some true) (Classical.propDecidable _))
    let continuation := first.flatMap (fun p=>second.flatMap (fun q=>later.map (fun r=>(p,q,r))))
    let experiment := earlier.flatMap (fun a=>continuation.map (fun r=>(a,r)))
    ∀ c0 : SelectedFutureGKREvidence sample distinct chosen0 second layout earlierRounds queries n0
      (fun a p qr=>accept a p qr.1 qr.2) (fun a p qr=>failure a p qr.1 qr.2),
    ∀ c1 : SelectedLastGKREvidence sample distinct (chosen1.flatMap (fun a=>first.map (fun p=>(a,p))))
      layout earlierRounds queries n1 (fun ap q r=>accept ap.1 ap.2 q r) (fun ap q r=>failure ap.1 ap.2 q r),
    (count experiment (fun x=>branch x.1=none ∧ accept x.1 x.2.1 x.2.2.1 x.2.2.2)*sample.length≤busBudget+
      count experiment (fun x=>branch x.1=none ∧ (accept x.1 x.2.1 x.2.2.1 x.2.2.2 ∧ failure x.1 x.2.1 x.2.2.1 x.2.2.2))*sample.length) →
    (count experiment (fun x=>accept x.1 x.2.1 x.2.2.1 x.2.2.2 ∧ failure x.1 x.2.1 x.2.2.1 x.2.2.2)*sample.length≤jointBudget) →
    count experiment (fun x=>accept x.1 x.2.1 x.2.2.1 x.2.2.2)*sample.length≤
      busBudget+
      selectedFutureEvidenceBudget sample distinct chosen0 second layout earlierRounds queries n0
        (fun a p qr=>accept a p qr.1 qr.2) (fun a p qr=>failure a p qr.1 qr.2) c0+
      selectedLastEvidenceBudget sample distinct (chosen1.flatMap (fun a=>first.map (fun p=>(a,p))))
        layout earlierRounds queries n1 (fun ap q r=>accept ap.1 ap.2 q r) (fun ap q r=>failure ap.1 ap.2 q r) c1+
      jointBudget := by
  intro first second later chosen0 chosen1 continuation experiment c0 c1 good joint
  apply two_table_filtered_history_budget earlier first second later branch accept failure sample.length
    busBudget _ _ jointBudget good _ _ joint
  · exact selected_future_evidence_bound sample distinct chosen0 second layout earlierRounds queries n0
      (fun a p qr=>accept a p qr.1 qr.2) (fun a p qr=>failure a p qr.1 qr.2) c0
  · exact selected_last_evidence_bound sample distinct (chosen1.flatMap (fun a=>first.map (fun p=>(a,p))))
      layout earlierRounds queries n1 (fun ap q r=>accept ap.1 ap.2 q r) (fun ap q r=>failure ap.1 ap.2 q r) c1

end NearCompression
