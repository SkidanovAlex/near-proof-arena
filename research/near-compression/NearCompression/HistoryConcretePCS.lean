import NearCompression.ConcretePCSEvidence
import NearCompression.PreparedSelectedGKRBudget
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

/-- Earlier histories may select different committed source oracles and PCS
strategies. Each evidence record fixes its oracles across later local draws.
The actual concrete PCS theorem is applied per history and then summed. -/
theorem history_concrete_pcs_failure_budget {A : Type}
    (earlier : List A) (layout : GKRJointLayout) (sample : List Fp8) (distinct : sample.Nodup)
    (T queries : Nat) (sizes : Nat → Nat) (earlierRounds : List Nat) (n0 n1 : Nat)
    (event : A → PreparedTwoTableContinuation → Prop)
    (evidence : ∀ a∈earlier,ConcreteTwoTablePCSEvidence layout sample distinct T queries sizes
      earlierRounds (n0+1) (n1+1)
      (fun p q rho blocks z path qs=>event a (p,q,rho,blocks,z,path,qs))) :
    count (earlier.flatMap (fun a=>(preparedTwoTableContinuations sample layout earlierRounds queries n0 n1).map
      (fun r=>(a,r)))) (fun x=>event x.1 x.2)*sample.length≤
      earlier.length*concreteTwoTablePCSBudget layout sample T queries sizes earlierRounds (n0+1) (n1+1) := by
  induction earlier with
  | nil => simp [count]
  | cons a rest ih =>
    have head := concrete_two_table_evidence_bound layout sample distinct T queries sizes earlierRounds (n0+1) (n1+1)
      (fun p q rho blocks z path qs=>event a (p,q,rho,blocks,z,path,qs)) (evidence a (by simp))
    have tail := ih (fun r hr=>evidence r (List.mem_cons_of_mem _ hr))
    change count (preparedTwoTableContinuations sample layout earlierRounds queries n0 n1) (event a)*sample.length≤_ at head
    simp only [List.flatMap_cons,count_append,count_map,Nat.add_mul,List.length_cons]
    simpa only [Nat.one_mul,Nat.add_comm] using Nat.add_le_add head tail

end NearCompression
