import NearCompression.PreparedDecodedBusContinuation
namespace NearCompression
open ArenaCore.Security

/-- Partition a chronological experiment by an earlier-only selector. None
is the valid-auxiliary branch; the two Boolean tags select invalid tables.
The identity applies equally to acceptance and shared downstream failures. -/
theorem history_three_branch_count {A R : Type} (earlier : List A) (later : List R)
    (branch : A → Option Bool) (event : A → R → Prop) :
    let experiment := earlier.flatMap (fun a=>later.map (fun r=>(a,r)))
    count experiment (fun x=>event x.1 x.2)=
      count experiment (fun x=>branch x.1=none ∧ event x.1 x.2)+
      count experiment (fun x=>branch x.1=some false ∧ event x.1 x.2)+
      count experiment (fun x=>branch x.1=some true ∧ event x.1 x.2) := by
  classical
  intro experiment
  have partition : ∀ xs : List (A × R),
      count xs (fun x=>event x.1 x.2)=
        count xs (fun x=>branch x.1=none ∧ event x.1 x.2)+
        count xs (fun x=>branch x.1=some false ∧ event x.1 x.2)+
        count xs (fun x=>branch x.1=some true ∧ event x.1 x.2) := by
    intro xs
    induction xs with
    | nil => simp [count]
    | cons x xs ih =>
      cases h : branch x.1 with
      | none => simp [count_cons,h] at *;omega
      | some b => cases b <;> simp [count_cons,h] at * <;> omega
  exact partition experiment

/-- Sum disjoint history branches, preserving a single shared accepted
failure count. Budgets already include each branch's chronological scaling;
no uniform conditional bound on downstream failure is inferred. -/
theorem history_three_branch_budget {A R : Type} (earlier : List A) (later : List R)
    (branch : A → Option Bool) (accept failure : A → R → Prop)
    (scale busBudget firstBudget secondBudget jointBudget : Nat)
    (each : ∀ tag : Option Bool,
      count (earlier.flatMap (fun a=>later.map (fun r=>(a,r))))
        (fun x=>branch x.1=tag ∧ accept x.1 x.2)*scale≤
      (match tag with | none=>busBudget | some false=>firstBudget | some true=>secondBudget)+
      count (earlier.flatMap (fun a=>later.map (fun r=>(a,r))))
        (fun x=>branch x.1=tag ∧ (accept x.1 x.2 ∧ failure x.1 x.2))*scale)
    (joint : count (earlier.flatMap (fun a=>later.map (fun r=>(a,r))))
      (fun x=>accept x.1 x.2 ∧ failure x.1 x.2)*scale≤jointBudget) :
    count (earlier.flatMap (fun a=>later.map (fun r=>(a,r))))
      (fun x=>accept x.1 x.2)*scale≤busBudget+firstBudget+secondBudget+jointBudget := by
  have accepts := history_three_branch_count earlier later branch accept
  have failures := history_three_branch_count earlier later branch (fun a r=>accept a r ∧ failure a r)
  have good := each none
  have first := each (some false)
  have second := each (some true)
  dsimp only at accepts failures good first second
  rw [accepts,Nat.add_mul,Nat.add_mul]
  rw [failures,Nat.add_mul,Nat.add_mul] at joint
  omega

end NearCompression
