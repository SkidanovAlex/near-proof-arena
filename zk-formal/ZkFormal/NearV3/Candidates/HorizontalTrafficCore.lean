import ZkFormal.Near.Render.Proof.Base

/-! Declarations of `ZkFormal.NearV3.Candidates.HorizontalTraffic` split out (unchanged names and statements) so that
  importers needing only these do not pull in the rest of the module (certificate pruning). -/
namespace ZkFormal.NearV3.Candidates.HorizontalTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

def rowCount (is : List Interaction) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (bus : Nat) (send : Bool) (msg : List Fp) : Nat :=
  (is.map (fun i=>if i.bus=bus ∧ i.send=send ∧ i.msgVal tr t r pub=msg then i.multNat tr t r pub else 0)).sum

theorem add_fold {α : Type} (xs : List α) (f : α→Nat) (n : Nat) :
    xs.foldr (fun x acc=>f x+acc) n=(xs.map f).sum+n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_assoc]

theorem table_sum (is : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (bus : Nat) (send : Bool) (msg : List Fp) :
    tableBusCount is tr t pub bus send msg=
      ((List.range (tr.height t)).map (fun r=>rowCount is tr t r pub bus send msg)).sum := by
  simp only [tableBusCount,add_fold,rowCount,Nat.add_zero]

def mapI (f : Expr→Expr) (i : Interaction) : Interaction :=
  {i with mult:=i.mult.map f,msg:=i.msg.map f}

theorem mult_map (f : Expr→Expr) (xs : List Expr) (a b : Trace Fp)
    (t r k : Nat) (pub : List Fp)
    (h : ∀e∈xs,(f e).eval a t r pub=e.eval b t r pub) :
    Interaction.multNat.go a t r pub (xs.map f) k=Interaction.multNat.go b t r pub xs k := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,Interaction.multNat.go,h x (by simp)]
    rw [ih (k+1) (by intro e he; exact h e (by simp [he]))]

theorem row_map (f : Expr→Expr) (xs : List Interaction) (a b : Trace Fp)
    (t r : Nat) (pub : List Fp) (bus : Nat) (send : Bool) (msg : List Fp)
    (h : ∀i∈xs,∀e∈i.exprs,(f e).eval a t r pub=e.eval b t r pub) :
    rowCount (xs.map (mapI f)) a t r pub bus send msg=rowCount xs b t r pub bus send msg := by
  unfold rowCount
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hm : (mapI f i).msgVal a t r pub=i.msgVal b t r pub := by
    simp only [Interaction.msgVal,mapI,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro e he
    exact h i hi e (List.mem_append_right _ he)
  have hb : (mapI f i).multNat a t r pub=i.multNat b t r pub :=
    mult_map f i.mult a b t r 0 pub (by intro e he; exact h i hi e (List.mem_append_left _ he))
  change (if i.bus=bus ∧ i.send=send ∧ (mapI f i).msgVal a t r pub=msg
    then (mapI f i).multNat a t r pub else 0)=_
  rw [hm,hb]

@[simp] theorem mapI_id (i : Interaction) : mapI id i=i := by
  cases i
  simp [mapI]

end ZkFormal.NearV3.Candidates.HorizontalTraffic
