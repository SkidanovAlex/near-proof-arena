import ZkFormal.NearV3.Candidates.HorizontalAssembly
import ZkFormal.NearV3.Candidates.HorizontalTrafficCore
namespace ZkFormal.NearV3.Candidates.HorizontalTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near HorizontalTables HorizontalTrace HorizontalJoin HorizontalAssembly

theorem sum_add {α : Type} (xs : List α) (f g : α→Nat) :
    (xs.map (fun x=>f x+g x)).sum=(xs.map f).sum+(xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]; omega

theorem count_append (xs ys : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (bus : Nat) (send : Bool) (msg : List Fp) :
    tableBusCount (xs++ys) tr t pub bus send msg=
      tableBusCount xs tr t pub bus send msg+tableBusCount ys tr t pub bus send msg := by
  simp only [table_sum,rowCount,List.map_append,List.sum_append,sum_add]

theorem count_map (f : Expr→Expr) (xs : List Interaction) (a b : Trace Fp)
    (t : Nat) (pub : List Fp) (bus : Nat) (send : Bool) (msg : List Fp)
    (hl : a.log t=b.log t)
    (h : ∀r,∀i∈xs,∀e∈i.exprs,(f e).eval a t r pub=e.eval b t r pub) :
    tableBusCount (xs.map (mapI f)) a t pub bus send msg=tableBusCount xs b t pub bus send msg := by
  simp only [table_sum,Trace.height,hl]
  congr 1
  apply List.map_congr_left
  intro r hr
  exact row_map f xs a b t r pub bus send msg (h r)

theorem pair_count (A B : Air.Table) (a b : Trace Fp) (t : Nat) (pub : List Fp)
    (bus : Nat) (send : Bool) (msg : List Fp) (hl : a.log t=b.log t)
    (hcols : ∀e∈A.exprs,e.colBound≤A.width) :
    tableBusCount (pair A B).interactions (join A.width a b) t pub bus send msg=
      tableBusCount A.interactions a t pub bus send msg+
      tableBusCount B.interactions b t pub bus send msg := by
  rw [show (pair A B).interactions=A.interactions++(shifted A.width B).interactions from rfl,
    count_append]
  have left := count_map id A.interactions (join A.width a b) a t pub bus send msg rfl
    (by
      intro r i hi e he
      exact join_left_eval a b t r A.width pub e
        (hcols e (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i,hi,he⟩))))
  have right := count_map (expression A.width) B.interactions (join A.width a b) b
    t pub bus send msg hl (by intro r i hi e he; exact join_right_eval a b t r A.width pub hl e)
  have hmap : mapI (expression A.width)=interaction A.width := rfl
  simpa only [hmap,show mapI id=id from funext mapI_id,List.map_id,shifted,mapI,interaction] using (congrArg (fun n=>n+tableBusCount (B.interactions.map (mapI (expression A.width))) (join A.width a b) t pub bus send msg) left).trans (congrArg (fun n=>tableBusCount A.interactions a t pub bus send msg+n) right)

/-- Exact per-bus, per-direction, per-message conservation under full-list fusion. -/
theorem trace_count (clock : Nat→Nat) (xs : List (Air.Table × Trace Fp))
    (t : Nat) (pub : List Fp) (bus : Nat) (send : Bool) (msg : List Fp)
    (hclock : ∀ x∈xs,x.2.log t=clock t)
    (hcap : ∀ x∈xs,x.1.maxLog≤22)
    (hcols : ∀ x∈xs,∀e∈x.1.exprs,e.colBound≤x.1.width) :
    tableBusCount (fuse (xs.map Prod.fst)).interactions (trace clock xs) t pub bus send msg=
      (xs.map (fun x=>tableBusCount x.1.interactions x.2 t pub bus send msg)).sum := by
  induction xs with
  | nil =>
    simp only [List.map_nil,fuse,layout,List.flatMap_nil,table_sum,rowCount,List.sum_nil]
    have hz : ∀ rs : List Nat, (rs.map (fun _=>0)).sum=0 := by
      intro rs
      induction rs <;> simp_all
    exact hz _
  | cons x xs ih =>
    rw [List.map_cons,fuse_cons _ _ (hcap x (by simp))]
    change tableBusCount (pair x.1 (fuse (xs.map Prod.fst))).interactions
      (join x.1.width x.2 (trace clock xs)) t pub bus send msg=_
    rw [pair_count _ _ _ _ _ _ _ _ _
      (by rw [hclock x (by simp),trace_log clock xs t (by intro y hy; exact hclock y (by simp [hy]))])
      (hcols x (by simp))]
    rw [ih (by intro y hy; exact hclock y (by simp [hy]))
      (by intro y hy; exact hcap y (by simp [hy]))
      (by intro y hy; exact hcols y (by simp [hy]))]
    rfl
end ZkFormal.NearV3.Candidates.HorizontalTraffic
