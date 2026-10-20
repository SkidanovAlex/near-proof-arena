import NearCompression.HistoryBranchBudget
namespace NearCompression
open ArenaCore.Security

/-- Restricting the earlier history list is exactly the corresponding branch
predicate in the full experiment; multiplicities are preserved. -/
theorem selected_history_filter_count {A R : Type} (earlier : List A) (later : List R)
    (branch : A → Option Bool) (tag : Option Bool) (event : A → R → Prop) :
    count ((earlier.filter (fun a=>@decide (branch a=tag) (Classical.propDecidable _))).flatMap
      (fun a=>later.map (fun r=>(a,r)))) (fun x=>event x.1 x.2)=
    count (earlier.flatMap (fun a=>later.map (fun r=>(a,r))))
      (fun x=>branch x.1=tag ∧ event x.1 x.2) := by
  classical
  induction earlier with
  | nil => simp [count]
  | cons a rest ih =>
    by_cases h : branch a=tag
    · simp [h,count_append,count_map,ih]
    · simp [h,count_append,count_map,ih,count_const]

/-- First-table future-prefix nesting is the same chronological experiment
as the common history/first/second/PCS nesting. -/
theorem first_selected_history_reindex {A P Q R : Type}
    (earlier : List A) (first : List P) (second : List Q) (later : List R)
    (event : A → P → Q → R → Prop) :
    count (earlier.flatMap (fun a=>first.flatMap (fun p=>
      (second.flatMap (fun q=>later.map (fun r=>(q,r)))).map (fun qr=>(a,p,qr)))))
      (fun x=>event x.1 x.2.1 x.2.2.1 x.2.2.2)=
    count (earlier.flatMap (fun a=>first.flatMap (fun p=>second.flatMap
      (fun q=>later.map (fun r=>(a,p,q,r))))))
      (fun x=>event x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  simp only [List.map_flatMap,List.map_map,Function.comp_def]

/-- Second-table earlier-prefix nesting preserves the same full event count,
without conditioning away first-table rowpoint randomness. -/
theorem second_selected_history_reindex {A P Q R : Type}
    (earlier : List A) (first : List P) (second : List Q) (later : List R)
    (event : A → P → Q → R → Prop) :
    count ((earlier.flatMap (fun a=>first.map (fun p=>(a,p)))).flatMap (fun ap=>
      second.flatMap (fun q=>later.map (fun r=>(ap,q,r)))))
      (fun x=>event x.1.1 x.1.2 x.2.1 x.2.2)=
    count (earlier.flatMap (fun a=>first.flatMap (fun p=>second.flatMap
      (fun q=>later.map (fun r=>(a,p,q,r))))))
      (fun x=>event x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  simp only [List.flatMap_assoc,List.flatMap_map,count,List.countP_flatMap,List.countP_map,Function.comp_def]

end NearCompression
