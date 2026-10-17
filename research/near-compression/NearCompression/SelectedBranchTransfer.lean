import NearCompression.SelectedHistoryExperiment
namespace NearCompression
open ArenaCore.Security

/-- The first-table bound's filtered earlier-history experiment is exactly
the corresponding branch of the common two-table continuation. -/
theorem first_selected_branch_count {A P Q R : Type}
    (earlier : List A) (first : List P) (second : List Q) (later : List R)
    (branch : A → Option Bool) (event : A → P → Q → R → Prop) :
    let chosen := earlier.filter (fun a=>@decide (branch a=some false) (Classical.propDecidable _))
    let continuation := first.flatMap (fun p=>second.flatMap (fun q=>later.map (fun r=>(p,q,r))))
    count (chosen.flatMap (fun a=>first.flatMap (fun p=>
      (second.flatMap (fun q=>later.map (fun r=>(q,r)))).map (fun qr=>(a,p,qr)))))
      (fun x=>event x.1 x.2.1 x.2.2.1 x.2.2.2)=
    count (earlier.flatMap (fun a=>continuation.map (fun r=>(a,r))))
      (fun x=>branch x.1=some false ∧ event x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  intro chosen continuation
  rw [first_selected_history_reindex]
  have h := selected_history_filter_count earlier continuation branch (some false)
    (fun a r=>event a r.1 r.2.1 r.2.2)
  simpa only [continuation,List.map_flatMap,List.map_map,Function.comp_def] using h

/-- The second-table bound filters bus histories before including first-local
prefixes; reindexing preserves both selection and the full failure event. -/
theorem second_selected_branch_count {A P Q R : Type}
    (earlier : List A) (first : List P) (second : List Q) (later : List R)
    (branch : A → Option Bool) (event : A → P → Q → R → Prop) :
    let chosen := earlier.filter (fun a=>@decide (branch a=some true) (Classical.propDecidable _))
    let continuation := first.flatMap (fun p=>second.flatMap (fun q=>later.map (fun r=>(p,q,r))))
    count ((chosen.flatMap (fun a=>first.map (fun p=>(a,p)))).flatMap (fun ap=>
      second.flatMap (fun q=>later.map (fun r=>(ap,q,r)))))
      (fun x=>event x.1.1 x.1.2 x.2.1 x.2.2)=
    count (earlier.flatMap (fun a=>continuation.map (fun r=>(a,r))))
      (fun x=>branch x.1=some true ∧ event x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  intro chosen continuation
  rw [second_selected_history_reindex]
  have h := selected_history_filter_count earlier continuation branch (some true)
    (fun a r=>event a r.1 r.2.1 r.2.2)
  simpa only [continuation,List.map_flatMap,List.map_map,Function.comp_def] using h

/-- Consume the actual differently nested first/second filtered experiments
and aggregate their retained failure counts only after converting to the
common branch experiment. This is a count transfer, not a source of numeric
local or PCS estimates. -/
theorem two_table_filtered_history_budget {A P Q R : Type}
    (earlier : List A) (first : List P) (second : List Q) (later : List R)
    (branch : A → Option Bool) (accept failure : A → P → Q → R → Prop)
    (scale busBudget firstBudget secondBudget jointBudget : Nat) :
    let chosen0 := earlier.filter (fun a=>@decide (branch a=some false) (Classical.propDecidable _))
    let chosen1 := earlier.filter (fun a=>@decide (branch a=some true) (Classical.propDecidable _))
    let continuation := first.flatMap (fun p=>second.flatMap (fun q=>later.map (fun r=>(p,q,r))))
    let experiment := earlier.flatMap (fun a=>continuation.map (fun r=>(a,r)))
    let firstExperiment := chosen0.flatMap (fun a=>first.flatMap (fun p=>
      (second.flatMap (fun q=>later.map (fun r=>(q,r)))).map (fun qr=>(a,p,qr))))
    let secondExperiment := (chosen1.flatMap (fun a=>first.map (fun p=>(a,p)))).flatMap (fun ap=>
      second.flatMap (fun q=>later.map (fun r=>(ap,q,r))))
    (count experiment (fun x=>branch x.1=none ∧ accept x.1 x.2.1 x.2.2.1 x.2.2.2)*scale≤busBudget+
      count experiment (fun x=>branch x.1=none ∧ (accept x.1 x.2.1 x.2.2.1 x.2.2.2 ∧ failure x.1 x.2.1 x.2.2.1 x.2.2.2))*scale) →
    (count firstExperiment (fun x=>accept x.1 x.2.1 x.2.2.1 x.2.2.2)*scale≤firstBudget+
      count firstExperiment (fun x=>accept x.1 x.2.1 x.2.2.1 x.2.2.2 ∧ failure x.1 x.2.1 x.2.2.1 x.2.2.2)*scale) →
    (count secondExperiment (fun x=>accept x.1.1 x.1.2 x.2.1 x.2.2)*scale≤secondBudget+
      count secondExperiment (fun x=>accept x.1.1 x.1.2 x.2.1 x.2.2 ∧ failure x.1.1 x.1.2 x.2.1 x.2.2)*scale) →
    (count experiment (fun x=>accept x.1 x.2.1 x.2.2.1 x.2.2.2 ∧ failure x.1 x.2.1 x.2.2.1 x.2.2.2)*scale≤jointBudget) →
    count experiment (fun x=>accept x.1 x.2.1 x.2.2.1 x.2.2.2)*scale≤
      busBudget+firstBudget+secondBudget+jointBudget := by
  intro chosen0 chosen1 continuation experiment firstExperiment secondExperiment good firstBound secondBound joint
  have f := first_selected_branch_count earlier first second later branch accept
  have fe := first_selected_branch_count earlier first second later branch (fun a p q r=>accept a p q r ∧ failure a p q r)
  have s := second_selected_branch_count earlier first second later branch accept
  have se := second_selected_branch_count earlier first second later branch (fun a p q r=>accept a p q r ∧ failure a p q r)
  dsimp only at f fe s se
  change count _ _*scale≤firstBudget+count _ _*scale at firstBound
  rw [f,fe] at firstBound
  change count _ _*scale≤secondBudget+count _ _*scale at secondBound
  rw [s,se] at secondBound
  apply history_three_branch_budget earlier continuation branch
    (fun a r=>accept a r.1 r.2.1 r.2.2) (fun a r=>failure a r.1 r.2.1 r.2.2)
    scale busBudget firstBudget secondBudget jointBudget _ joint
  intro tag
  cases tag with
  | none => exact good
  | some b => cases b
              · exact firstBound
              · exact secondBound

end NearCompression
