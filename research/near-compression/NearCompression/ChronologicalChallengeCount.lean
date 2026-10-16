import NearCompression.JointSourceAcceptance
namespace NearCompression
open ArenaCore.Security

/-- Concatenating a fixed earlier and suffix of independent ideal draws gives
exactly the original ordered sample list, including multiplicities. -/
theorem uniform_tuples_append {A : Type} (sample : List A) (a b : Nat) :
    uniformTuples sample (a+b)=(uniformTuples sample a).flatMap
      (fun x => (uniformTuples sample b).map (fun y => x++y)) := by
  induction a with
  | zero => simp [uniformTuples]
  | succ a ih =>
    rw [show a+1+b=(a+b)+1 by omega]
    simp only [uniformTuples,ih,List.flatMap_assoc,List.map_flatMap,List.flatMap_map,List.map_map]
    rfl

private theorem tuple_length {A : Type} (sample : List A) (n : Nat) :
    ∀ x∈uniformTuples sample n,x.length=n := by
  induction n with
  | zero => simp [uniformTuples]
  | succ n ih =>
    intro x hx
    simp only [uniformTuples,List.mem_flatMap,List.mem_map] at hx
    obtain ⟨a,ha,rest,hr,rfl⟩ := hx
    simp [ih rest hr]

/-- A uniform conditional suffix bound lifts to the joint-coordinate experiment.
The event and subsequent strategy may depend on the entire earlier. This is
an exact finite-count result, not a Fiat-Shamir sampling assertion. -/
theorem chronological_suffix_count {A B : Type} (sample : List A)
    (earlier suffix : Nat) (continuations : List B)
    (accept : List A → List A → B → Prop) (scale budget : Nat)
    (conditional : ∀ h∈uniformTuples sample earlier,
      count ((uniformTuples sample suffix).flatMap (fun z => continuations.map (fun b => (z,b))))
        (fun pair => accept h pair.1 pair.2)*scale≤budget) :
    count ((uniformTuples sample (earlier+suffix)).flatMap
      (fun z => continuations.map (fun b => (z,b))))
      (fun pair => accept (pair.1.take earlier) (pair.1.drop earlier) pair.2)*scale≤
      sample.length^earlier*budget := by
  classical
  rw [uniform_tuples_append]
  simp only [List.flatMap_assoc,List.flatMap_map]
  have fiber := finite_product_acceptance_budget (uniformTuples sample earlier)
    ((uniformTuples sample suffix).flatMap (fun z => continuations.map (fun b => (z,b))))
    (fun h pair => accept h pair.1 pair.2) (fun _ => False) scale budget
    (by intro h hh absent; exact conditional h hh)
  simp only [count,decide_false,List.countP_false,Function.const,Nat.zero_mul,Nat.zero_add,uniform_tuples_length] at fiber
  have equal : count ((uniformTuples sample earlier).flatMap (fun h =>
      (uniformTuples sample suffix).flatMap (fun z => continuations.map (fun b => (h++z,b)))))
      (fun pair => accept (pair.1.take earlier) (pair.1.drop earlier) pair.2)=
      count ((uniformTuples sample earlier).flatMap (fun h =>
        ((uniformTuples sample suffix).flatMap (fun z => continuations.map (fun b => (z,b)))).map
          (fun pair => (h,pair)))) (fun pair => accept pair.1 pair.2.1 pair.2.2) := by
    simp only [count,List.countP_flatMap,List.countP_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro h hh
    have length := tuple_length sample earlier h hh
    simp [←length]
  rw [equal]
  exact fiber

end NearCompression
