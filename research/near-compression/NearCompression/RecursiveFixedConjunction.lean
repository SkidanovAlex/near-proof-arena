import NearCompression.RecursiveResidualConjunction
import NearCompression.RecursiveOperandPacking
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- The only free live slots are even/odd (4,5) in each seven-word fold row. -/
def recursiveFreeOperand (rows slot : Nat) : Prop :=
  slot<7*rows ∧ (slot%7=4 ∨ slot%7=5)
instance (rows slot : Nat) : Decidable (recursiveFreeOperand rows slot) :=
  inferInstanceAs (Decidable (slot<7*rows ∧ (slot%7=4 ∨ slot%7=5)))

def recursiveFixedSlots (rows total : Nat) : List Nat :=
  (List.range total).filter (fun slot=>!decide (recursiveFreeOperand rows slot))

theorem recursive_fixed_slot_coverage (rows total slot : Nat) :
    slot∈recursiveFixedSlots rows total ↔ slot<total ∧ ¬recursiveFreeOperand rows slot := by
  simp [recursiveFixedSlots]

theorem recursive_free_operand_exact (rows slot : Nat) :
    recursiveFreeOperand rows slot ↔ ∃ row,row<rows ∧ (slot=7*row+4 ∨ slot=7*row+5) := by
  unfold recursiveFreeOperand
  constructor
  · intro h;refine ⟨slot/7,?_,?_⟩ <;> omega
  · rintro ⟨row,hr,hs⟩;omega

/-- Authenticated a,b,x,r,next are all covered by the canonical complement. -/
theorem recursive_fold_fixed_coverage (rows total row slot : Nat)
    (fits : 7*rows≤total) (hr : row<rows)
    (hs : slot=0 ∨ slot=1 ∨ slot=2 ∨ slot=3 ∨ slot=6) :
    7*row+slot∈recursiveFixedSlots rows total := by
  rw [recursive_fixed_slot_coverage]
  unfold recursiveFreeOperand
  omega

/-- Every source-batching operand is fixed, even if its index modulo7 is4/5. -/
theorem recursive_source_fixed_coverage (rows total slot : Nat)
    (lower : 7*rows≤slot) (upper : slot<total) :
    slot∈recursiveFixedSlots rows total := by
  rw [recursive_fixed_slot_coverage]
  unfold recursiveFreeOperand
  omega

def recursiveFixedResiduals (rows total : Nat) (values expected : Nat → K)
    (arithmetic : List K) : List K :=
  arithmetic ++ (recursiveFixedSlots rows total).map (fun i=>values i-expected i)

/-- Deterministic all-zero vector semantics, not an aggregate-acceptance premise. -/
theorem recursive_fixed_residuals_zero_iff (rows total : Nat) (values expected : Nat → K)
    (arithmetic : List K) :
    (∀ x∈recursiveFixedResiduals rows total values expected arithmetic,x=0) ↔
      (∀ x∈arithmetic,x=0) ∧
      (∀ i,i<total → ¬recursiveFreeOperand rows i → values i=expected i) := by
  constructor
  · intro hz
    constructor
    · intro x hx;exact hz x (List.mem_append_left _ hx)
    · intro i hi hf
      have hm := (recursive_fixed_slot_coverage rows total i).mpr ⟨hi,hf⟩
      have hv := hz (values i-expected i) (List.mem_append_right _ (List.mem_map.mpr ⟨i,hm,rfl⟩))
      grind
  · rintro ⟨ha,hf⟩ x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact ha x hx
    · obtain ⟨i,hi,he⟩ := List.mem_map.mp hx
      obtain ⟨bound,notfree⟩ := (recursive_fixed_slot_coverage rows total i).mp hi
      have hv := hf i bound notfree
      grind

def recursiveFoldResiduals (rows : Nat) (values : Nat → K) : List K :=
  (List.range rows).flatMap (fun row=>
    [2*values (7*row+4)-values (7*row)-values (7*row+1),
     2*values (7*row+2)*values (7*row+5)-values (7*row)+values (7*row+1),
     values (7*row+4)+values (7*row+3)*(values (7*row+5)-values (7*row+4))-values (7*row+6)])

/-- A source pair is (computed virtual source value, linked first-fold value).
Its native DAG evaluation/authentication is an explicit upstream boundary. -/
def recursiveSourceResiduals (pairs : List (K×K)) : List K := pairs.map (fun p=>p.1-p.2)

/-- All fold equations and all source links follow from the concrete residual
vector. No division is needed; the separate domain certificate supplies x≠0. -/
theorem recursive_arithmetic_zero_relations (rows : Nat) (values : Nat → K)
    (pairs : List (K×K))
    (zero : ∀ x∈recursiveFoldResiduals rows values++recursiveSourceResiduals pairs,x=0) :
    (∀ row,row<rows →
      2*values (7*row+4)=values (7*row)+values (7*row+1) ∧
      2*values (7*row+2)*values (7*row+5)=values (7*row)-values (7*row+1) ∧
      values (7*row+4)+values (7*row+3)*(values (7*row+5)-values (7*row+4))=values (7*row+6)) ∧
    (∀ pair∈pairs,pair.1=pair.2) := by
  constructor
  · intro row hr
    have hz : ∀ x∈[2*values (7*row+4)-values (7*row)-values (7*row+1),
        2*values (7*row+2)*values (7*row+5)-values (7*row)+values (7*row+1),
        values (7*row+4)+values (7*row+3)*(values (7*row+5)-values (7*row+4))-values (7*row+6)],x=0 := by
      intro x hx
      apply zero
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨row,List.mem_range.mpr hr,hx⟩
    have h0 := hz (2*values (7*row+4)-values (7*row)-values (7*row+1)) (by simp)
    have h1 := hz (2*values (7*row+2)*values (7*row+5)-values (7*row)+values (7*row+1)) (by simp)
    have h2 := hz (values (7*row+4)+values (7*row+3)*(values (7*row+5)-values (7*row+4))-values (7*row+6)) (by simp)
    grind
  · intro pair hp
    have hz := zero (pair.1-pair.2) (List.mem_append_right _ (List.mem_map.mpr ⟨pair,hp,rfl⟩))
    grind

/-- A bad fixed slot supplies an actual nonzero output index in the appended
vector. The vector and expected operands are fixed BEFORE the sampled point. -/
theorem recursive_bad_fixed_escape_count (n rows total slot : Nat)
    (values expected : Nat → K) (arithmetic : List K)
    (fits : (recursiveFixedResiduals rows total values expected arithmetic).length≤2^(n+1))
    (valid : slot<total) (fixed : ¬recursiveFreeOperand rows slot)
    (wrong : values slot≠expected slot) (sample : List K) (distinct : sample.Nodup) :
    count (packedGrid sample (n+1)) (fun point=>
      recursiveResidualEval (n+1) (recursiveFixedResiduals rows total values expected arithmetic) point=0)
      ≤(n+1)*sample.length^n := by
  have member : values slot-expected slot∈recursiveFixedResiduals rows total values expected arithmetic :=
    List.mem_append_right _ (List.mem_map.mpr ⟨slot,(recursive_fixed_slot_coverage rows total slot).mpr ⟨valid,fixed⟩,rfl⟩)
  obtain ⟨index,hi,he⟩ := List.getElem_of_mem member
  apply recursive_residual_false_zero_count n _ fits index hi _ sample distinct
  rw [he]
  grind


private theorem fold_residual_length (rows : Nat) (values : Nat → K) :
    (recursiveFoldResiduals rows values).length=3*rows := by
  have h (indices : List Nat) :
      (indices.flatMap (fun row=>
        [2*values (7*row+4)-values (7*row)-values (7*row+1),
         2*values (7*row+2)*values (7*row+5)-values (7*row)+values (7*row+1),
         values (7*row+4)+values (7*row+3)*(values (7*row+5)-values (7*row+4))-values (7*row+6)])).length=3*indices.length := by
    induction indices with
    | nil => rfl
    | cons i indices ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_cons,List.length_nil,ih]
      omega
  simpa only [recursiveFoldResiduals,List.length_range] using h (List.range rows)

/-- A conservative exact-derived size bound needs no trusted certificate count. -/
theorem recursive_fixed_residual_length_bound (rows total : Nat)
    (values expected : Nat → K) (pairs : List (K×K)) :
    (recursiveFixedResiduals rows total values expected
      (recursiveFoldResiduals rows values++recursiveSourceResiduals pairs)).length≤
        3*rows+pairs.length+total := by
  have h := List.length_filter_le (fun slot=>!decide (recursiveFreeOperand rows slot)) (List.range total)
  simp only [List.length_range] at h
  simp only [recursiveFixedResiduals,List.length_append,List.length_map,
    recursiveSourceResiduals,fold_residual_length,recursiveFixedSlots]
  omega

/-- Runtime shape:256 seven-slot fold rows,32 source links,12144 live inputs.
Every malformed fixed operand has at most14*|S|^13 zero-aggregation points.
This counts ideal independent coordinate challenges, not accepted FS proofs. -/
theorem recursive_single_root_fixed_escape_count (slot : Nat)
    (values expected : Nat → K) (pairs : List (K×K)) (pairCount : pairs.length=32)
    (valid : slot<12144) (fixed : ¬recursiveFreeOperand 256 slot)
    (wrong : values slot≠expected slot) (sample : List K) (distinct : sample.Nodup) :
    count (packedGrid sample 14) (fun point=>recursiveResidualEval 14
      (recursiveFixedResiduals 256 12144 values expected
        (recursiveFoldResiduals 256 values++recursiveSourceResiduals pairs)) point=0)
      ≤14*sample.length^13 := by
  apply recursive_bad_fixed_escape_count 13 256 12144 slot values expected _ _ valid fixed wrong sample distinct
  have h := recursive_fixed_residual_length_bound 256 12144 values expected pairs
  rw [pairCount] at h
  omega

/-- One vector supplies both the fixed operands and every arithmetic relation.
Only this all-zero-vector implication is deterministic; a sampled aggregate
uses the preceding counting theorem. PCS binding to this vector remains an
external cryptographic obligation; RecursiveOperandPacking proves its exact
terminal functional representation, not authentication. -/
theorem recursive_single_root_zero_semantics (rows total : Nat)
    (values expected : Nat → K) (pairs : List (K×K))
    (zero : ∀ x∈recursiveFixedResiduals rows total values expected
      (recursiveFoldResiduals rows values++recursiveSourceResiduals pairs),x=0) :
    (∀ i,i<total → ¬recursiveFreeOperand rows i → values i=expected i) ∧
    (∀ row,row<rows →
      2*values (7*row+4)=values (7*row)+values (7*row+1) ∧
      2*values (7*row+2)*values (7*row+5)=values (7*row)-values (7*row+1) ∧
      values (7*row+4)+values (7*row+3)*(values (7*row+5)-values (7*row+4))=values (7*row+6)) ∧
    (∀ pair∈pairs,pair.1=pair.2) := by
  obtain ⟨arithmetic,fixed⟩ := (recursive_fixed_residuals_zero_iff rows total values expected _).mp zero
  exact ⟨fixed,recursive_arithmetic_zero_relations rows values pairs arithmetic⟩


/-- Source arithmetic is evaluated on the SAME operand vector. The source
program and operands are fixed before the output point; there is deliberately
no output-point argument here. Instantiating this function with the Python
emitted source DAG still needs its execution/certificate refinement. -/
def recursiveSingleRootResiduals (rows total : Nat) (values expected : Nat → K)
    (source : (Nat → K) → List (K×K)) : List K :=
  recursiveFixedResiduals rows total values expected
    (recursiveFoldResiduals rows values++recursiveSourceResiduals (source values))

/-- Same-vector version for the actual source-evaluator interface. Together
with recursive_operand_branches_functional it fixes the deterministic data
that GKR/PCS must bind; neither theorem asserts cryptographic binding. -/
theorem recursive_single_root_same_vector_escape_count (slot : Nat)
    (values expected : Nat → K) (source : (Nat → K) → List (K×K))
    (pairCount : (source values).length=32)
    (valid : slot<12144) (fixed : ¬recursiveFreeOperand 256 slot)
    (wrong : values slot≠expected slot) (sample : List K) (distinct : sample.Nodup) :
    count (packedGrid sample 14) (fun point=>recursiveResidualEval 14
      (recursiveSingleRootResiduals 256 12144 values expected source) point=0)
      ≤14*sample.length^13 :=
  recursive_single_root_fixed_escape_count slot values expected (source values)
    pairCount valid fixed wrong sample distinct

end NearCompression
