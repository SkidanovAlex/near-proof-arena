import NearCompression.GlobalChainGeometry
import NearCompression.WeightedConsistencyTransfer
import NearCompression.FiniteRSUniqueDecoding

/-! Exact finite uniform query counts for transcript-indexed modulo chains.
Checks are arbitrary fixed predicates, instantiated with verifier fold checks.
The recursive weights count surviving initial query seeds, without candidates. -/
namespace NearCompression
open ArenaCore.Security

def globalChainPass (sizes : Nat → Nat) (check : Nat → Nat → Prop) : Nat → Nat → Prop
  | 0,_ => True
  | i+1,s => globalChainPass sizes check i s ∧ check i (s%sizes (i+1))

noncomputable def globalChainWeight (seeds : List Nat) (sizes : Nat → Nat)
    (check : Nat → Nat → Prop) : Nat → Nat → Nat := by
  classical
  exact fun i => match i with
    | 0 => fun y => count seeds (fun s => s%sizes 0=y)
    | i+1 => fun y => if check i y then
        globalChainWeight seeds sizes check i y+
          globalChainWeight seeds sizes check i (y+sizes (i+1)) else 0

theorem global_chain_fiber_split (s N y : Nat) (positive : 0<N) (bound : y<N) :
    s%N=y ↔ s%(2*N)=y ∨ s%(2*N)=y+N := by
  have h := global_chain_pair_indices s N positive
  have b := Nat.mod_lt s (show 0<2*N by omega)
  constructor
  · intro eq
    have q := h.2.1
    have small : ∀ k : Nat,k<2 → k=0 ∨ k=1 := by intro k hk; omega
    have split := small _ q
    rcases split with z|o
    · left; rw [z,eq] at h; omega
    · right; rw [o,eq] at h; omega
  · intro eq
    rcases eq with z|o
    · rw [z,Nat.mod_eq_of_lt bound] at h; exact h.1.symm
    · have mod : (y+N)%N=y := by simp [Nat.mod_eq_of_lt bound]
      rw [o,mod] at h
      exact h.1.symm

private theorem count_split_fiber (seeds : List Nat) (event : Nat → Prop)
    (N y : Nat) (positive : 0<N) (bound : y<N) :
    count seeds (fun s => event s ∧ s%N=y)=
      count seeds (fun s => event s ∧ s%(2*N)=y)+
      count seeds (fun s => event s ∧ s%(2*N)=y+N) := by
  classical
  induction seeds with
  | nil => simp [count]
  | cons s ss ih =>
    have split := global_chain_fiber_split s N y positive bound
    simp only [count,List.countP_cons] at ih ⊢
    by_cases he : event s <;> by_cases hl : s%(2*N)=y <;>
      by_cases hr : s%(2*N)=y+N <;> by_cases hf : s%N=y <;> simp_all <;> omega

theorem global_chain_weight_exact (seeds : List Nat) (sizes : Nat → Nat)
    (check : Nat → Nat → Prop) (stage : Nat)
    (positive : ∀ j≤stage,0<sizes j)
    (halves : ∀ j<stage,sizes j=2*sizes (j+1)) (y : Nat) (bound : y<sizes stage) :
    globalChainWeight seeds sizes check stage y=
      count seeds (fun s => globalChainPass sizes check stage s ∧ s%sizes stage=y) := by
  classical
  induction stage generalizing y with
  | zero => simp [globalChainWeight,globalChainPass]
  | succ i ih =>
    have size := halves i (by omega)
    have pos := positive (i+1) (by omega)
    have left := ih (fun j hj => positive j (by omega))
      (fun j hj => halves j (by omega)) y (by omega)
    have right := ih (fun j hj => positive j (by omega))
      (fun j hj => halves j (by omega)) (y+sizes (i+1)) (by omega)
    have split := count_split_fiber seeds (globalChainPass sizes check i)
      (sizes (i+1)) y pos bound
    rw [← size] at split
    simp only [globalChainWeight]
    by_cases gate : check i y
    · simp only [gate,ite_true]
      rw [left,right,←split]
      apply congrArg (count seeds)
      funext s
      apply propext
      simp only [globalChainPass]
      constructor
      · intro h; exact ⟨⟨h.1,h.2 ▸ gate⟩,h.2⟩
      · intro h; exact ⟨h.1.1,h.2⟩
    · simp only [gate,ite_false]
      have pred : (fun s => globalChainPass sizes check (i+1) s ∧ s%sizes (i+1)=y)=
          (fun _ => False) := by
        funext s; apply propext
        simp only [globalChainPass]
        constructor
        · intro h; exact gate (h.2 ▸ h.1.2)
        · intro h; exact False.elim h
      rw [pred]
      simp [count]

private theorem count_fibers (seeds : List Nat) (event : Nat → Prop) (projection : Nat → Nat)
    (N : Nat) :
    ((List.range N).map (fun y => count seeds (fun s => event s ∧ projection s=y))).sum=
      count seeds (fun s => event s ∧ projection s<N) := by
  classical
  induction N with
  | zero => simp [count]
  | succ N ih =>
    simp only [List.range_succ,List.map_append,List.sum_append,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,Nat.add_zero,ih]
    clear ih
    induction seeds with
    | nil => simp [count]
    | cons s ss hs =>
      simp only [count,List.countP_cons] at hs ⊢
      by_cases he : event s <;> by_cases hl : projection s<N <;>
        by_cases hq : projection s=N <;> by_cases hn : projection s<N+1 <;>
        simp_all <;> (try split) <;> (try split) <;> (try simp_all) <;> omega

/-- Total recursively computed mass is EXACTLY the number of accepted global
query seeds. Uniform sampling from a duplicate-free seed list therefore has
acceptance probability mass / seeds.length (no probabilistic axiom needed). -/
theorem global_chain_total_mass (seeds : List Nat) (sizes : Nat → Nat)
    (check : Nat → Nat → Prop) (stage : Nat)
    (positive : ∀ j≤stage,0<sizes j)
    (halves : ∀ j<stage,sizes j=2*sizes (j+1)) :
    ((List.range (sizes stage)).map (globalChainWeight seeds sizes check stage)).sum=
      count seeds (globalChainPass sizes check stage) := by
  have lists : (List.range (sizes stage)).map (globalChainWeight seeds sizes check stage)=
      (List.range (sizes stage)).map (fun y =>
        count seeds (fun s => globalChainPass sizes check stage s ∧ s%sizes stage=y)) := by
    apply List.map_congr_left
    intro y hy
    exact global_chain_weight_exact seeds sizes check stage positive halves y (List.mem_range.mp hy)
  rw [lists,count_fibers]
  apply congrArg (count seeds)
  funext s
  apply propext
  exact and_iff_left (Nat.mod_lt s (positive stage (by omega)))

/-- Exact scalar fold check on canonical source pair y,y+Nchild. The next
oracle is indexed on the full child domain; its pair index/side are the
implementation's y mod(Nchild/2) and y/(Nchild/2). -/
def globalRSChainCheck {K : Type} [Lean.Grind.Field K] (sizes : Nat → Nat)
    (roots challenges : Nat → K) (oracles : Nat → Nat → K) (i y : Nat) : Prop :=
  let eo := rsPairDecode (roots i ^ y) (oracles i y,oracles i (y+sizes (i+1)))
  (1-challenges i)*eo.1+challenges i*eo.2=oracles (i+1) y

/-- Finite uniform numerator for the actual sequence of scalar RS pair checks.
For seeds=range N0 the probability is exactly this mass divided by N0.
Merkle binding and independent uniform challenge generation are external. -/
theorem global_rs_chain_query_count {K : Type} [Lean.Grind.Field K]
    (N0 : Nat) (sizes : Nat → Nat) (roots challenges : Nat → K)
    (oracles : Nat → Nat → K) (stage : Nat)
    (positive : ∀ j≤stage,0<sizes j)
    (halves : ∀ j<stage,sizes j=2*sizes (j+1)) :
    ((List.range (sizes stage)).map
      (globalChainWeight (List.range N0) sizes
        (globalRSChainCheck sizes roots challenges oracles) stage)).sum=
      count (List.range N0)
        (globalChainPass sizes (globalRSChainCheck sizes roots challenges oracles) stage) :=
  global_chain_total_mass _ _ _ _ positive halves

end NearCompression
