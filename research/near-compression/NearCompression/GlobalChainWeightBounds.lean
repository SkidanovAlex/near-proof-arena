import NearCompression.GlobalChainMass
namespace NearCompression
open Lean.Grind ArenaCore.Security

private theorem initial_residue_weight_one (N y : Nat) (hy : y<N) :
    count (List.range N) (fun s => s%N=y)=1 := by
  classical
  have equal : count (List.range N) (fun s => s%N=y)=List.count y (List.range N) := by
    rw [List.count_eq_countP]
    unfold count
    apply List.countP_congr
    intro s hs
    have mod := Nat.mod_eq_of_lt (List.mem_range.mp hs)
    constructor
    · intro h
      have eq : s%N=y := @_root_.of_decide_eq_true _ (Classical.propDecidable _) h
      rw [mod] at eq
      exact beq_iff_eq.mpr eq
    · intro h
      have eq : s%N=y := by rw [mod]; exact beq_iff_eq.mp h
      exact @_root_.decide_eq_true _ (Classical.propDecidable _) eq
  rw [equal,List.Nodup.count List.nodup_range]
  simp [List.mem_range.mpr hy]

/-- Actual recursively gated transcript weights have cap 2^stage. Initial
uniform domain weights are proved to equal one, not supplied as a premise. -/
theorem global_chain_weight_cap (N0 : Nat) (sizes : Nat → Nat)
    (check : Nat → Nat → Prop) (stage : Nat) (initial : sizes 0=N0)
    (halves : ∀ j<stage,sizes j=2*sizes (j+1)) (y : Nat) (hy : y<sizes stage) :
    globalChainWeight (List.range N0) sizes check stage y≤2^stage := by
  classical
  induction stage generalizing y with
  | zero =>
    simp only [globalChainWeight,initial,Nat.pow_zero]
    rw [initial_residue_weight_one N0 y (by rw [initial] at hy; exact hy)]
    exact Nat.le_refl 1
  | succ i ih =>
    have step := halves i (by omega)
    have left := ih (fun j hj => halves j (by omega)) y (by omega)
    have right := ih (fun j hj => halves j (by omega)) (y+sizes (i+1)) (by omega)
    simp only [globalChainWeight,Nat.pow_succ]
    split <;> omega

private theorem map_sum_nat_add {A : Type} (xs : List A) (f g : A → Nat) :
    (xs.map (fun x => f x+g x)).sum=(xs.map f).sum+(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih]; omega

theorem range_pair_weight_sum (N : Nat) (weight : Nat → Nat) :
    ((List.range N).map (fun y => weight y+weight (y+N))).sum=
      ((List.range (2*N)).map weight).sum := by
  rw [map_sum_nat_add]
  have size : 2*N=N+N := by omega
  rw [size,List.range_add,List.map_append,List.sum_append,List.map_map]
  simp only [Function.comp_def,Nat.add_comm N]

/-- The projected measure before the next challenge has mass at most N0,
even after arbitrary malicious intermediate oracles and any prior gates. -/
theorem global_chain_projected_mass_bound (N0 : Nat) (sizes : Nat → Nat)
    (check : Nat → Nat → Prop) (stage : Nat)
    (positive : ∀ j≤stage,0<sizes j)
    (halves : ∀ j≤stage,sizes j=2*sizes (j+1)) :
    ((List.range (sizes (stage+1))).map (fun y =>
      globalChainWeight (List.range N0) sizes check stage y+
      globalChainWeight (List.range N0) sizes check stage (y+sizes (stage+1)))).sum≤N0 := by
  rw [range_pair_weight_sum,←halves stage (by omega)]
  rw [global_chain_total_mass (List.range N0) sizes check stage positive (fun j hj => halves j (by omega))]
  have bound : count (List.range N0) (globalChainPass sizes check stage)≤(List.range N0).length :=
    List.countP_le_length
  simpa only [List.length_range] using bound

theorem global_chain_projected_cap (N0 : Nat) (sizes : Nat → Nat)
    (check : Nat → Nat → Prop) (stage : Nat) (initial : sizes 0=N0)
    (halves : ∀ j≤stage,sizes j=2*sizes (j+1)) (y : Nat) (hy : y<sizes (stage+1)) :
    globalChainWeight (List.range N0) sizes check stage y+
      globalChainWeight (List.range N0) sizes check stage (y+sizes (stage+1))≤2^(stage+1) := by
  have step := halves stage (by omega)
  have left := global_chain_weight_cap N0 sizes check stage initial
    (fun j hj => halves j (by omega)) y (by omega)
  have right := global_chain_weight_cap N0 sizes check stage initial
    (fun j hj => halves j (by omega)) (y+sizes (stage+1)) (by omega)
  rw [Nat.pow_succ]
  omega

end NearCompression
