import NearCompression.GenericRowMLE
import NearCompression.InstructionSumcheckSoundness
import NearCompression.GenericPackedClaimAuthentication

/-! Counting over independent coordinates from a duplicate-free finite field
alphabet. No random-oracle, commitment, or sampling implementation claim. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def packedGrid (sample : List K) : Nat → List (List K)
  | 0 => [[]]
  | n+1 => (packedGrid sample n).flatMap (fun tail => sample.map (fun x => x::tail))

def packedGridBudget (m : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => m*packedGridBudget m n+m^n

omit [Field K] in
theorem packed_grid_length (sample : List K) (n : Nat) :
    (packedGrid sample n).length=sample.length^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [packedGrid,List.length_flatMap,List.length_map]
    have constant : ∀ xs : List (List K), (xs.map (fun _ => sample.length)).sum = xs.length*sample.length := by
      intro xs
      induction xs with
      | nil => simp
      | cons a xs hi => simp [hi,Nat.succ_mul,Nat.add_comm]
    rw [constant,ih,Nat.pow_succ]

theorem packed_grid_budget_closed (m n : Nat) :
    packedGridBudget m (n+1)=(n+1)*m^n := by
  induction n with
  | zero => simp [packedGridBudget]
  | succ n ih =>
    rw [packedGridBudget,ih,Nat.pow_succ]
    grind

private theorem count_nil_grid {A : Type} (event : A → Prop) :
    count [] event=0 := rfl

open Classical in
private theorem count_cons_grid {A : Type} (x : A) (xs : List A) (event : A → Prop) :
    count (x::xs) event=(if event x then 1 else 0)+count xs event := by
  classical
  simp only [count,List.countP_cons]
  split <;> simp_all [Nat.add_comm]

open Classical in
private theorem count_fibers_bound {A B : Type} (xs : List A) (fibers : A → List B)
    (event : B → Prop) (exceptional : A → Prop) (m : Nat)
    (bound : ∀ x, count (fibers x) event ≤ (if exceptional x then m else 0)+1) :
    count (xs.flatMap fibers) event ≤ m*count xs exceptional+xs.length := by
  classical
  induction xs with
  | nil => simp [count]
  | cons x xs ih =>
    have hx := bound x
    simp only [List.flatMap_cons,count,List.countP_append] at ih hx ⊢
    change _ ≤ m*count (x::xs) exceptional+(x::xs).length
    rw [count_cons_grid]
    simp only [List.length_cons]
    by_cases he : exceptional x
    · simp only [he,ite_true] at hx ⊢
      simp only [Nat.mul_add,Nat.mul_one]
      simp only [count] at *
      omega
    · simp only [he,ite_false,Nat.zero_add] at hx ⊢
      simp only [count] at *
      omega

private theorem affine_bad_roots (a b : K) (sample : List K) (distinct : sample.Nodup)
    (nonzero : a ≠ 0 ∨ b ≠ 0) :
    count sample (fun x => (1-x)*a+x*b=0) ≤ 1 := by
  let f : Poly K := Poly.C a+Poly.X*(Poly.C b-Poly.C a)
  have eval : ∀ x, f.eval x=(1-x)*a+x*b := by
    intro x
    simp only [f,Poly.eval_add,Poly.eval_mul,Poly.eval_sub,Poly.eval_C,Poly.eval_X]
    grind
  have nz : ¬ f.IsZero := by
    intro zero
    have h0 := Poly.eval_of_isZero zero (0:K)
    have h1 := Poly.eval_of_isZero zero (1:K)
    rw [eval] at h0 h1
    grind
  have deg : f.DegLt 2 := by
    apply Poly.degLt_add
    · exact (Poly.degLt_length _).mono (by change 1≤2; decide)
    · exact Poly.degLt_mul (Poly.degLt_length Poly.X)
        (Poly.degLt_sub (Poly.degLt_length (Poly.C b)) (Poly.degLt_length (Poly.C a)))
  have roots := PolyRoots.cardRootsLe_of polyEval polyDeg quotFacts isZeroEval
    K f 2 sample nz deg distinct
  simp only [eval] at roots
  omega

def packedGridEval (n : Nat) (values : Nat → K) (point : List K) : K :=
  genericRowMLE n values (fun i => point.getD i 0)

theorem packed_grid_eval_cons (n : Nat) (values : Nat → K) (x : K) (tail : List K) :
    packedGridEval (n+1) values (x::tail) =
      (1-x)*packedGridEval n (fun i => values (2*i)) tail+
      x*packedGridEval n (fun i => values (2*i+1)) tail := by
  simp only [packedGridEval,genericRowMLE,List.getD_cons_zero,List.getD_cons_succ]

/-- Multilinear Schwartz--Zippel by conditioning on independent coordinates.
The nonzero witness is an actual Boolean lane, not a chosen affine line. -/
theorem packed_grid_zero_bound (n : Nat) (values : Nat → K) (bits : Nat → Bool)
    (nonzero : values (genericRowBitIndex n bits) ≠ 0)
    (sample : List K) (distinct : sample.Nodup) :
    count (packedGrid sample n) (fun point => packedGridEval n values point=0) ≤
      packedGridBudget sample.length n := by
  classical
  induction n generalizing values bits with
  | zero =>
    simp only [genericRowBitIndex] at nonzero
    simp [packedGrid,packedGridEval,genericRowMLE,packedGridBudget,count,nonzero]
  | succ n ih =>
    let even : Nat → K := fun i => values (2*i)
    let odd : Nat → K := fun i => values (2*i+1)
    let chosen : Nat → K := if bits 0 then odd else even
    have chosenNonzero : chosen (genericRowBitIndex n (fun i => bits (i+1))) ≠ 0 := by
      simp only [genericRowBitIndex] at nonzero
      cases hbit : bits 0 <;> simp only [hbit,chosen,even,odd,ite_true,ite_false,
        Bool.false_eq_true,Nat.zero_add] at nonzero ⊢ <;> grind
    have tails := ih chosen (fun i => bits (i+1)) chosenNonzero
    let bad : List K → Prop := fun tail => packedGridEval n chosen tail=0
    have fibers : ∀ tail : List K,
        count (sample.map (fun x => x::tail))
          (fun point => packedGridEval (n+1) values point=0) ≤
          (if bad tail then sample.length else 0)+1 := by
      intro tail
      by_cases hb : bad tail
      · simp only [hb,ite_true]
        have trivial := count_le_length (sample.map (fun x => x::tail))
          (fun point => packedGridEval (n+1) values point=0)
        simp only [List.length_map] at trivial
        omega
      · simp only [hb,ite_false]
        have nz : packedGridEval n even tail ≠ 0 ∨ packedGridEval n odd tail ≠ 0 := by
          change packedGridEval n chosen tail ≠ 0 at hb
          cases hbit : bits 0 <;> simp only [chosen,hbit,ite_true,ite_false,Bool.false_eq_true] at hb
          · exact Or.inl hb
          · exact Or.inr hb
        have roots := affine_bad_roots (packedGridEval n even tail)
          (packedGridEval n odd tail) sample distinct nz
        simpa only [count,List.countP_map,Function.comp_def,packed_grid_eval_cons,even,odd,
          Nat.zero_add] using roots
    have total := count_fibers_bound (packedGrid sample n)
      (fun tail => sample.map (fun x => x::tail))
      (fun point => packedGridEval (n+1) values point=0) bad sample.length fibers
    rw [packed_grid_length] at total
    change _ ≤ packedGridBudget sample.length (n+1)
    rw [packedGridBudget]
    change count ((packedGrid sample n).flatMap _) _ ≤ _
    change count (packedGrid sample n) bad ≤ _ at tails
    exact Nat.le_trans total (Nat.add_le_add_right (Nat.mul_le_mul_left _ tails) _)

theorem packed_grid_zero_bound_closed (n : Nat) (values : Nat → K) (bits : Nat → Bool)
    (nonzero : values (genericRowBitIndex (n+1) bits) ≠ 0)
    (sample : List K) (distinct : sample.Nodup) :
    count (packedGrid sample (n+1)) (fun point => packedGridEval (n+1) values point=0) ≤
      (n+1)*sample.length^n := by
  have bound := packed_grid_zero_bound (n+1) values bits nonzero sample distinct
  rw [packed_grid_budget_closed] at bound
  exact bound

theorem packed_grid_eval_sub (n : Nat) (sent source : Nat → K) (point : List K) :
    packedGridEval n (fun i => sent i-source i) point =
      packedGridEval n sent point-packedGridEval n source point := by
  have diff : (fun i => sent i-source i)=(fun i => sent i+(-1)*source i) := by
    funext i
    grind
  simp only [packedGridEval,diff,generic_row_mle_add,generic_row_mle_scale]
  grind

/-- Direct authentication bound for two fixed claim vectors. The valid lane
is in the packed, zero-padded width 2^(n+1); no randomness depends on it. -/
theorem packed_claim_grid_bad_count (n lane : Nat) (sent source : Nat → K)
    (valid : lane < 2^(n+1)) (wrong : sent lane ≠ source lane)
    (sample : List K) (distinct : sample.Nodup) :
    count (packedGrid sample (n+1))
      (fun point => packedGridEval (n+1) sent point=packedGridEval (n+1) source point) ≤
      (n+1)*sample.length^n := by
  obtain ⟨bits,hbits⟩ := packed_claim_lane_bits (n+1) lane valid
  have nz : (sent (genericRowBitIndex (n+1) bits)-source (genericRowBitIndex (n+1) bits)) ≠ 0 := by
    rw [hbits]
    grind
  have bound := packed_grid_zero_bound_closed n (fun i => sent i-source i) bits nz sample distinct
  have subset : count (packedGrid sample (n+1))
      (fun point => packedGridEval (n+1) sent point=packedGridEval (n+1) source point) ≤
      count (packedGrid sample (n+1))
        (fun point => packedGridEval (n+1) (fun i => sent i-source i) point=0) := by
    apply count_mono
    intro point eq
    rw [packed_grid_eval_sub,eq]
    grind
  exact Nat.le_trans subset bound

/-- Counting form of probability at most (n+1)/|sample| for independent
uniform coordinates. Positivity excludes a vacuous empty alphabet. -/
theorem packed_claim_grid_probability_count (n lane : Nat) (sent source : Nat → K)
    (valid : lane < 2^(n+1)) (wrong : sent lane ≠ source lane)
    (sample : List K) (distinct : sample.Nodup) (positive : 0 < sample.length) :
    0 < sample.length ∧
    count (packedGrid sample (n+1))
      (fun point => packedGridEval (n+1) sent point=packedGridEval (n+1) source point) * sample.length ≤
      (n+1)*(packedGrid sample (n+1)).length := by
  refine ⟨positive, ?_⟩
  have bound := Nat.mul_le_mul_right sample.length
    (packed_claim_grid_bad_count n lane sent source valid wrong sample distinct)
  rw [packed_grid_length,Nat.pow_succ]
  simpa only [Nat.mul_assoc] using bound

end NearCompression
