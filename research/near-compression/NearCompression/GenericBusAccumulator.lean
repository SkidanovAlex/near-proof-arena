import ZkFormal.Algebra.PolyLemmas

/-! Division-free running products, generic over a commutative ring. This
generalizes the recurrence underlying ZkFormal.Udr.Np.Msg4.running_prod.
Zero factors are allowed. Matching products is not, by itself, exact bus
multiset balance: fingerprint and integer-multiplicity arguments remain separate. -/
namespace NearCompression

variable {K : Type} [Lean.Grind.CommRing K]

def genericBusPrefix (factor : Nat → K) (n : Nat) : K :=
  ((List.range n).map factor).prod

theorem generic_bus_prod_append_single (xs : List K) (x : K) :
    (xs ++ [x]).prod = xs.prod * x := by
  induction xs with
  | nil => simp only [List.nil_append, List.prod_cons, List.prod_nil]; grind
  | cons a xs ih => simp only [List.cons_append, List.prod_cons, ih]; grind

theorem generic_bus_prefix_zero (factor : Nat → K) : genericBusPrefix factor 0 = 1 := rfl

theorem generic_bus_prefix_succ (factor : Nat → K) (n : Nat) :
    genericBusPrefix factor (n+1) = genericBusPrefix factor n * factor n := by
  simp only [genericBusPrefix, List.range_succ, List.map_append, List.map_singleton,
    generic_bus_prod_append_single]

/-- This is the concrete accumulator constraint system for one group. -/
structure GenericBusAccumulatorHolds (n : Nat) (factor accumulator : Nat → K) (fin : K) : Prop where
  positive : 1 ≤ n
  initial : accumulator 0 = 1
  step : ∀ i, i+1 < n → accumulator (i+1) = accumulator i * factor i
  terminal : accumulator (n-1) * factor (n-1) = fin

theorem generic_bus_accumulator_prefix (n : Nat) (factor accumulator : Nat → K) (fin : K)
    (h : GenericBusAccumulatorHolds n factor accumulator fin) :
    ∀ i, i < n → accumulator i = genericBusPrefix factor i := by
  intro i hi
  induction i with
  | zero => exact h.initial
  | succ i ih =>
    rw [h.step i hi, generic_bus_prefix_succ, ih (by omega)]

theorem generic_bus_accumulator_product (n : Nat) (factor accumulator : Nat → K) (fin : K)
    (h : GenericBusAccumulatorHolds n factor accumulator fin) :
    fin = ((List.range n).map factor).prod := by
  have hn := h.positive
  have hp := generic_bus_accumulator_prefix n factor accumulator fin h (n-1) (by omega)
  rw [← h.terminal, hp]
  change genericBusPrefix factor (n-1) * factor (n-1) = genericBusPrefix factor n
  rw [← generic_bus_prefix_succ, show n-1+1=n by omega]

/-- Honest prefix products satisfy every equation, without inverses or
nonzero-factor conditions. -/
theorem generic_bus_accumulator_complete (n : Nat) (positive : 1 ≤ n) (factor : Nat → K) :
    GenericBusAccumulatorHolds n factor (genericBusPrefix factor) (genericBusPrefix factor n) := by
  refine ⟨positive, generic_bus_prefix_zero factor, ?_, ?_⟩
  · intro i _; exact generic_bus_prefix_succ factor i
  · rw [← generic_bus_prefix_succ, show n-1+1=n by omega]

/-- The exact first/transition/last gated equations used by the main AIR
imply the recurrence contract. No division by a factor is performed. -/
theorem generic_bus_accumulator_of_gates (n : Nat) (positive : 1 ≤ n)
    (a an factor first transition last : Nat → K) (fin : K)
    (hfirst : ∀ r, r < n → first r = if r=0 then 1 else 0)
    (htransition : ∀ r, r < n → transition r = if r+1=n then 0 else 1)
    (hlast : ∀ r, r < n → last r = if r+1=n then 1 else 0)
    (hnext : ∀ r, r+1<n → an r = a (r+1))
    (initial : ∀ r, r<n → first r*(a r-1)=0)
    (step : ∀ r, r<n → transition r*(an r-a r*factor r)=0)
    (terminal : ∀ r, r<n → last r*(a r*factor r-fin)=0) :
    GenericBusAccumulatorHolds n factor a fin := by
  refine ⟨positive, ?_, ?_, ?_⟩
  · have h := initial 0 positive
    rw [hfirst 0 positive, ite_eq_left rfl] at h
    grind
  · intro i hi
    have h := step i (by omega)
    rw [htransition i (by omega), ite_eq_right (by omega), hnext i hi] at h
    grind
  · have h := terminal (n-1) (by omega)
    rw [hlast (n-1) (by omega), ite_eq_left (by omega)] at h
    grind

/-- Direct composition check: the concrete gated equations imply the final
product, through the independently proved recurrence interface. -/
theorem generic_bus_product_of_gates (n : Nat) (positive : 1 ≤ n)
    (a an factor first transition last : Nat → K) (fin : K)
    (hfirst : ∀ r, r < n → first r = if r=0 then 1 else 0)
    (htransition : ∀ r, r < n → transition r = if r+1=n then 0 else 1)
    (hlast : ∀ r, r < n → last r = if r+1=n then 1 else 0)
    (hnext : ∀ r, r+1<n → an r = a (r+1))
    (initial : ∀ r, r<n → first r*(a r-1)=0)
    (step : ∀ r, r<n → transition r*(an r-a r*factor r)=0)
    (terminal : ∀ r, r<n → last r*(a r*factor r-fin)=0) :
    fin = ((List.range n).map factor).prod :=
  generic_bus_accumulator_product n factor a fin
    (generic_bus_accumulator_of_gates n positive a an factor first transition last fin
      hfirst htransition hlast hnext initial step terminal)

end NearCompression
