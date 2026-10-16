import ZkFormal.Algebra.PolyLemmas

/-! Borrow-automaton algebra for a cyclic-next opening reduction. Coordinates
are little endian. The final borrow is discarded. The theorem here identifies
the executable recurrence with an explicit Boolean sum; identifying the bit
transform with natural-number indexing modulo 2^n is a separate obligation. -/
namespace NearCompression

variable {K : Type} [Lean.Grind.CommRing K]

def shiftBitValue (b : Bool) : K := if b then 1 else 0

def shiftBitWeight (x : K) (b : Bool) : K := if b then x else 1 - x

def shiftEqCoordinate (r y : K) : K := (1-r)*(1-y)+r*y

/-- Output bit and outgoing borrow for subtraction of one borrow bit. -/
def shiftBorrowStep (borrow bit : Bool) : Bool × Bool :=
  (Bool.xor bit borrow, borrow && !bit)

/-- Exact forward arithmetic of shift_opening.py, accepting arbitrary state. -/
def shiftKernelDP : List (K × K) → K → K → K
  | [], nb, b => nb + b
  | (r,y)::rest, nb, b =>
    shiftKernelDP rest (nb*shiftEqCoordinate r y+b*y*(1-r)) (b*(1-y)*r)

/-- Explicit recursive sum over all Boolean assignments of the input bits.
Each branch contributes eq(y,inputBit)·eq(r,outputBit), then recurses on the
remaining coordinates with the actual Boolean borrow transition. -/
def shiftKernelBooleanSum : List (K × K) → Bool → K
  | [], _ => 1
  | (r,y)::rest, borrow =>
    shiftBitWeight y false * shiftBitWeight r (shiftBorrowStep borrow false).1 *
      shiftKernelBooleanSum rest (shiftBorrowStep borrow false).2 +
    shiftBitWeight y true * shiftBitWeight r (shiftBorrowStep borrow true).1 *
      shiftKernelBooleanSum rest (shiftBorrowStep borrow true).2

theorem shift_kernel_dp_linear_sum (coords : List (K × K)) (nb b : K) :
    shiftKernelDP coords nb b =
      nb * shiftKernelBooleanSum coords false + b * shiftKernelBooleanSum coords true := by
  induction coords generalizing nb b with
  | nil => simp only [shiftKernelDP, shiftKernelBooleanSum]; grind
  | cons p rest ih =>
    obtain ⟨r,y⟩ := p
    rw [shiftKernelDP, ih]
    simp only [shiftKernelBooleanSum, shiftBorrowStep, Bool.xor_false,
      Bool.xor_true, Bool.not_false, Bool.not_true, Bool.false_and,
      Bool.true_and, shiftBitWeight]
    unfold shiftEqCoordinate
    grind

theorem shift_kernel_dp_boolean_sum (coords : List (K × K)) :
    shiftKernelDP coords 0 1 = shiftKernelBooleanSum coords true := by
  rw [shift_kernel_dp_linear_sum]
  grind

/-- Explicit subtraction of an incoming borrow from a bit vector; overflow
is discarded by the empty-list case. -/
def shiftSubtractBits : Bool → List Bool → List Bool
  | _, [] => []
  | borrow, bit::rest =>
    (shiftBorrowStep borrow bit).1 :: shiftSubtractBits (shiftBorrowStep borrow bit).2 rest

def shiftEqBits : List K → List Bool → K
  | [], [] => 1
  | r::rs, bit::bs => shiftBitWeight r bit * shiftEqBits rs bs
  | _, _ => 0

/-- Finite Boolean-cube summation weighted by the multilinear basis at x.
Expanding this definition gives Σ_bits eq(x,bits) * f(bits). -/
def shiftWeightedCubeSum : List K → (List Bool → K) → K
  | [], f => f []
  | y::ys, f =>
    (1-y)*shiftWeightedCubeSum ys (fun bs => f (false::bs)) +
      y*shiftWeightedCubeSum ys (fun bs => f (true::bs))

theorem shift_weighted_cube_sum_scale (ys : List K) (c : K) (f : List Bool → K) :
    shiftWeightedCubeSum ys (fun bs => c*f bs) = c*shiftWeightedCubeSum ys f := by
  induction ys generalizing f with
  | nil => rfl
  | cons y ys ih =>
    simp only [shiftWeightedCubeSum, ih]
    grind

/-- The automaton computes the MLE of the explicit subtract-borrow bit
transform, for arbitrary field points, not just Boolean points. -/
theorem shift_kernel_sum_weighted (coords : List (K × K)) (borrow : Bool) :
    shiftKernelBooleanSum coords borrow =
      shiftWeightedCubeSum (coords.map Prod.snd) (fun bits =>
        shiftEqBits (coords.map Prod.fst) (shiftSubtractBits borrow bits)) := by
  induction coords generalizing borrow with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨r,y⟩ := p
    simp only [shiftKernelBooleanSum, List.map_cons, shiftWeightedCubeSum,
      shiftSubtractBits, shiftEqBits, shift_weighted_cube_sum_scale, ih]
    unfold shiftBitWeight
    grind

theorem shift_kernel_dp_weighted (coords : List (K × K)) :
    shiftKernelDP coords 0 1 =
      shiftWeightedCubeSum (coords.map Prod.snd) (fun bits =>
        shiftEqBits (coords.map Prod.fst) (shiftSubtractBits true bits)) := by
  rw [shift_kernel_dp_boolean_sum, shift_kernel_sum_weighted]

/-- At a Boolean point exactly its branch survives in the Boolean sum. -/
theorem shift_kernel_sum_boolean (coords : List (K × Bool)) (borrow : Bool) :
    shiftKernelBooleanSum (coords.map fun p => (p.1, shiftBitValue p.2)) borrow =
      shiftEqBits (coords.map Prod.fst) (shiftSubtractBits borrow (coords.map Prod.snd)) := by
  induction coords generalizing borrow with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨r,bit⟩ := p
    simp only [shiftBitValue] at ih
    cases borrow <;> cases bit <;>
      simp only [List.map_cons, shiftKernelBooleanSum, shiftSubtractBits,
        shiftBorrowStep, Bool.xor_false, Bool.xor_true, Bool.not_false,
        Bool.not_true, Bool.false_and, Bool.true_and, shiftBitValue,
        shiftBitWeight, shiftEqBits] <;>
      simp only [ih false, ih true] <;> grind

theorem shift_kernel_dp_boolean (coords : List (K × Bool)) :
    shiftKernelDP (coords.map fun p => (p.1, shiftBitValue p.2)) 0 1 =
      shiftEqBits (coords.map Prod.fst) (shiftSubtractBits true (coords.map Prod.snd)) := by
  rw [shift_kernel_dp_boolean_sum, shift_kernel_sum_boolean]

end NearCompression
