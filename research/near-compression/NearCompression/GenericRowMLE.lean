import ZkFormal.Air.Basic

/-! Generic multilinear row interpolation with little-endian Boolean indices.
The cyclic next-row operation is a permutation of the evaluation table, not
addition of one to an off-cube field challenge. -/
namespace NearCompression
open Lean.Grind ZkFormal.Air

section Ring
variable {K : Type} [CommRing K]

def genericRowMLE : Nat → (Nat → K) → (Nat → K) → K
  | 0,values,_ => values 0
  | n+1,values,point =>
      (1-point 0)*genericRowMLE n (fun i => values (2*i)) (fun i => point (i+1)) +
      point 0*genericRowMLE n (fun i => values (2*i+1)) (fun i => point (i+1))

def genericRowBitIndex : Nat → (Nat → Bool) → Nat
  | 0,_ => 0
  | n+1,bits => (if bits 0 then 1 else 0)+2*genericRowBitIndex n (fun i => bits (i+1))

def genericRowBooleanPoint (bits : Nat → Bool) (i : Nat) : K := if bits i then 1 else 0

theorem generic_row_bit_index_bound (n : Nat) (bits : Nat → Bool) :
    genericRowBitIndex n bits<2^n := by
  induction n generalizing bits with
  | zero => change 0<1; decide
  | succ n ih =>
    have bound := ih (fun i => bits (i+1))
    simp only [genericRowBitIndex,Nat.pow_succ]
    split <;> omega

theorem generic_row_mle_boolean (n : Nat) (values : Nat → K) (bits : Nat → Bool) :
    genericRowMLE n values (genericRowBooleanPoint bits)=values (genericRowBitIndex n bits) := by
  induction n generalizing values bits with
  | zero => rfl
  | succ n ih =>
    simp only [genericRowMLE,genericRowBitIndex]
    change (1-genericRowBooleanPoint bits 0)*
      genericRowMLE n (fun i => values (2*i)) (genericRowBooleanPoint (fun i => bits (i+1))) +
      genericRowBooleanPoint bits 0*
      genericRowMLE n (fun i => values (2*i+1)) (genericRowBooleanPoint (fun i => bits (i+1)))=_
    rw [ih,ih]
    unfold genericRowBooleanPoint
    split
    · simp only [Nat.add_comm 1]
      grind
    · simp only [Nat.zero_add]
      grind

theorem generic_row_mle_congr (n : Nat) (values other : Nat → K) (point : Nat → K)
    (same : ∀ i,i<2^n → values i=other i) :
    genericRowMLE n values point=genericRowMLE n other point := by
  induction n generalizing values other point with
  | zero => exact same 0 (by decide)
  | succ n ih =>
    have even := ih (fun i => values (2*i)) (fun i => other (2*i)) (fun i => point (i+1)) (by
      intro i hi
      apply same
      rw [Nat.pow_succ]
      omega)
    have odd := ih (fun i => values (2*i+1)) (fun i => other (2*i+1)) (fun i => point (i+1)) (by
      intro i hi
      apply same
      rw [Nat.pow_succ]
      omega)
    simp only [genericRowMLE,even,odd]

theorem generic_row_mle_zero (n : Nat) (point : Nat → K) :
    genericRowMLE n (fun _ => 0) point=0 := by
  induction n generalizing point with
  | zero => rfl
  | succ n ih => simp only [genericRowMLE,ih]; grind

theorem generic_row_mle_add (n : Nat) (a b point : Nat → K) :
    genericRowMLE n (fun i => a i+b i) point=genericRowMLE n a point+genericRowMLE n b point := by
  induction n generalizing a b point with
  | zero => rfl
  | succ n ih => simp only [genericRowMLE,ih]; grind

theorem generic_row_mle_scale (n : Nat) (scalar : K) (values point : Nat → K) :
    genericRowMLE n (fun i => scalar*values i) point=scalar*genericRowMLE n values point := by
  induction n generalizing values point with
  | zero => rfl
  | succ n ih => simp only [genericRowMLE,ih]; grind

/-- The next-row oracle is the MLE of the cyclically permuted source table. -/
def genericRowNextMLE (n : Nat) (values point : Nat → K) : K :=
  genericRowMLE n (fun i => values ((i+1)%(2^n))) point

theorem generic_row_next_mle_boolean (n : Nat) (values : Nat → K) (bits : Nat → Bool) :
    genericRowNextMLE n values (genericRowBooleanPoint bits)=
      values ((genericRowBitIndex n bits+1)%(2^n)) :=
  generic_row_mle_boolean n _ bits

/-- Exact agreement with the existing AIR cyclic next-row semantics. -/
theorem generic_row_next_mle_air (tr : Trace K) (t col : Nat) (pub : List K) (bits : Nat → Bool) :
    genericRowNextMLE (tr.log t) (fun r => tr.cell t r col) (genericRowBooleanPoint bits)=
      (Expr.col col true).eval tr t (genericRowBitIndex (tr.log t) bits) pub := by
  rw [generic_row_next_mle_boolean]
  rfl

/-- On nonfinal Boolean rows, cyclic access is ordinary next-row access. -/
theorem generic_row_next_mle_nonfinal (n : Nat) (values : Nat → K) (bits : Nat → Bool)
    (next : genericRowBitIndex n bits+1<2^n) :
    genericRowNextMLE n values (genericRowBooleanPoint bits)=values (genericRowBitIndex n bits+1) := by
  rw [generic_row_next_mle_boolean,Nat.mod_eq_of_lt next]

/-- The final Boolean row wraps to source row zero, as AIR rowEnv specifies. -/
theorem generic_row_next_mle_final (n : Nat) (values : Nat → K) (bits : Nat → Bool)
    (last : genericRowBitIndex n bits+1=2^n) :
    genericRowNextMLE n values (genericRowBooleanPoint bits)=values 0 := by
  rw [generic_row_next_mle_boolean,last,Nat.mod_self]

end Ring
end NearCompression
