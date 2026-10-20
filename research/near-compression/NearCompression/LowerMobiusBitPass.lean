import NearCompression.UpperZetaBitPass
import Init.Data.Nat.Bitwise.Lemmas

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Simultaneous semantics of a single bit pass. The implementation below
will be proved equal despite its sequential in-place writes. -/
def mobiusBitPass (bit : Nat) (values : Nat → K) (i : Nat) : K :=
  if i.testBit bit then values i-values (i ^^^ 2^bit) else values i

def mobiusBitRuns : Nat → Nat → (Nat → K) → Nat → K
  | _,0,values => values
  | bit,count+1,values => mobiusBitRuns (bit+1) count (mobiusBitPass bit values)

omit [Field K] in
private theorem pair_xor_bit (i b j : Nat) (small : b<2) :
    (2*i+b) ^^^ 2^(j+1)=2*(i ^^^ 2^j)+b := by
  have half : (2*i+b)/2=i := by omega
  have rem : (2*i+b)%2=b := by omega
  have powerHalf : 2^(j+1)/2=2^j := by rw [Nat.pow_succ,Nat.mul_div_cancel _ (by decide)]
  have powerRem : 2^(j+1)%2=0 := by simp [Nat.pow_succ]
  have div : ((2*i+b) ^^^ 2^(j+1))/2=i ^^^ 2^j := by rw [Nat.xor_div_two,half,powerHalf]
  have mod : ((2*i+b) ^^^ 2^(j+1))%2=b := by
    have h := Nat.xor_mod_two_pow (a:=2*i+b) (b:=2^(j+1)) (n:=1)
    simpa [rem,powerRem] using h
  have rebuild := Nat.mod_add_div ((2*i+b) ^^^ 2^(j+1)) 2
  rw [div,mod] at rebuild
  omega

private theorem bit_pass_pair (j i b : Nat) (values : Nat → K) (small : b<2) :
    mobiusBitPass (j+1) values (2*i+b)=mobiusBitPass j (fun k => values (2*k+b)) i := by
  have half : (2*i+b)/2=i := by omega
  simp only [mobiusBitPass,Nat.testBit_add_one,half,pair_xor_bit i b j small]

private theorem bit_runs_pair (start rounds i b : Nat) (values : Nat → K) (small : b<2) :
    mobiusBitRuns (start+1) rounds values (2*i+b)=
      mobiusBitRuns start rounds (fun k => values (2*k+b)) i := by
  induction rounds generalizing start values with
  | zero => rfl
  | succ rounds ih =>
    rw [mobiusBitRuns,ih,mobiusBitRuns]
    have same : (fun k => mobiusBitPass (start+1) values (2*k+b))=
        mobiusBitPass start (fun k => values (2*k+b)) := by
      funext k
      exact bit_pass_pair start k b values small
    rw [same]

private theorem first_bit_even (values : Nat → K) (i : Nat) :
    mobiusBitPass 0 values (2*i)=values (2*i) := by
  have hm : (2*i)%2=0 := by omega
  simp [mobiusBitPass,Nat.testBit_zero,hm]

private theorem first_bit_odd (values : Nat → K) (i : Nat) :
    mobiusBitPass 0 values (2*i+1)=values (2*i+1)-values (2*i) := by
  have hm : (2*i+1)%2=1 := by omega
  have target : (2*i+1) ^^^ 1=2*i := by
    apply Nat.eq_of_testBit_eq
    intro b
    cases b with
    | zero => simp [Nat.testBit_zero,hm,show (2*i)%2=0 by omega]
    | succ b => simp [Nat.testBit_add_one,Nat.xor_div_two,show (2*i+1)/2=i by omega,show (2*i)/2=i by omega]
  simp [mobiusBitPass,Nat.testBit_zero,hm,target]

/-- All passes occur in ascending bit order, exactly bit=1,2,4,... . -/
theorem bit_runs_lower_mobius (n : Nat) (values : Nat → K) (i : Nat) (bound : i<2^n) :
    mobiusBitRuns 0 n values i=mobiusCoefficients n values i := by
  induction n generalizing values i with
  | zero =>
    have hi : i=0 := by simpa using bound
    subst i
    rfl
  | succ n ih =>
    have half : i/2<2^n := by rw [Nat.pow_succ] at bound; omega
    have remainder : i%2<2 := Nat.mod_lt _ (by decide)
    have rebuild : 2*(i/2)+i%2=i := by have h := Nat.mod_add_div i 2; omega
    rw [mobiusBitRuns,←rebuild,bit_runs_pair 0 n _ _ _ remainder]
    rw [rebuild,mobiusCoefficients]
    by_cases even : i%2=0
    · rw [even,ite_eq_left rfl]
      have same : (fun k => mobiusBitPass 0 values (2*k+0))=(fun k => values (2*k)) := by
        funext k
        simpa using first_bit_even values k
      rw [same]
      exact ih _ _ half
    · have odd : i%2=1 := by omega
      rw [odd,ite_eq_right (by decide : ¬(1:Nat)=0)]
      rw [funext (first_bit_odd values)]
      exact ih _ _ half

/-- One actual in-place write. Reads use the current state, not a saved copy. -/
def mobiusWrite (bit : Nat) (values : Nat → K) (index : Nat) : Nat → K :=
  if index.testBit bit then
    fun i => if i=index then values index-values (index ^^^ 2^bit) else values i
  else values

def mobiusSequentialPass (bit : Nat) : List Nat → (Nat → K) → Nat → K
  | [],values => values
  | index::rest,values => mobiusSequentialPass bit rest (mobiusWrite bit values index)

/-- A set-bit destination reads a cleared-bit source, which this pass never writes. -/
theorem mobius_source_bit_clear (bit i : Nat) (set : i.testBit bit=true) :
    (i ^^^ 2^bit).testBit bit=false := by
  simp [Nat.testBit_xor,Nat.testBit_two_pow_self,set]

/-- Sequential current-state subtraction agrees with simultaneous semantics;
no source/nonalias assumption is supplied by the caller. -/
theorem sequential_mobius_pass_exact (bit : Nat) (indices : List Nat) (distinct : indices.Nodup)
    (values : Nat → K) (i : Nat) :
    mobiusSequentialPass bit indices values i=
      if i∈indices then mobiusBitPass bit values i else values i := by
  induction indices generalizing values with
  | nil => simp [mobiusSequentialPass]
  | cons index rest ih =>
    have absent : index∉rest := (List.nodup_cons.mp distinct).1
    have tail : rest.Nodup := (List.nodup_cons.mp distinct).2
    rw [mobiusSequentialPass,ih tail]
    by_cases same : i=index
    · subst i
      simp only [absent,ite_false,List.mem_cons,true_or,ite_true]
      unfold mobiusWrite mobiusBitPass
      split <;> simp
    · by_cases gate : index.testBit bit=true
      · simp only [mobiusWrite,gate,ite_true,List.mem_cons,same,false_or]
        by_cases own : i.testBit bit=true
        · have source : i ^^^ 2^bit≠index := by
            intro equal
            have clear := mobius_source_bit_clear bit i own
            rw [equal,gate] at clear
            contradiction
          simp only [mobiusBitPass,own,ite_true,same,ite_false,source]
        · simp only [mobiusBitPass,own,Bool.false_eq_true,ite_false,same]
      · simp only [mobiusWrite,gate,Bool.false_eq_true,ite_false,List.mem_cons,same,false_or]

/-- Full sequential loop over a power-of-two array. The first argument is
fixed array dimension; the pass counter increases from zero. -/
def mobiusMutableRuns (dimension : Nat) : Nat → Nat → (Nat → K) → Nat → K
  | _,0,values => values
  | bit,remaining+1,values => mobiusMutableRuns dimension (bit+1) remaining
      (mobiusSequentialPass bit (List.range (2^dimension)) values)

private theorem bit_runs_bounded_congr (dimension bit remaining : Nat) (a b : Nat → K)
    (within : bit+remaining≤dimension) (same : ∀ i,i<2^dimension → a i=b i)
    (i : Nat) (hi : i<2^dimension) :
    mobiusBitRuns bit remaining a i=mobiusBitRuns bit remaining b i := by
  induction remaining generalizing bit a b with
  | zero => exact same i hi
  | succ remaining ih =>
    rw [mobiusBitRuns,mobiusBitRuns]
    apply ih (bit+1) _ _ (by omega)
    intro j hj
    have target : j ^^^ 2^bit<2^dimension :=
      Nat.xor_lt_two_pow hj (Nat.pow_lt_pow_right (by decide) (by omega))
    simp only [mobiusBitPass,same j hj,same _ target]

theorem mutable_mobius_runs_exact (dimension bit remaining : Nat) (within : bit+remaining≤dimension)
    (values : Nat → K) (i : Nat) (hi : i<2^dimension) :
    mobiusMutableRuns dimension bit remaining values i=mobiusBitRuns bit remaining values i := by
  induction remaining generalizing bit values with
  | zero => rfl
  | succ remaining ih =>
    rw [mobiusMutableRuns,ih (bit+1) (by omega),mobiusBitRuns]
    apply bit_runs_bounded_congr dimension (bit+1) remaining _ _ (by omega) _ i hi
    intro j hj
    rw [sequential_mobius_pass_exact bit _ List.nodup_range]
    simp only [List.mem_range.mpr hj,ite_true]

/-- The exact ascending-index in-place bit-pass loop returns mobiusCoefficients at
every array slot. There are no assumed transform or nonaliasing premises. -/
theorem mutable_lower_mobius (n : Nat) (values : Nat → K) (i : Nat) (hi : i<2^n) :
    mobiusMutableRuns n 0 n values i=mobiusCoefficients n values i := by
  rw [mutable_mobius_runs_exact n 0 n (by omega) values i hi,bit_runs_lower_mobius n values i hi]

/-- Literal native mask guard and XOR source address. -/
theorem mobius_write_native (bit : Nat) (values : Nat → K) (index : Nat) :
    mobiusWrite bit values index=
      if index &&& 2^bit≠0 then
        (fun i => if i=index then values index-values (index ^^^ 2^bit) else values i)
      else values := by
  simp only [ne_eq,zeta_python_guard]
  unfold mobiusWrite
  cases index.testBit bit <;> simp

/-- Executable list interface. Its contract requires the supplied dimension
and actual array length to agree, as the native power-of-two caller enforces. -/
def mobiusCoefficientsMutableList (n : Nat) (values : List K) : List K :=
  (List.range values.length).map (fun i => mobiusMutableRuns n 0 n (fun j => values.getD j 0) i)

theorem mutable_lower_mobius_list (n : Nat) (values : List K) (shape : values.length=2^n) :
    mobiusCoefficientsMutableList n values=
      (List.range (2^n)).map (mobiusCoefficients n (fun j => values.getD j 0)) := by
  unfold mobiusCoefficientsMutableList
  rw [shape]
  apply List.map_congr_left
  intro i hi
  exact mutable_lower_mobius n _ i (List.mem_range.mp hi)

end NearCompression
