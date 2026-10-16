import NearCompression.DualMobiusWeights
import Init.Data.Nat.Bitwise.Lemmas

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Simultaneous semantics of a single bit pass. The implementation below
will be proved equal despite its sequential in-place writes. -/
def zetaBitPass (bit : Nat) (values : Nat → K) (i : Nat) : K :=
  if i.testBit bit then values i else values i+values (i ||| 2^bit)

def zetaBitRuns : Nat → Nat → (Nat → K) → Nat → K
  | _,0,values => values
  | bit,count+1,values => zetaBitRuns (bit+1) count (zetaBitPass bit values)

omit [Field K] in
private theorem pair_or_bit (i b j : Nat) (small : b<2) :
    (2*i+b) ||| 2^(j+1)=2*(i ||| 2^j)+b := by
  have half : (2*i+b)/2=i := by omega
  have rem : (2*i+b)%2=b := by omega
  have powerHalf : 2^(j+1)/2=2^j := by rw [Nat.pow_succ,Nat.mul_div_cancel _ (by decide)]
  have powerRem : 2^(j+1)%2=0 := by simp [Nat.pow_succ]
  have div : ((2*i+b) ||| 2^(j+1))/2=i ||| 2^j := by rw [Nat.or_div_two,half,powerHalf]
  have mod : ((2*i+b) ||| 2^(j+1))%2=b := by
    have h := Nat.or_mod_two_pow (a:=2*i+b) (b:=2^(j+1)) (n:=1)
    simpa [rem,powerRem] using h
  have rebuild := Nat.mod_add_div ((2*i+b) ||| 2^(j+1)) 2
  rw [div,mod] at rebuild
  omega

private theorem bit_pass_pair (j i b : Nat) (values : Nat → K) (small : b<2) :
    zetaBitPass (j+1) values (2*i+b)=zetaBitPass j (fun k => values (2*k+b)) i := by
  have half : (2*i+b)/2=i := by omega
  simp only [zetaBitPass,Nat.testBit_add_one,half,pair_or_bit i b j small]

private theorem bit_runs_pair (start rounds i b : Nat) (values : Nat → K) (small : b<2) :
    zetaBitRuns (start+1) rounds values (2*i+b)=
      zetaBitRuns start rounds (fun k => values (2*k+b)) i := by
  induction rounds generalizing start values with
  | zero => rfl
  | succ rounds ih =>
    rw [zetaBitRuns,ih,zetaBitRuns]
    have same : (fun k => zetaBitPass (start+1) values (2*k+b))=
        zetaBitPass start (fun k => values (2*k+b)) := by
      funext k
      exact bit_pass_pair start k b values small
    rw [same]

private theorem first_bit_even (values : Nat → K) (i : Nat) :
    zetaBitPass 0 values (2*i)=values (2*i)+values (2*i+1) := by
  have mod : (2*i)%2=0 := by omega
  have target : (2*i) ||| 1=2*i+1 := by
    have h := Nat.two_pow_add_eq_or_of_lt (i:=1) (b:=1) (by decide) i
    simpa using h.symm
  simp only [zetaBitPass,Nat.testBit_zero,mod,Nat.reduceEqDiff,decide_false,Bool.false_eq_true,ite_false,Nat.pow_zero,target]

private theorem first_bit_odd (values : Nat → K) (i : Nat) :
    zetaBitPass 0 values (2*i+1)=values (2*i+1) := by
  have mod : (2*i+1)%2=1 := by omega
  simp [zetaBitPass,Nat.testBit_zero,mod]

/-- All passes occur in ascending bit order, exactly bit=1,2,4,... . -/
theorem bit_runs_upper_zeta (n : Nat) (values : Nat → K) (i : Nat) (bound : i<2^n) :
    zetaBitRuns 0 n values i=upperZeta n values i := by
  induction n generalizing values i with
  | zero =>
    have hi : i=0 := by simpa using bound
    subst i
    rfl
  | succ n ih =>
    have half : i/2<2^n := by rw [Nat.pow_succ] at bound; omega
    have remainder : i%2<2 := Nat.mod_lt _ (by decide)
    have rebuild : 2*(i/2)+i%2=i := by have h := Nat.mod_add_div i 2; omega
    rw [zetaBitRuns,←rebuild,bit_runs_pair 0 n _ _ _ remainder]
    rw [rebuild,upperZeta]
    by_cases even : i%2=0
    · rw [even,ite_eq_left rfl]
      have same : (fun k => zetaBitPass 0 values (2*k+0))=(fun k => values (2*k)+values (2*k+1)) := by
        funext k
        simpa using first_bit_even values k
      rw [same]
      exact ih _ _ half
    · have odd : i%2=1 := by omega
      rw [odd,ite_eq_right (by decide : ¬(1:Nat)=0)]
      rw [funext (first_bit_odd values)]
      exact ih _ _ half

/-- One actual in-place write. Reads use the current state, not a saved copy. -/
def zetaWrite (bit : Nat) (values : Nat → K) (index : Nat) : Nat → K :=
  if index.testBit bit then values else
    fun i => if i=index then values index+values (index ||| 2^bit) else values i

def zetaSequentialPass (bit : Nat) : List Nat → (Nat → K) → Nat → K
  | [],values => values
  | index::rest,values => zetaSequentialPass bit rest (zetaWrite bit values index)

/-- Source slots have the pass bit set. Consequently they are never written
by this pass, which justifies using each current-state source value. -/
theorem zeta_source_bit_set (bit i : Nat) : (i ||| 2^bit).testBit bit=true := by
  simp [Nat.testBit_or,Nat.testBit_two_pow_self]

/-- Every listed slot is visited once, in the supplied order. The Python order
is List.range N; the proof covers it without replacing mutable reads by an
unproved simultaneous-update assumption. -/
theorem sequential_zeta_pass_exact (bit : Nat) (indices : List Nat) (distinct : indices.Nodup)
    (values : Nat → K) (i : Nat) :
    zetaSequentialPass bit indices values i=
      if i∈indices then zetaBitPass bit values i else values i := by
  induction indices generalizing values with
  | nil => simp [zetaSequentialPass]
  | cons index rest ih =>
    have absent : index∉rest := (List.nodup_cons.mp distinct).1
    have tail : rest.Nodup := (List.nodup_cons.mp distinct).2
    rw [zetaSequentialPass,ih tail]
    by_cases same : i=index
    · subst i
      simp only [absent,ite_false,List.mem_cons,true_or,ite_true]
      unfold zetaWrite zetaBitPass
      split <;> simp
    · by_cases gate : index.testBit bit=true
      · simp only [zetaWrite,gate,ite_true,List.mem_cons,same,false_or]
      · have source : i ||| 2^bit≠index := by
          intro equal
          have set := zeta_source_bit_set bit i
          rw [equal] at set
          exact gate set
        simp only [zetaWrite,gate,Bool.false_eq_true,ite_false,List.mem_cons,same,false_or]
        by_cases member : i∈rest
        · simp only [member,ite_true,zetaBitPass,same,ite_false,source]
        · simp only [member,ite_false]

/-- Exact bitmask guard in the Python source, rather than merely a related
parity test. The source lookup is already the same bitwise OR operation. -/
theorem zeta_python_guard (i bit : Nat) : i &&& 2^bit=0 ↔ i.testBit bit=false := by
  constructor
  · intro zero
    have test := congrArg (fun n => n.testBit bit) zero
    simpa [Nat.testBit_and,Nat.testBit_two_pow_self] using test
  · intro clear
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases same : bit=j
    · subst j
      simp [Nat.testBit_and,Nat.testBit_two_pow_self,clear]
    · simp [Nat.testBit_and,same]

/-- Full sequential loop over a power-of-two array. The first argument is
fixed array dimension; the pass counter increases from zero. -/
def zetaMutableRuns (dimension : Nat) : Nat → Nat → (Nat → K) → Nat → K
  | _,0,values => values
  | bit,remaining+1,values => zetaMutableRuns dimension (bit+1) remaining
      (zetaSequentialPass bit (List.range (2^dimension)) values)

private theorem bit_runs_bounded_congr (dimension bit remaining : Nat) (a b : Nat → K)
    (within : bit+remaining≤dimension) (same : ∀ i,i<2^dimension → a i=b i)
    (i : Nat) (hi : i<2^dimension) :
    zetaBitRuns bit remaining a i=zetaBitRuns bit remaining b i := by
  induction remaining generalizing bit a b with
  | zero => exact same i hi
  | succ remaining ih =>
    rw [zetaBitRuns,zetaBitRuns]
    apply ih (bit+1) _ _ (by omega)
    intro j hj
    have target : j ||| 2^bit<2^dimension :=
      Nat.or_lt_two_pow hj (Nat.pow_lt_pow_right (by decide) (by omega))
    simp only [zetaBitPass,same j hj,same _ target]

theorem mutable_zeta_runs_exact (dimension bit remaining : Nat) (within : bit+remaining≤dimension)
    (values : Nat → K) (i : Nat) (hi : i<2^dimension) :
    zetaMutableRuns dimension bit remaining values i=zetaBitRuns bit remaining values i := by
  induction remaining generalizing bit values with
  | zero => rfl
  | succ remaining ih =>
    rw [zetaMutableRuns,ih (bit+1) (by omega),zetaBitRuns]
    apply bit_runs_bounded_congr dimension (bit+1) remaining _ _ (by omega) _ i hi
    intro j hj
    rw [sequential_zeta_pass_exact bit _ List.nodup_range]
    simp only [List.mem_range.mpr hj,ite_true]

/-- The exact ascending-index in-place bit-pass loop returns upperZeta at
every array slot. There are no assumed transform or nonaliasing premises. -/
theorem mutable_upper_zeta (n : Nat) (values : Nat → K) (i : Nat) (hi : i<2^n) :
    zetaMutableRuns n 0 n values i=upperZeta n values i := by
  rw [mutable_zeta_runs_exact n 0 n (by omega) values i hi,bit_runs_upper_zeta n values i hi]

/-- Equality with the literal `if not i & bit` branch, including current-state
reads at both the destination and `i | bit` source. -/
theorem zeta_write_python (bit : Nat) (values : Nat → K) (index : Nat) :
    zetaWrite bit values index=
      if index &&& 2^bit=0 then
        (fun i => if i=index then values index+values (index ||| 2^bit) else values i)
      else values := by
  simp only [zeta_python_guard]
  unfold zetaWrite
  cases index.testBit bit <;> simp

/-- Executable list interface. Its contract requires the supplied dimension
and actual array length to agree, as the Python power-of-two caller enforces. -/
def upperZetaMutableList (n : Nat) (values : List K) : List K :=
  (List.range values.length).map (fun i => zetaMutableRuns n 0 n (fun j => values.getD j 0) i)

theorem mutable_upper_zeta_list (n : Nat) (values : List K) (shape : values.length=2^n) :
    upperZetaMutableList n values=
      (List.range (2^n)).map (upperZeta n (fun j => values.getD j 0)) := by
  unfold upperZetaMutableList
  rw [shape]
  apply List.map_congr_left
  intro i hi
  exact mutable_upper_zeta n _ i (List.mem_range.mp hi)

end NearCompression
