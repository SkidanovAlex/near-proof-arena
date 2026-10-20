import NearCompression.RadixTwoFFTStages
import NearCompression.UpperZetaBitPass

namespace NearCompression

/-- Arithmetic form of the native high-to-low reversed carry. -/
def fftReverseCarry : Nat → Nat → Nat
  | 0,j => j
  | n+1,j => if j<2^n then j+2^n else fftReverseCarry n (j-2^n)

/-- Exact native xor/test-bit carry, with the bit position decreasing after
each set bit. The exhausted case is irrelevant before the last array index. -/
def fftReverseCarryXor : Nat → Nat → Nat
  | 0,j => j
  | n+1,j => if j.testBit n then fftReverseCarryXor n (j ^^^ 2^n) else j ^^^ 2^n

theorem fft_reverse_bits_bound (n i : Nat) : fftReverseBits n i<2^n := by
  induction n generalizing i with
  | zero => simp [fftReverseBits]
  | succ n ih =>
    have bound := ih (i/2)
    have rem := Nat.mod_lt i (by decide : 0<2)
    have cases : i%2=0 ∨ i%2=1 := by omega
    rcases cases with h|h <;> simp only [fftReverseBits,h,Nat.zero_mul,Nat.one_mul,Nat.zero_add,Nat.pow_succ] <;> omega

private theorem xor_clear_bit (n j : Nat) (bound : j<2^n) : j ^^^ 2^n=j+2^n := by
  rw [←Nat.or_two_pow_eq_add_of_lt bound]
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases same : n=bit
  · subst bit
    simp [Nat.testBit_xor,Nat.testBit_or,Nat.testBit_two_pow_self,Nat.testBit_lt_two_pow bound]
  · simp [Nat.testBit_xor,Nat.testBit_or,same]

private theorem xor_set_bit (n j : Nat) (bound : j<2^n) : (j+2^n) ^^^ 2^n=j := by
  rw [←xor_clear_bit n j bound,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]

theorem fft_reverse_carry_xor (n j : Nat) (bound : j<2^n) :
    fftReverseCarryXor n j=fftReverseCarry n j := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    by_cases low : j<2^n
    · simp only [fftReverseCarryXor,fftReverseCarry,Nat.testBit_lt_two_pow low,Bool.false_eq_true,ite_false,low,ite_true]
      exact xor_clear_bit n j low
    · have high : 2^n≤j := by omega
      have bit : j.testBit n=true := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt high bound
      have tail : j-2^n<2^n := by rw [Nat.pow_succ] at bound; omega
      have clear : j ^^^ 2^n=j-2^n := by
        have decompose : j=(j-2^n)+2^n := by omega
        calc
          j ^^^ 2^n=((j-2^n)+2^n) ^^^ 2^n := congrArg (fun x => x ^^^ 2^n) decompose
          _ = _ := xor_set_bit n (j-2^n) tail
      simp only [fftReverseCarryXor,fftReverseCarry,bit,ite_true,low,ite_false,clear]
      exact ih _ tail

/-- One native counter update advances the represented ordinary index. This
is used only before N-1, so no exhausted-bit overflow iteration is presumed. -/
theorem fft_reverse_carry_successor (n i : Nat) (bound : i+1<2^n) :
    fftReverseCarry n (fftReverseBits n i)=fftReverseBits n (i+1) := by
  induction n generalizing i with
  | zero => simp at bound
  | succ n ih =>
    have small := fft_reverse_bits_bound n (i/2)
    by_cases even : i%2=0
    · have rem : (i+1)%2=1 := by omega
      have div : (i+1)/2=i/2 := by omega
      simp only [fftReverseBits,even,rem,div,Nat.zero_mul,Nat.one_mul,Nat.zero_add,
        fftReverseCarry,small,ite_true]
      omega
    · have odd : i%2=1 := by have h := Nat.mod_lt i (by decide : 0<2); omega
      have rem : (i+1)%2=0 := by omega
      have div : (i+1)/2=i/2+1 := by omega
      have next : i/2+1<2^n := by rw [Nat.pow_succ] at bound; omega
      simp only [fftReverseBits,odd,rem,div,Nat.zero_mul,Nat.one_mul,Nat.zero_add,fftReverseCarry]
      rw [ite_eq_right (by omega : ¬2^n+fftReverseBits n (i/2)<2^n)]
      have subtract : 2^n+fftReverseBits n (i/2)-2^n=fftReverseBits n (i/2) := by omega
      rw [subtract,ih _ next]

def fftReverseCounter (n : Nat) : Nat → Nat
  | 0 => 0
  | i+1 => fftReverseCarryXor n (fftReverseCounter n i)

private theorem reverse_zero (n : Nat) : fftReverseBits n 0=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fftReverseBits,ih]

theorem fft_reverse_counter_exact (n i : Nat) (bound : i<2^n) :
    fftReverseCounter n i=fftReverseBits n i := by
  induction i with
  | zero => exact (reverse_zero n).symm
  | succ i ih =>
    rw [fftReverseCounter,ih (by omega),fft_reverse_carry_xor n _ (fft_reverse_bits_bound n i)]
    exact fft_reverse_carry_successor n i bound

theorem fft_reverse_test_bit (n i bit : Nat) (position : bit<n) :
    (fftReverseBits n i).testBit bit=i.testBit (n-1-bit) := by
  induction n generalizing i bit with
  | zero => omega
  | succ n ih =>
    have form : fftReverseBits (n+1) i=2^n*(i%2)+fftReverseBits n (i/2) := by
      rw [fftReverseBits,Nat.mul_comm (i%2)]
    rw [form,Nat.testBit_two_pow_mul_add _ (fft_reverse_bits_bound n (i/2))]
    by_cases low : bit<n
    · rw [ite_eq_left low,ih _ _ low,Nat.testBit_div_two]
      congr 1
      omega
    · have equal : bit=n := by omega
      subst bit
      simp [Nat.testBit_zero]

theorem fft_reverse_involutive (n i : Nat) (bound : i<2^n) :
    fftReverseBits n (fftReverseBits n i)=i := by
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases low : bit<n
  · rw [fft_reverse_test_bit n _ bit low,fft_reverse_test_bit n i (n-1-bit) (by omega)]
    congr 1
    omega
  · have size : 2^n≤2^bit := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (fft_reverse_bits_bound n _) size),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le bound size)]

/-- Exactly the native `if i<j { swap(i,j) }` action. -/
def fftConditionalSwap {A : Type} (permutation : Nat → Nat) (i : Nat) (state : Nat → A) : Nat → A :=
  if i<permutation i then fun t =>
    if t=i then state (permutation i) else if t=permutation i then state i else state t
  else state

def fftSwapLoop {A : Type} (permutation : Nat → Nat) : List Nat → (Nat → A) → Nat → A
  | [],state => state
  | i::rest,state => fftSwapLoop permutation rest (fftConditionalSwap permutation i state)

/-- A sequential conditional-swap loop over an involution visits each orbit
at most once. The minimum element determines whether its pair was swapped. -/
private theorem swap_loop_formula {A : Type} (N : Nat) (p : Nat → Nat)
    (inverse : ∀ i,i<N → p (p i)=i)
    (indices : List Nat) (distinct : indices.Nodup) (indicesBound : ∀ i∈indices,i<N)
    (state : Nat → A) (i : Nat) (bound : i<N) :
    fftSwapLoop p indices state i=if min i (p i)∈indices then state (p i) else state i := by
  induction indices generalizing state with
  | nil => simp [fftSwapLoop]
  | cons head rest ih =>
    have absent : head∉rest := (List.nodup_cons.mp distinct).1
    have tail : rest.Nodup := (List.nodup_cons.mp distinct).2
    have headBound := indicesBound head (by simp)
    have tailBound : ∀ j∈rest,j<N := by intro j hj; exact indicesBound j (by simp [hj])
    have invI := inverse i bound
    have invHead := inverse head headBound
    rw [fftSwapLoop,ih tail tailBound]
    by_cases gate : head<p head
    · by_cases equal : min i (p i)=head
      · have notRest : min i (p i)∉rest := by rw [equal]; exact absent
        simp only [List.mem_cons,equal,true_or,ite_true,fftConditionalSwap,gate,absent,ite_false]
        by_cases first : i=head
        · subst i
          simp
        · have second : p i=head := by omega
          have selected : i=p head := by rw [←second,invI]
          have ne : p head≠head := by omega
          simp [selected,invHead,ne]
      · have first : i≠head := by
          intro h
          subst i
          apply equal
          exact Nat.min_eq_left (by omega)
        have second : i≠p head := by
          intro h
          have partner : p i=head := by rw [h,invHead]
          apply equal
          rw [partner]
          exact Nat.min_eq_right (by omega)
        have partnerFirst : p i≠head := by intro h; exact second (by rw [←h,invI])
        have partnerSecond : p i≠p head := by
          intro h
          exact first (by have eq := congrArg p h; simpa [invI,invHead] using eq)
        simp only [List.mem_cons,equal,false_or,fftConditionalSwap,gate,ite_true,
          first,second,partnerFirst,partnerSecond,ite_false]
    · by_cases equal : min i (p i)=head
      · have fixed : i=p i := by
          by_cases order : i≤p i
          · have h : i=head := by rw [Nat.min_eq_left order] at equal; exact equal
            subst i
            omega
          · have h : p i=head := by rw [Nat.min_eq_right (by omega)] at equal; exact equal
            have ip : i=p head := by rw [←h,invI]
            omega
        simp only [fftConditionalSwap,gate,ite_false,List.mem_cons,equal,true_or,ite_true]
        split
        · rfl
        · exact congrArg state fixed
      · simp only [fftConditionalSwap,gate,ite_false,List.mem_cons,equal,false_or]

/-- The exact ascending-index conditional swaps materialize the bit-reversed
input permutation needed by fftBlockStage stage zero. -/
theorem fft_bit_reverse_swaps {A : Type} (n : Nat) (state : Nat → A) (i : Nat) (bound : i<2^n) :
    fftSwapLoop (fftReverseBits n) (List.range (2^n)) state i=state (fftReverseBits n i) := by
  have result := swap_loop_formula (2^n) (fftReverseBits n)
    (fft_reverse_involutive n)
    (List.range (2^n)) List.nodup_range (fun j hj => List.mem_range.mp hj) state i bound
  have member : min i (fftReverseBits n i)∈List.range (2^n) := List.mem_range.mpr
    (Nat.lt_of_le_of_lt (Nat.min_le_left _ _) bound)
  simpa only [member,ite_true] using result

/-- Literal outer loop: update the reversed counter, then conditionally swap,
then advance the ordinary index. The initial index is one and counter zero. -/
def fftNativeReverseLoop {A : Type} (n : Nat) : Nat → Nat → Nat → (Nat → A) → Nat → A
  | _,0,_,state => state
  | index,remaining+1,counter,state =>
      let next := fftReverseCarryXor n counter
      fftNativeReverseLoop n (index+1) remaining next
        (fftConditionalSwap (fun _ => next) index state)

private theorem native_reverse_loop_exact {A : Type} (n index remaining : Nat)
    (positive : 0<index) (bound : index+remaining≤2^n) (state : Nat → A) :
    fftNativeReverseLoop n index remaining (fftReverseBits n (index-1)) state=
      fftSwapLoop (fftReverseBits n) ((List.range remaining).map (fun t => index+t)) state := by
  induction remaining generalizing index state with
  | zero => rfl
  | succ remaining ih =>
    rw [fftNativeReverseLoop,fft_reverse_carry_xor n _ (fft_reverse_bits_bound n _)]
    have next : fftReverseCarry n (fftReverseBits n (index-1))=fftReverseBits n index := by
      have step := fft_reverse_carry_successor n (index-1) (by omega)
      simpa [Nat.sub_add_cancel (by omega : 1≤index)] using step
    rw [next]
    have predecessor : (index+1)-1=index := by omega
    have tail := ih (index+1) (by omega) (by omega)
      (fftConditionalSwap (fun _ => fftReverseBits n index) index state)
    rw [predecessor] at tail
    rw [tail,List.range_succ_eq_map,List.map_cons,List.map_map]
    simp only [Nat.add_zero,Function.comp_def,fftSwapLoop]
    have same : (fun t => index+(t+1))=(fun t => index+1+t) := by funext t; omega
    rw [same]
    rfl

/-- Combined counter-and-swap correctness for the native loop's exact start
and iteration count. This produces the stage-zero input array. -/
theorem fft_native_bit_reversal {A : Type} (n : Nat) (state : Nat → A) (i : Nat) (bound : i<2^n) :
    fftNativeReverseLoop n 1 (2^n-1) 0 state i=state (fftReverseBits n i) := by
  have positive := Nat.two_pow_pos n
  have exactLoop := native_reverse_loop_exact n 1 (2^n-1) (by omega) (by omega) state
  simp only [Nat.sub_self,reverse_zero] at exactLoop
  rw [exactLoop]
  have indices : List.range (2^n)=0::((List.range (2^n-1)).map (fun t => 1+t)) := by
    have size : 2^n=(2^n-1)+1 := by omega
    calc
      List.range (2^n)=List.range ((2^n-1)+1) := congrArg List.range size
      _ = _ := by rw [List.range_succ_eq_map]; simp [Nat.add_comm]
  have swaps := fft_bit_reverse_swaps n state i bound
  rw [indices,fftSwapLoop] at swaps
  simp only [fftConditionalSwap,reverse_zero,Nat.lt_irrefl,ite_false] at swaps
  exact swaps

end NearCompression
