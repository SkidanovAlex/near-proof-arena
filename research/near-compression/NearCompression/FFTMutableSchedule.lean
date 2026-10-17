import NearCompression.FFTButterflyWrites
import NearCompression.FFTBitReversal

/-! Complete natural-index mutable FFT model. Field operations and state updates
are mathematical operations; native word arithmetic and memory refinement remain
separate obligations. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Bit reversal followed by ascending radix-two butterfly stages. -/
def fftMutableSchedule (n : Nat) (omega : K) (coefficients : Nat → K) : Nat → Nat → K
  | 0 => fftNativeReverseLoop n 1 (2^n-1) 0 coefficients
  | s+1 => fftStageWrites (2^s)
      (fun i => fftTwiddleWalk (omega^(2^(n-(s+1)))) i)
      (List.range (2^(n-(s+1)))) (fftMutableSchedule n omega coefficients s)

/-- Each completed mutable stage agrees at every in-domain slot with the
functional block stage. This includes the actual counter/swap initialization. -/
theorem fft_mutable_schedule_stage (n s : Nat) (omega : K) (coefficients : Nat → K)
    (stage : s≤n) (b j : Nat) (hb : b<2^(n-s)) (hj : j<2^s) :
    fftMutableSchedule n omega coefficients s (2^s*b+j)=
      fftBlockStage n omega coefficients s b j := by
  induction s generalizing b j with
  | zero =>
    have jzero : j=0 := by simpa using hj
    subst j
    simp only [fftMutableSchedule,Nat.pow_zero,Nat.one_mul,Nat.add_zero,fftBlockStage]
    exact fft_native_bit_reversal n coefficients b (by simpa using hb)
  | succ s ih =>
    have hs : s≤n := by omega
    have count : 2^(n-s)=2^(n-(s+1))*2 := by
      rw [←Nat.pow_succ]
      congr 1
      omega
    have previous : ∀ c<2^(n-(s+1))*2, ∀ i<2^s,
        fftMutableSchedule n omega coefficients s (2^s*c+i)=
          fftBlockStage n omega coefficients s c i := by
      intro c hc i hi
      exact ih hs c i (by rw [count]; exact hc) hi
    have positive : 0<2^s := Nat.two_pow_pos s
    have hi : j%2^s<2^s := Nat.mod_lt j positive
    have pair := fft_stage_writes_refine n s (2^(n-(s+1))) omega coefficients
      (fftMutableSchedule n omega coefficients s) previous b (j%2^s) hb hi
    change (fftMutableSchedule n omega coefficients (s+1) (2*2^s*b+j%2^s),
      fftMutableSchedule n omega coefficients (s+1) (2*2^s*b+j%2^s+2^s)) = _ at pair
    by_cases low : j<2^s
    · have index : 2^(s+1)*b+j=2*2^s*b+j%2^s := by
        rw [Nat.pow_succ,Nat.mod_eq_of_lt low]
        simp only [Nat.mul_comm (2^s) 2]
      rw [index]
      simpa only [Nat.mod_eq_of_lt low] using congrArg Prod.fst pair
    · have split : j=j%2^s+2^s := by
        have bound : j<2^s*2 := by simpa only [Nat.pow_succ] using hj
        have quotient : j/2^s=1 := by
          have upper : j/2^s<2 := (Nat.div_lt_iff_lt_mul positive).mpr (by omega)
          have lower : 1≤j/2^s := (Nat.le_div_iff_mul_le positive).mpr (by omega)
          omega
        have division := Nat.mod_add_div j (2^s)
        rw [quotient,Nat.mul_one] at division
        omega
      have index : 2^(s+1)*b+j=2*2^s*b+j%2^s+2^s := by
        rw [Nat.pow_succ]
        rw [Nat.mul_comm (2^s) 2]
        omega
      rw [index]
      have result := congrArg Prod.snd pair
      simpa only [←split] using result

/-- Complete mutable execution yields natural-order polynomial evaluation. -/
theorem fft_mutable_schedule_evaluation (n : Nat) (omega : K) (coefficients : Nat → K)
    (root : 0<n → omega^(2^(n-1))= -1) (i : Nat) (bound : i<2^n) :
    fftMutableSchedule n omega coefficients n i=
      (coefficientPolynomial n coefficients).eval (omega^i) := by
  have h := fft_mutable_schedule_stage n n omega coefficients (by omega) 0 i (by simp) bound
  simp only [Nat.mul_zero,Nat.zero_add] at h
  rw [h,fft_stages_natural_evaluation n omega coefficients root i bound]


/-- Zero padding and full execution compose without an assumed FFT oracle. -/
theorem fft_mutable_zero_padded_evaluation (n : Nat) (omega : K) (coefficients : List K)
    (shape : coefficients.length≤2^n) (root : 0<n → omega^(2^(n-1))= -1)
    (i : Nat) (bound : i<2^n) :
    fftMutableSchedule n omega (fun t => coefficients.getD t 0) n i=
      (Poly.mk coefficients).eval (omega^i) := by
  have h := fft_mutable_schedule_stage n n omega (fun t => coefficients.getD t 0)
    (by omega) 0 i (by simp) bound
  simp only [Nat.mul_zero,Nat.zero_add] at h
  rw [h,fft_stages_zero_padded_evaluation n omega coefficients shape root i bound]

/-- The two scalar values placed in each natural-order commitment leaf are
exactly evaluation at x and -x after the complete modeled execution. -/
theorem fft_mutable_rs_pair (n : Nat) (omega : K) (coefficients : List K)
    (shape : coefficients.length≤2^(n+1)) (halfOrder : omega^(2^n)= -1)
    (i : Nat) (bound : i<2^n) :
    (fftMutableSchedule (n+1) omega (fun t => coefficients.getD t 0) (n+1) i,
     fftMutableSchedule (n+1) omega (fun t => coefficients.getD t 0) (n+1) (i+2^n))=
      ((Poly.mk coefficients).eval (omega^i),(Poly.mk coefficients).eval (-(omega^i))) := by
  have first := fft_mutable_schedule_stage (n+1) (n+1) omega
    (fun t => coefficients.getD t 0) (by omega) 0 i (by simp) (by rw [Nat.pow_succ]; omega)
  have second := fft_mutable_schedule_stage (n+1) (n+1) omega
    (fun t => coefficients.getD t 0) (by omega) 0 (i+2^n) (by simp) (by rw [Nat.pow_succ]; omega)
  simp only [Nat.mul_zero,Nat.zero_add] at first second
  rw [first,second]
  exact fft_stages_rs_pair n omega coefficients shape halfOrder i bound

end NearCompression
