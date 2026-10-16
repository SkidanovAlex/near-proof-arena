import NearCompression.SparseLiftPolynomial

/-! Functional radix-two DIT stage invariant. Inputs are bit-reversed and
stage butterflies have the exact lower/upper sign and ascending block layout.
This does not yet certify native permutation-counter or mutable-array loops. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def fftReverseBits : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,i => (i%2)*2^n+fftReverseBits n (i/2)

/-- Stage s block b, local position j. Each next block combines consecutive
previous blocks 2b and 2b+1; the second half uses subtraction. -/
def fftBlockStage (n : Nat) (omega : K) (coefficients : Nat → K) : Nat → Nat → Nat → K
  | 0,block,_ => coefficients (fftReverseBits n block)
  | s+1,block,j =>
      let low := j%(2^s)
      let even := fftBlockStage n omega coefficients s (2*block) low
      let odd := fftBlockStage n omega coefficients s (2*block+1) low
      let twiddle := omega^(2^(n-(s+1))*low)
      if j<2^s then even+twiddle*odd else even-twiddle*odd

private theorem coefficient_split (s : Nat) (c : Nat → K) (x : K) :
    (coefficientPolynomial (s+1) c).eval x=
      (coefficientPolynomial s (fun i => c (2*i))).eval (x*x)+
      x*(coefficientPolynomial s (fun i => c (2*i+1))).eval (x*x) := by
  rw [coefficient_polynomial_eval,laneTensor]
  simp only [Nat.pow_zero,Semiring.pow_one]
  have curve : (fun i => x^(2^(i+1)))=(fun i => (x*x)^(2^i)) := by
    funext i
    have square : x*x=x^2 := by simp only [Semiring.pow_succ,Semiring.pow_zero]; grind
    rw [square,←pow_mul_eq,Nat.pow_succ]
    congr 1
    omega
  rw [curve,←coefficient_polynomial_eval,←coefficient_polynomial_eval]

private theorem coefficient_split_negative (s : Nat) (c : Nat → K) (x : K) :
    (coefficientPolynomial (s+1) c).eval (-x)=
      (coefficientPolynomial s (fun i => c (2*i))).eval (x*x)-
      x*(coefficientPolynomial s (fun i => c (2*i+1))).eval (x*x) := by
  rw [coefficient_split]
  have square : (-x)*(-x)=x*x := by grind
  rw [square]
  grind

omit [Field K] in
private theorem reverse_even (n block : Nat) : fftReverseBits (n+1) (2*block)=fftReverseBits n block := by
  have rem : (2*block)%2=0 := by omega
  have div : (2*block)/2=block := by omega
  simp [fftReverseBits,rem,div]

omit [Field K] in
private theorem reverse_odd (n block : Nat) : fftReverseBits (n+1) (2*block+1)=2^n+fftReverseBits n block := by
  have rem : (2*block+1)%2=1 := by omega
  have div : (2*block+1)/2=block := by omega
  simp [fftReverseBits,rem,div]

/-- Exact bottom-up stage invariant. After stage s, block b contains the DFT
of coefficient subsequence rev_(n-s)(b)+2^(n-s)*t, in natural local order. -/
theorem fft_block_stage_invariant (n s : Nat) (omega : K) (coefficients : Nat → K)
    (stage : s≤n) (root : 0<n → omega^(2^(n-1))= -1)
    (block j : Nat) (blockBound : block<2^(n-s)) (slotBound : j<2^s) :
    fftBlockStage n omega coefficients s block j=
      (coefficientPolynomial s (fun t => coefficients (fftReverseBits (n-s) block+2^(n-s)*t))).eval
        (omega^(2^(n-s)*j)) := by
  induction s generalizing block j with
  | zero =>
    have zero : j=0 := by simpa using slotBound
    subst j
    simp only [fftBlockStage,coefficientPolynomial,Nat.pow_zero,List.range_one,List.map_cons,List.map_nil,
      Poly.eval,Poly.evalL,Nat.mul_zero,Nat.add_zero,Nat.sub_zero]
    grind
  | succ s ih =>
    have gap : n-s=(n-(s+1))+1 := by omega
    have lowBound : j%2^s<2^s := Nat.mod_lt _ (Nat.two_pow_pos s)
    have evenBound : 2*block<2^(n-s) := by rw [gap,Nat.pow_succ]; omega
    have oddBound : 2*block+1<2^(n-s) := by rw [gap,Nat.pow_succ]; omega
    rw [fftBlockStage,ih (by omega) _ _ evenBound lowBound,
      ih (by omega) _ _ oddBound lowBound]
    rw [gap,reverse_even,reverse_odd]
    let stride := 2^(n-(s+1))
    let offset := fftReverseBits (n-(s+1)) block
    let x := omega^(stride*(j%2^s))
    let c := fun t => coefficients (offset+stride*t)
    have evenCoefficients : (fun t => coefficients (fftReverseBits (n-(s+1)) block+2^(n-(s+1)+1)*t))=
        (fun t => c (2*t)) := by
      funext t
      dsimp [c,offset,stride]
      congr 1
      rw [Nat.pow_succ]
      grind
    have oddCoefficients : (fun t => coefficients (2^(n-(s+1))+fftReverseBits (n-(s+1)) block+
        2^(n-(s+1)+1)*t))=(fun t => c (2*t+1)) := by
      funext t
      dsimp [c,offset,stride]
      congr 1
      rw [Nat.pow_succ]
      grind
    have square : omega^(2^(n-(s+1)+1)*(j%2^s))=x*x := by
      dsimp [x,stride]
      rw [←Semiring.pow_add]
      congr 1
      rw [Nat.pow_succ]
      grind
    rw [evenCoefficients,oddCoefficients,square]
    change (if j<2^s then (coefficientPolynomial s (fun t => c (2*t))).eval (x*x)+
      x*(coefficientPolynomial s (fun t => c (2*t+1))).eval (x*x) else
      (coefficientPolynomial s (fun t => c (2*t))).eval (x*x)-
      x*(coefficientPolynomial s (fun t => c (2*t+1))).eval (x*x))=
      (coefficientPolynomial (s+1) c).eval (omega^(stride*j))
    by_cases lower : j<2^s
    · rw [ite_eq_left lower,←coefficient_split]
      have same : x=omega^(stride*j) := by dsimp [x]; rw [Nat.mod_eq_of_lt lower]
      rw [same]
    · rw [ite_eq_right lower,←coefficient_split_negative]
      have splitIndex : j=j%2^s+2^s := by
        have rem : j%2^s=j-2^s := by
          rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by rw [Nat.pow_succ] at slotBound; omega)]
        rw [rem]
        omega
      have halfOrder : omega^(stride*2^s)= -1 := by
        dsimp [stride]
        rw [←Nat.pow_add]
        have exponent : n-(s+1)+s=n-1 := by omega
        rw [exponent]
        exact root (by omega)
      have negative : omega^(stride*j)= -x := by
        have exponent : stride*j=stride*(j%2^s)+stride*2^s := by
          have eq := congrArg (fun t => stride*t) splitIndex
          simpa only [Nat.mul_add] using eq
        rw [exponent,Semiring.pow_add,halfOrder]
        change x*(-1)= -x
        grind
      rw [negative]

/-- Final functional stages give the natural-order polynomial evaluations.
The mutable native implementation must still refine these exact stages. -/
theorem fft_stages_natural_evaluation (n : Nat) (omega : K) (coefficients : Nat → K)
    (root : 0<n → omega^(2^(n-1))= -1) (i : Nat) (bound : i<2^n) :
    fftBlockStage n omega coefficients n 0 i=(coefficientPolynomial n coefficients).eval (omega^i) := by
  have result := fft_block_stage_invariant n n omega coefficients (by omega) root 0 i (by simp) bound
  simpa only [Nat.sub_self,fftReverseBits,Nat.pow_zero,Nat.one_mul,Nat.zero_add] using result

/-- Short input coefficient arrays are zero padded by getD, exactly as both
native forward-FFT entry points initialize their larger output domains. -/
theorem fft_stages_zero_padded_evaluation (n : Nat) (omega : K) (coefficients : List K)
    (shape : coefficients.length≤2^n) (root : 0<n → omega^(2^(n-1))= -1)
    (i : Nat) (bound : i<2^n) :
    fftBlockStage n omega (fun t => coefficients.getD t 0) n 0 i=
      (Poly.mk coefficients).eval (omega^i) := by
  rw [fft_stages_natural_evaluation n omega _ root i bound,coefficient_polynomial_eval,
    ←lane_tensor_monomial]
  have curve : (fun t => (omega^i)^(2^t))=genericMonomialCurve (omega^i) := by
    funext t
    exact (generic_monomial_curve_power _ _).symm
  rw [curve]
  exact generic_monomial_tensor_curve n coefficients shape _

/-- Natural first-half/second-half output positions are precisely the ±x
leaf pair committed by rs_commit and opened by the source-pair interface. -/
theorem fft_stages_rs_pair (n : Nat) (omega : K) (coefficients : List K)
    (shape : coefficients.length≤2^(n+1)) (halfOrder : omega^(2^n)= -1)
    (i : Nat) (bound : i<2^n) :
    (fftBlockStage (n+1) omega (fun t => coefficients.getD t 0) (n+1) 0 i,
     fftBlockStage (n+1) omega (fun t => coefficients.getD t 0) (n+1) 0 (i+2^n))=
      ((Poly.mk coefficients).eval (omega^i),(Poly.mk coefficients).eval (-(omega^i))) := by
  have root : 0<n+1 → omega^(2^((n+1)-1))= -1 := by intro h; simpa using halfOrder
  rw [fft_stages_zero_padded_evaluation (n+1) omega coefficients shape root i (by rw [Nat.pow_succ]; omega),
    fft_stages_zero_padded_evaluation (n+1) omega coefficients shape root (i+2^n) (by rw [Nat.pow_succ]; omega)]
  rw [Semiring.pow_add,halfOrder]
  have sign : omega^i*(-1)= -(omega^i) := by grind
  rw [sign]

end NearCompression
