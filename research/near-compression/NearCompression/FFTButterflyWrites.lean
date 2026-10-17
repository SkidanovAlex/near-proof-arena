import NearCompression.RadixTwoFFTStages

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def fftButterflyWrite (left right : Nat) (twiddle : K) (state : Nat → K) : Nat → K :=
  let u := state left
  let v := twiddle*state right
  fun i => if i=left then u+v else if i=right then u-v else state i

def fftBlockWrites (base half : Nat) (twiddles : Nat → K) : List Nat → (Nat → K) → Nat → K
  | [],state => state
  | offset::rest,state => fftBlockWrites base half twiddles rest
      (fftButterflyWrite (base+offset) (base+offset+half) (twiddles offset) state)

/-- Both outputs of a pair always use the same pre-write u,v, matching the
native loop's temporary variables rather than rereading the overwritten u. -/
theorem fft_butterfly_write_pair (base half offset : Nat) (positive : 0<half)
    (twiddle : K) (state : Nat → K) :
    (fftButterflyWrite (base+offset) (base+offset+half) twiddle state (base+offset),
     fftButterflyWrite (base+offset) (base+offset+half) twiddle state (base+offset+half))=
      (state (base+offset)+twiddle*state (base+offset+half),
       state (base+offset)-twiddle*state (base+offset+half)) := by
  simp [fftButterflyWrite,show half≠0 by omega]

private theorem block_writes_pair (base half : Nat) (twiddles : Nat → K)
    (offsets : List Nat) (distinct : offsets.Nodup) (bounds : ∀ j∈offsets,j<half)
    (state : Nat → K) (i : Nat) (hi : i<half) :
    (fftBlockWrites base half twiddles offsets state (base+i),
     fftBlockWrites base half twiddles offsets state (base+i+half))=
      if i∈offsets then
        (state (base+i)+twiddles i*state (base+i+half),state (base+i)-twiddles i*state (base+i+half))
      else (state (base+i),state (base+i+half)) := by
  induction offsets generalizing state with
  | nil => simp [fftBlockWrites]
  | cons j rest ih =>
    have absent := (List.nodup_cons.mp distinct).1
    have tail := (List.nodup_cons.mp distinct).2
    have hj := bounds j (by simp)
    have tailBounds : ∀ k∈rest,k<half := by intro k hk; exact bounds k (by simp [hk])
    change (fftBlockWrites base half twiddles rest (fftButterflyWrite (base+j) (base+j+half) (twiddles j) state) (base+i),
      fftBlockWrites base half twiddles rest (fftButterflyWrite (base+j) (base+j+half) (twiddles j) state) (base+i+half))=_
    rw [ih tail tailBounds]
    by_cases same : i=j
    · subst i
      simp only [absent,ite_false,List.mem_cons,true_or,ite_true]
      exact fft_butterfly_write_pair base half j (by omega) (twiddles j) state
    · have ll : base+i≠base+j := by omega
      have lr : base+i≠base+j+half := by omega
      have rl : base+i+half≠base+j := by omega
      have rr : base+i+half≠base+j+half := by omega
      simp only [List.mem_cons,same,false_or,fftButterflyWrite,ll,lr,rl,rr,ite_false]

/-- Exact ascending-offset mutable butterfly block, including current-state
reads and the two output locations. Pair disjointness is proved internally. -/
theorem fft_block_writes_exact (base half : Nat) (twiddles : Nat → K)
    (state : Nat → K) (i : Nat) (hi : i<half) :
    (fftBlockWrites base half twiddles (List.range half) state (base+i),
     fftBlockWrites base half twiddles (List.range half) state (base+i+half))=
      (state (base+i)+twiddles i*state (base+i+half),state (base+i)-twiddles i*state (base+i+half)) := by
  have result := block_writes_pair base half twiddles (List.range half) List.nodup_range
    (fun j hj => List.mem_range.mp hj) state i hi
  simpa only [List.mem_range.mpr hi,ite_true] using result

/-- A block writes only its declared contiguous range. -/
theorem fft_block_writes_outside (base half : Nat) (twiddles : Nat → K)
    (offsets : List Nat) (bounds : ∀ j∈offsets,j<half) (state : Nat → K)
    (i : Nat) (outside : i<base ∨ base+2*half≤i) :
    fftBlockWrites base half twiddles offsets state i=state i := by
  induction offsets generalizing state with
  | nil => rfl
  | cons j rest ih =>
    have hj := bounds j (by simp)
    have tail : ∀ k∈rest,k<half := by intro k hk; exact bounds k (by simp [hk])
    rw [fftBlockWrites,ih tail]
    simp [fftButterflyWrite,show i≠base+j by omega,show i≠base+j+half by omega]

def fftTwiddleWalk (step : K) : Nat → K
  | 0 => 1
  | i+1 => fftTwiddleWalk step i*step

theorem fft_twiddle_walk_power (step : K) (i : Nat) : fftTwiddleWalk step i=step^i := by
  induction i with
  | zero => simp only [fftTwiddleWalk,Semiring.pow_zero]
  | succ i ih => simp only [fftTwiddleWalk,Semiring.pow_succ,ih]


def fftStageWrites (half : Nat) (twiddles : Nat → K) : List Nat → (Nat → K) → Nat → K
  | [],state => state
  | block::rest,state => fftStageWrites half twiddles rest
      (fftBlockWrites (2*half*block) half twiddles (List.range half) state)

private theorem separate_blocks (half b c i : Nat) (hi : i<half) (different : b≠c) :
    (2*half*b+i<2*half*c ∨ 2*half*c+2*half≤2*half*b+i) ∧
    (2*half*b+i+half<2*half*c ∨ 2*half*c+2*half≤2*half*b+i+half) := by
  by_cases lt : b<c
  · have h := Nat.mul_le_mul_left (2*half) (show b+1≤c by omega)
    simp only [Nat.mul_add,Nat.mul_one] at h
    constructor <;> left <;> omega
  · have h := Nat.mul_le_mul_left (2*half) (show c+1≤b by omega)
    simp only [Nat.mul_add,Nat.mul_one] at h
    constructor <;> right <;> omega

private theorem stage_writes_pair (half : Nat) (twiddles : Nat → K)
    (blocks : List Nat) (distinct : blocks.Nodup) (state : Nat → K)
    (b i : Nat) (hi : i<half) :
    (fftStageWrites half twiddles blocks state (2*half*b+i),
     fftStageWrites half twiddles blocks state (2*half*b+i+half)) =
      if b∈blocks then
        (state (2*half*b+i)+twiddles i*state (2*half*b+i+half),
         state (2*half*b+i)-twiddles i*state (2*half*b+i+half))
      else (state (2*half*b+i),state (2*half*b+i+half)) := by
  induction blocks generalizing state with
  | nil => simp [fftStageWrites]
  | cons c rest ih =>
    have absent := (List.nodup_cons.mp distinct).1
    have tail := (List.nodup_cons.mp distinct).2
    rw [fftStageWrites,ih tail]
    by_cases same : b=c
    · subst b
      simp only [absent,ite_false,List.mem_cons,true_or,ite_true]
      exact fft_block_writes_exact (2*half*c) half twiddles state i hi
    · have sep := separate_blocks half b c i hi same
      have first := fft_block_writes_outside (2*half*c) half twiddles
        (List.range half) (fun j hj => List.mem_range.mp hj) state (2*half*b+i) sep.1
      have second := fft_block_writes_outside (2*half*c) half twiddles
        (List.range half) (fun j hj => List.mem_range.mp hj) state (2*half*b+i+half) sep.2
      simp only [List.mem_cons,same,false_or,first,second]

/-- Complete ascending block loop: every output pair depends on the original
stage state, even though the implementation reads and writes a changing state. -/
theorem fft_stage_writes_exact (half count : Nat) (twiddles : Nat → K)
    (state : Nat → K) (b i : Nat) (hb : b<count) (hi : i<half) :
    (fftStageWrites half twiddles (List.range count) state (2*half*b+i),
     fftStageWrites half twiddles (List.range count) state (2*half*b+i+half)) =
      (state (2*half*b+i)+twiddles i*state (2*half*b+i+half),
       state (2*half*b+i)-twiddles i*state (2*half*b+i+half)) := by
  have h := stage_writes_pair half twiddles (List.range count) List.nodup_range state b i hi
  simpa only [List.mem_range.mpr hb,ite_true] using h


/-- One full mutable stage refines the established functional FFT stage.
No root-of-unity condition is needed for this implementation equivalence. -/
theorem fft_stage_writes_refine (n s count : Nat) (omega : K)
    (coefficients state : Nat → K)
    (previous : ∀ b<count*2, ∀ i<2^s,
      state (2^s*b+i)=fftBlockStage n omega coefficients s b i)
    (b i : Nat) (hb : b<count) (hi : i<2^s) :
    let next := fftStageWrites (2^s)
      (fun j => fftTwiddleWalk (omega^(2^(n-(s+1)))) j) (List.range count) state
    (next (2*2^s*b+i),next (2*2^s*b+i+2^s)) =
      (fftBlockStage n omega coefficients (s+1) b i,
       fftBlockStage n omega coefficients (s+1) b (i+2^s)) := by
  dsimp only
  rw [fft_stage_writes_exact (2^s) count _ state b i hb hi]
  have leftIndex : 2*2^s*b+i=2^s*(2*b)+i := by simp only [Nat.mul_assoc,Nat.mul_left_comm]
  have rightIndex : 2*2^s*b+i+2^s=2^s*(2*b+1)+i := by
    simp only [Nat.mul_add,Nat.mul_one]
    omega
  rw [rightIndex,leftIndex,previous (2*b) (by omega) i hi,
    previous (2*b+1) (by omega) i hi,fft_twiddle_walk_power,←pow_mul_eq]
  have rem : i%2^s=i := Nat.mod_eq_of_lt hi
  have remUpper : (i+2^s)%2^s=i := by simp only [Nat.add_mod,Nat.mod_self,Nat.add_zero,rem]
  simp only [fftBlockStage,rem,remUpper,hi,ite_true,
    show ¬i+2^s<2^s by omega,ite_false]

end NearCompression
