import NearCompression.DualMobiusWeights
import NearCompression.GenericShiftIndex

/-! Exact optimized row_weight_mles recurrence. The input bits contribute
(1-u) for zero and 1 for one after dual zeta; this is deliberately different
from the ordinary equality-kernel recurrence in GenericShiftKernel. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def dualRowSum : Nat → (Nat → K) → (Nat → K) → K
  | 0,w,_ => w 0
  | n+1,w,u => (1-u 0)*dualRowSum n (fun i => w (2*i)) (fun i => u (i+1))+
      dualRowSum n (fun i => w (2*i+1)) (fun i => u (i+1))

/-- Taking the MLE of upper-zeta weights changes Boolean zero/one weights
from (1-u,u) to (1-u,1). This identity needs no normalization or inversion. -/
theorem upper_zeta_mle_dual_sum (n : Nat) (w u : Nat → K) :
    genericRowMLE n (upperZeta n w) u=dualRowSum n w u := by
  induction n generalizing w u with
  | zero => rfl
  | succ n ih =>
    rw [genericRowMLE]
    have even : (fun i => upperZeta (n+1) w (2*i))=
        upperZeta n (fun j => w (2*j)+w (2*j+1)) := by
      funext i
      have hm : (2*i)%2=0 := by omega
      have hd : (2*i)/2=i := by omega
      simp [upperZeta,hm,hd]
    have odd : (fun i => upperZeta (n+1) w (2*i+1))=upperZeta n (fun j => w (2*j+1)) := by
      funext i
      have hm : (2*i+1)%2=1 := by omega
      have hd : (2*i+1)/2=i := by omega
      simp [upperZeta,hm,hd]
    rw [even,odd]
    have add : upperZeta n (fun j => w (2*j)+w (2*j+1))=
        (fun i => upperZeta n (fun j => w (2*j)) i+upperZeta n (fun j => w (2*j+1)) i) :=
      funext (upper_zeta_add n _ _)
    rw [add,generic_row_mle_add,ih,ih]
    simp only [dualRowSum]
    grind

def zeroBitCubeSum : List K → (List Bool → K) → K
  | [],f => f []
  | u::us,f => (1-u)*zeroBitCubeSum us (fun bits => f (false::bits))+
      zeroBitCubeSum us (fun bits => f (true::bits))

private theorem zero_cube_scale (us : List K) (a : K) (f : List Bool → K) :
    zeroBitCubeSum us (fun bits => a*f bits)=a*zeroBitCubeSum us f := by
  induction us generalizing f with
  | nil => rfl
  | cons u us ih => simp only [zeroBitCubeSum,ih]; grind

private theorem zero_cube_congr (us : List K) (f g : List Bool → K)
    (same : ∀ bits,bits.length=us.length → f bits=g bits) :
    zeroBitCubeSum us f=zeroBitCubeSum us g := by
  induction us generalizing f g with
  | nil => exact same [] rfl
  | cons u us ih =>
    rw [zeroBitCubeSum,zeroBitCubeSum]
    rw [ih (fun bits => f (false::bits)) (fun bits => g (false::bits)) (by intro bits hb; apply same; simp [hb]),
      ih (fun bits => f (true::bits)) (fun bits => g (true::bits)) (by intro bits hb; apply same; simp [hb])]

theorem dual_row_sum_boolean_cube (us : List K) (w : Nat → K) :
    dualRowSum us.length w (fun i => us.getD i 0)=
      zeroBitCubeSum us (fun bits => w (shiftListBitIndex bits)) := by
  induction us generalizing w with
  | nil => rfl
  | cons u us ih =>
    simp only [List.length_cons,dualRowSum,List.getD_cons_zero,List.getD_cons_succ,ih,zeroBitCubeSum]
    have even : (fun bits => w (shiftListBitIndex (false::bits)))=
        (fun bits => w (2*shiftListBitIndex bits)) := by funext bits; simp [shiftListBitIndex]
    have odd : (fun bits => w (shiftListBitIndex (true::bits)))=
        (fun bits => w (2*shiftListBitIndex bits+1)) := by funext bits; simp [shiftListBitIndex,Nat.add_comm]
    rw [even,odd]

/-- Exact Python no_borrow/borrow update, with arbitrary initial state. -/
def dualBorrowDP : List (K×K) → K → K → K
  | [],nb,b => nb+b
  | (r,u)::rest,nb,b => dualBorrowDP rest
      (nb*((1-r)*(1-u)+r)+b*(1-r)) (b*r*(1-u))

def dualBorrowSum : List (K×K) → Bool → K
  | [],_ => 1
  | (r,u)::rest,borrow =>
      (1-u)*shiftBitWeight r (shiftBorrowStep borrow false).1*
        dualBorrowSum rest (shiftBorrowStep borrow false).2+
      shiftBitWeight r (shiftBorrowStep borrow true).1*
        dualBorrowSum rest (shiftBorrowStep borrow true).2

theorem dual_borrow_dp_linear_sum (coords : List (K×K)) (nb b : K) :
    dualBorrowDP coords nb b=nb*dualBorrowSum coords false+b*dualBorrowSum coords true := by
  induction coords generalizing nb b with
  | nil => simp only [dualBorrowDP,dualBorrowSum]; grind
  | cons pair rest ih =>
    obtain ⟨r,u⟩ := pair
    rw [dualBorrowDP,ih]
    simp only [dualBorrowSum,shiftBorrowStep,shiftBitWeight,Bool.xor_false,Bool.xor_true,
      Bool.not_false,Bool.not_true,Bool.false_and,Bool.true_and]
    grind

theorem dual_borrow_sum_cube (coords : List (K×K)) (borrow : Bool) :
    dualBorrowSum coords borrow=zeroBitCubeSum (coords.map Prod.snd) (fun bits =>
      shiftEqBits (coords.map Prod.fst) (shiftSubtractBits borrow bits)) := by
  induction coords generalizing borrow with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨r,u⟩ := pair
    simp only [dualBorrowSum,List.map_cons,zeroBitCubeSum,shiftSubtractBits,shiftEqBits,
      zero_cube_scale,ih]
    grind

theorem row_equality_weight_bits (point : List K) (bits : List Bool)
    (shape : bits.length=point.length) :
    rowEqualityWeight point.length (fun i => point.getD i 0) (shiftListBitIndex bits)=
      shiftEqBits point bits := by
  induction point generalizing bits with
  | nil => cases bits <;> simp_all [rowEqualityWeight,shiftEqBits]
  | cons r rs ih =>
    cases bits with
    | nil => simp at shape
    | cons bit bs =>
      have tail : bs.length=rs.length := by simpa using shape
      cases bit <;>
        simp only [List.length_cons,shiftListBitIndex,Bool.false_eq_true,ite_false,ite_true,
          Nat.zero_add,rowEqualityWeight,List.getD_cons_zero,List.getD_cons_succ,shiftEqBits,shiftBitWeight]
      · have hm : (2*shiftListBitIndex bs)%2=0 := by omega
        have hd : (2*shiftListBitIndex bs)/2=shiftListBitIndex bs := by omega
        rw [hm,hd,ite_eq_left rfl,ih bs tail]
      · have hm : (1+2*shiftListBitIndex bs)%2=1 := by omega
        have hd : (1+2*shiftListBitIndex bs)/2=shiftListBitIndex bs := by omega
        rw [hm,hd,ite_eq_right (by decide : ¬(1:Nat)=0),ih bs tail]

/-- Explicit predecessor indexing supplies the same shifted row weights as
row_weights; the final borrow is discarded to implement cyclic wraparound. -/
theorem cyclic_row_weight_bits (point : List K) (bits : List Bool)
    (shape : bits.length=point.length) :
    cyclicRowWeight point.length (fun i => point.getD i 0) (shiftListBitIndex bits)=
      shiftEqBits point (shiftSubtractBits true bits) := by
  have identity := row_equality_weight_bits point (shiftSubtractBits true bits)
    (by rw [shift_subtract_bits_length,shape])
  rw [shift_subtract_index_mod,shape] at identity
  exact identity

/-- The shifted branch of the exact DP is the MLE of the explicit upper-zeta
cyclic-predecessor table used by lane_weights. -/
theorem dual_borrow_shift_mle (coords : List (K×K)) :
    dualBorrowDP coords 0 1=
      genericRowMLE coords.length
        (upperZeta coords.length (cyclicRowWeight coords.length (fun i => (coords.map Prod.fst).getD i 0)))
        (fun i => (coords.map Prod.snd).getD i 0) := by
  rw [dual_borrow_dp_linear_sum]
  have start : (0:K)*dualBorrowSum coords false+1*dualBorrowSum coords true=dualBorrowSum coords true := by grind
  rw [start,dual_borrow_sum_cube,upper_zeta_mle_dual_sum]
  have cube := dual_row_sum_boolean_cube (coords.map Prod.snd)
    (cyclicRowWeight coords.length (fun i => (coords.map Prod.fst).getD i 0))
  simp only [List.length_map] at cube
  rw [cube]
  apply zero_cube_congr
  intro bits shape
  have weight := cyclic_row_weight_bits (coords.map Prod.fst) bits (by simpa using shape)
  simpa only [List.length_map] using weight.symm

def currentWeightProduct : List (K×K) → K
  | [] => 1
  | (r,u)::rest => (1-u+u*r)*currentWeightProduct rest

def currentWeightAccumulator : List (K×K) → K → K
  | [],value => value
  | (r,u)::rest,value => currentWeightAccumulator rest (value*(1-u+u*r))

theorem current_weight_accumulator_product (coords : List (K×K)) (value : K) :
    currentWeightAccumulator coords value=value*currentWeightProduct coords := by
  induction coords generalizing value with
  | nil => simp only [currentWeightAccumulator,currentWeightProduct]; grind
  | cons pair rest ih => cases pair; simp only [currentWeightAccumulator,currentWeightProduct,ih]; grind

private theorem current_product_sum (coords : List (K×K)) :
    currentWeightProduct coords=dualBorrowSum coords false := by
  induction coords with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨r,u⟩ := pair
    simp only [currentWeightProduct,dualBorrowSum,shiftBorrowStep,shiftBitWeight,
      Bool.xor_false,Bool.not_false,Bool.not_true,Bool.false_and,ih]
    grind

theorem dual_borrow_current_mle (coords : List (K×K)) :
    currentWeightAccumulator coords 1=
      genericRowMLE coords.length
        (upperZeta coords.length (rowEqualityWeight coords.length (fun i => (coords.map Prod.fst).getD i 0)))
        (fun i => (coords.map Prod.snd).getD i 0) := by
  rw [current_weight_accumulator_product,current_product_sum]
  have start : (1:K)*dualBorrowSum coords false=dualBorrowSum coords false := by grind
  rw [start,dual_borrow_sum_cube,upper_zeta_mle_dual_sum]
  have cube := dual_row_sum_boolean_cube (coords.map Prod.snd)
    (rowEqualityWeight coords.length (fun i => (coords.map Prod.fst).getD i 0))
  simp only [List.length_map] at cube
  rw [cube]
  apply zero_cube_congr
  intro bits shape
  rw [shift_subtract_false]
  have weight := row_equality_weight_bits (coords.map Prod.fst) bits (by simpa using shape)
  simpa only [List.length_map] using weight.symm

/-- The two outputs of Python row_weight_mles, with its exact current
accumulation and exact borrow update, equal the current and cyclic-next
upper-zeta table MLEs. Arbitrary field coordinates, including zero/one and
zero products, are allowed. The empty coordinate list is included. -/
theorem optimized_row_weight_mles (coords : List (K×K)) :
    (currentWeightAccumulator coords 1,dualBorrowDP coords 0 1)=
      (genericRowMLE coords.length
        (upperZeta coords.length (rowEqualityWeight coords.length (fun i => (coords.map Prod.fst).getD i 0)))
        (fun i => (coords.map Prod.snd).getD i 0),
       genericRowMLE coords.length
        (upperZeta coords.length (cyclicRowWeight coords.length (fun i => (coords.map Prod.fst).getD i 0)))
        (fun i => (coords.map Prod.snd).getD i 0)) := by
  rw [dual_borrow_current_mle,dual_borrow_shift_mle]

end NearCompression
