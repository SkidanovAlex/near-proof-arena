import NearCompression.DualMobiusWeights
import NearCompression.GenericPackingIdentity

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem cube_add (n : Nat) (f g : Nat → K) :
    cubeSum n (fun i => f i+g i)=cubeSum n f+cubeSum n g := by
  unfold cubeSum
  induction List.range (2^n) with
  | nil => simp; grind
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih]; grind

private theorem cube_scale (n : Nat) (a : K) (f : Nat → K) :
    cubeSum n (fun i => a*f i)=a*cubeSum n f := by
  unfold cubeSum
  induction List.range (2^n) with
  | nil => simp; grind
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih]; grind

private theorem cube_congr (n : Nat) (f g : Nat → K) (same : ∀ i,i<2^n → f i=g i) :
    cubeSum n f=cubeSum n g := by
  unfold cubeSum
  congr 1
  apply List.map_congr_left
  intro i hi
  exact same i (List.mem_range.mp hi)

/-- Consecutive coefficient slots enumerate the row coordinate first. -/
theorem cube_sum_split_axes (n p : Nat) (f : Nat → K) :
    cubeSum (n+p) f=cubeSum p (fun col => cubeSum n (fun row => f (row+2^n*col))) := by
  induction n generalizing f with
  | zero =>
    simp only [Nat.zero_add,Nat.pow_zero,Nat.one_mul,cubeSum,List.range_one,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    have same : (fun col => f col+0)=f := by funext col; grind
    rw [same]
  | succ n ih =>
    rw [Nat.succ_add,cube_sum_split,ih,ih]
    have same : (fun col => cubeSum (n+1) (fun row => f (row+2^(n+1)*col)))=
        (fun col => cubeSum n (fun row => f (2*(row+2^n*col)))+
          cubeSum n (fun row => f (2*(row+2^n*col)+1))) := by
      funext col
      rw [cube_sum_split]
      congr 1 <;> congr 1 <;> funext row <;> congr 1 <;> simp only [Nat.pow_succ] <;> grind
    rw [same,cube_add]

/-- A packed coefficient weight table, with row bits low and column bits high.
This is the exact list comprehension order of lane_weights. -/
def packedDualWeight (n p : Nat) (point current next : Nat → K) (index : Nat) : K :=
  upperZeta p current (index/2^n)*upperZeta n (rowEqualityWeight n point) (index%2^n)+
  upperZeta p next (index/2^n)*upperZeta n (cyclicRowWeight n point) (index%2^n)

theorem packed_dual_weight_index (n p row col : Nat) (point current next : Nat → K)
    (bound : row<2^n) :
    packedDualWeight n p point current next (row+2^n*col)=
      upperZeta p current col*upperZeta n (rowEqualityWeight n point) row+
      upperZeta p next col*upperZeta n (cyclicRowWeight n point) row := by
  have hd : (row+2^n*col)/2^n=col := by
    rw [Nat.add_mul_div_left row col (Nat.two_pow_pos n),Nat.div_eq_of_lt bound,Nat.zero_add]
  have hm : (row+2^n*col)%2^n=row := by simp [Nat.add_mod,Nat.mod_eq_of_lt bound]
  simp only [packedDualWeight,hd,hm]

/-- Product decomposition used by lane_weight_mle, including a partially
occupied lane after its column slot arrays have been zero padded. No nonzero
factor or division assumption is needed. -/
theorem packed_dual_weight_mle (n p : Nat) (point current next u : Nat → K) :
    genericRowMLE (n+p) (packedDualWeight n p point current next) u=
      genericRowMLE n (upperZeta n (rowEqualityWeight n point)) u*
        genericRowMLE p (upperZeta p current) (fun i => u (n+i))+
      genericRowMLE n (upperZeta n (cyclicRowWeight n point)) u*
        genericRowMLE p (upperZeta p next) (fun i => u (n+i)) := by
  rw [generic_row_mle_split_axes]
  have same : genericRowMLE p
      (fun col => genericRowMLE n (fun row => packedDualWeight n p point current next (row+2^n*col)) u)
      (fun i => u (n+i))=
    genericRowMLE p (fun col => upperZeta p current col*genericRowMLE n (upperZeta n (rowEqualityWeight n point)) u+
      upperZeta p next col*genericRowMLE n (upperZeta n (cyclicRowWeight n point)) u) (fun i => u (n+i)) := by
    apply generic_row_mle_congr
    intro col hc
    have inner := generic_row_mle_congr n
      (fun row => packedDualWeight n p point current next (row+2^n*col))
      (fun row => upperZeta p current col*upperZeta n (rowEqualityWeight n point) row+
        upperZeta p next col*upperZeta n (cyclicRowWeight n point) row) u
      (fun row hr => packed_dual_weight_index n p row col point current next hr)
    rw [inner,generic_row_mle_add,generic_row_mle_scale,generic_row_mle_scale]
  rw [same,generic_row_mle_add]
  have commute : ∀ a : K,∀ f : Nat → K,(fun i => f i*a)=(fun i => a*f i) := by intros; funext i; grind
  rw [commute,commute,generic_row_mle_scale,generic_row_mle_scale]

private theorem cube_commute (n p : Nat) (f : Nat → Nat → K) :
    cubeSum n (fun row => cubeSum p (fun col => f row col))=
      cubeSum p (fun col => cubeSum n (fun row => f row col)) := by
  induction n generalizing f with
  | zero =>
    simp only [cubeSum,Nat.pow_zero,List.range_one,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    have same : (fun col => f 0 col+0)=(fun col => f 0 col) := by funext col; grind
    rw [same]
    grind
  | succ n ih =>
    rw [cube_sum_split,ih,ih]
    have same : (fun col => cubeSum (n+1) (fun row => f row col))=
        (fun col => cubeSum n (fun row => f (2*row) col)+cubeSum n (fun row => f (2*row+1) col)) := by
      funext col
      exact cube_sum_split n _
    rw [same,cube_add]

/-- The full one-dimensional Mobius transform splits into row and column
transforms in exactly the packed low-row/high-column order. -/
theorem mobius_split_axes (n p : Nat) (values : Nat → K) (row col : Nat)
    (bound : row<2^n) :
    mobiusCoefficients (n+p) values (row+2^n*col)=
      mobiusCoefficients p (fun c => mobiusCoefficients n (fun r => values (r+2^n*c)) row) col := by
  induction n generalizing values row col with
  | zero =>
    have hr : row=0 := by simpa using bound
    subst row
    simp only [Nat.zero_add,Nat.pow_zero,Nat.one_mul,mobiusCoefficients]
  | succ n ih =>
    have half : row/2<2^n := by rw [Nat.pow_succ] at bound; omega
    have two : 2^(n+1)*col=2*(2^n*col) := by rw [Nat.pow_succ]; grind
    have modulo : (row+2^(n+1)*col)%2=row%2 := by
      rw [two]
      simp [Nat.add_mod]
    have division : (row+2^(n+1)*col)/2=row/2+2^n*col := by
      rw [two,Nat.add_mul_div_left _ _ (by decide)]
    rw [Nat.succ_add,mobiusCoefficients,modulo,division]
    by_cases even : row%2=0
    · rw [ite_eq_left even,ih _ _ _ half]
      have same : (fun c => mobiusCoefficients (n+1) (fun r => values (r+2^(n+1)*c)) row)=
          (fun c => mobiusCoefficients n (fun r => values (2*(r+2^n*c))) (row/2)) := by
        funext c
        rw [mobiusCoefficients,ite_eq_left even]
        congr 1
        funext r
        congr 1
        rw [Nat.pow_succ]
        grind
      rw [same]
    · rw [ite_eq_right even,ih _ _ _ half]
      have same : (fun c => mobiusCoefficients (n+1) (fun r => values (r+2^(n+1)*c)) row)=
          (fun c => mobiusCoefficients n (fun r => values (2*(r+2^n*c)+1)-values (2*(r+2^n*c))) (row/2)) := by
        funext c
        rw [mobiusCoefficients,ite_eq_right even]
        congr 1
        funext r
        congr 1 <;> congr 1 <;> rw [Nat.pow_succ] <;> grind
      rw [same]

/-- Full packed coefficient specification: row Mobius followed by column
Mobius. The row index is low. This explicitly states which source coefficient
representation the packed functional consumes. -/
def tensorMobius (n p : Nat) (values : Nat → Nat → K) (index : Nat) : K :=
  mobiusCoefficients p (fun col => mobiusCoefficients n (fun row => values row col) (index%2^n)) (index/2^n)

private theorem mobius_coefficients_congr (n : Nat) (a b : Nat → K) (same : ∀ i,i<2^n → a i=b i)
    (index : Nat) : mobiusCoefficients n a index=mobiusCoefficients n b index := by
  induction n generalizing a b index with
  | zero => exact same 0 (by decide)
  | succ n ih =>
    simp only [mobiusCoefficients]
    split
    · apply ih
      intro i hi
      apply same
      rw [Nat.pow_succ]
      omega
    · apply ih
      intro i hi
      rw [same (2*i+1) (by rw [Nat.pow_succ]; omega),same (2*i) (by rw [Nat.pow_succ]; omega)]

/-- Full packed Mobius coefficients equal the tensor specification.
Values outside the row cube are immaterial. -/
theorem packed_mobius_tensor (n p : Nat) (values : Nat → Nat → K) (index : Nat) :
    mobiusCoefficients (n+p) (fun i => values (i%2^n) (i/2^n)) index=tensorMobius n p values index := by
  have rows : index%2^n<2^n := Nat.mod_lt _ (Nat.two_pow_pos n)
  have rebuild : index%2^n+2^n*(index/2^n)=index := Nat.mod_add_div _ _
  have split := mobius_split_axes n p (fun i => values (i%2^n) (i/2^n))
    (index%2^n) (index/2^n) rows
  rw [rebuild] at split
  rw [split]
  unfold tensorMobius
  congr 1
  funext col
  apply mobius_coefficients_congr
  intro row hr
  have hd : (row+2^n*col)/2^n=col := by
    rw [Nat.add_mul_div_left row col (Nat.two_pow_pos n),Nat.div_eq_of_lt hr,Nat.zero_add]
  have hm : (row+2^n*col)%2^n=row := by simp [Nat.add_mod,Nat.mod_eq_of_lt hr]
  rw [hd,hm]

private theorem tensor_mobius_index (n p row col : Nat) (values : Nat → Nat → K)
    (bound : row<2^n) : tensorMobius n p values (row+2^n*col)=
      mobiusCoefficients p (fun col => mobiusCoefficients n (fun row => values row col) row) col := by
  have hd : (row+2^n*col)/2^n=col := by
    rw [Nat.add_mul_div_left row col (Nat.two_pow_pos n),Nat.div_eq_of_lt bound,Nat.zero_add]
  have hm : (row+2^n*col)%2^n=row := by simp [Nat.add_mod,Nat.mod_eq_of_lt bound]
  simp only [tensorMobius,hd,hm]

/-- Tensor duality for arbitrary row and column functionals, without assuming
that either weight family is a Boolean equality basis. -/
theorem tensor_dual_mobius_dot (n p : Nat) (columns rows : Nat → K) (values : Nat → Nat → K) :
    cubeSum p (fun col => cubeSum n (fun row =>
      (upperZeta p columns col*upperZeta n rows row)*
        mobiusCoefficients p (fun col => mobiusCoefficients n (fun row => values row col) row) col))=
      cubeSum p (fun col => columns col*cubeSum n (fun row => rows row*values row col)) := by
  rw [cube_commute]
  have inner : ∀ row,cubeSum p (fun col =>
      (upperZeta p columns col*upperZeta n rows row)*
        mobiusCoefficients p (fun col => mobiusCoefficients n (fun row => values row col) row) col)=
      cubeSum p (fun col => columns col*(upperZeta n rows row*mobiusCoefficients n (fun row => values row col) row)) := by
    intro row
    have left : (fun col => (upperZeta p columns col*upperZeta n rows row)*
        mobiusCoefficients p (fun col => mobiusCoefficients n (fun row => values row col) row) col)=
        (fun col => upperZeta n rows row*(upperZeta p columns col*
          mobiusCoefficients p (fun col => mobiusCoefficients n (fun row => values row col) row) col)) := by funext col; grind
    rw [left,cube_scale,dual_mobius_dot]
    rw [←cube_scale]
    apply cube_congr
    intro col hc
    grind
  have same := funext inner
  rw [same,cube_commute]
  apply cube_congr
  intro col hc
  rw [cube_scale,dual_mobius_dot]

/-- Packed current/cyclic-next functional, with a shared original table and
column-major coefficients. Padding is represented by zero table columns and
zero current/next column weights, not extra independently selected claims. -/
theorem packed_current_next_functional (n p : Nat) (point current next : Nat → K)
    (values : Nat → Nat → K) (polynomial : Poly K)
    (coefficients : ∀ i,i<2^(n+p) → polynomial.coeff i=tensorMobius n p values i) :
    coefficientTableFunctional (n+p) [packedDualWeight n p point current next] [polynomial]=
      cubeSum p (fun col => current col*genericRowMLE n (fun row => values row col) point+
        next col*genericRowNextMLE n (fun row => values row col) point) := by
  have start : coefficientTableFunctional (n+p) [packedDualWeight n p point current next] [polynomial]=
      cubeSum (n+p) (fun i => packedDualWeight n p point current next i*tensorMobius n p values i) := by
    unfold coefficientTableFunctional cubeSum
    congr 1
    apply List.map_congr_left
    intro i hi
    simp only [List.map_cons,List.map_nil,weightedLaneValues]
    rw [coefficients i (List.mem_range.mp hi)]
    grind
  rw [start,cube_sum_split_axes]
  have rectangular : cubeSum p (fun col => cubeSum n (fun row =>
      packedDualWeight n p point current next (row+2^n*col)*tensorMobius n p values (row+2^n*col)))=
    cubeSum p (fun col => cubeSum n (fun row =>
      (upperZeta p current col*upperZeta n (rowEqualityWeight n point) row+
        upperZeta p next col*upperZeta n (cyclicRowWeight n point) row)*
        mobiusCoefficients p (fun col => mobiusCoefficients n (fun row => values row col) row) col)) := by
    apply cube_congr
    intro col hc
    apply cube_congr
    intro row hr
    rw [packed_dual_weight_index n p row col point current next hr,tensor_mobius_index n p row col values hr]
  rw [rectangular]
  have distribute : ∀ col,cubeSum n (fun row =>
      (upperZeta p current col*upperZeta n (rowEqualityWeight n point) row+
        upperZeta p next col*upperZeta n (cyclicRowWeight n point) row)*
        mobiusCoefficients p (fun col => mobiusCoefficients n (fun row => values row col) row) col)=
      cubeSum n (fun row => (upperZeta p current col*upperZeta n (rowEqualityWeight n point) row)*
        mobiusCoefficients p (fun col => mobiusCoefficients n (fun row => values row col) row) col)+
      cubeSum n (fun row => (upperZeta p next col*upperZeta n (cyclicRowWeight n point) row)*
        mobiusCoefficients p (fun col => mobiusCoefficients n (fun row => values row col) row) col) := by
    intro col
    rw [←cube_add]
    apply cube_congr
    intro row hr
    grind
  rw [funext distribute,cube_add,tensor_dual_mobius_dot,tensor_dual_mobius_dot,←cube_add]
  apply cube_congr
  intro col hc
  rw [row_equality_dot]
  have nextRow : cubeSum n (fun row => cyclicRowWeight n point row*values row col)=
      genericRowNextMLE n (fun row => values row col) point := by
    change ((List.range (2^n)).map (fun row => rowEqualityWeight n point ((row+2^n-1)%(2^n))*values row col)).sum=_
    rw [cyclic_predecessor_dot (2^n) (Nat.two_pow_pos n)]
    exact row_equality_dot n point _
  rw [nextRow]

/-- Direct specialization to one full-dimension Mobius transform of the
column-major packed source, rather than an assumed two-stage transform. -/
theorem packed_full_mobius_functional (n p : Nat) (point current next : Nat → K)
    (values : Nat → Nat → K) (polynomial : Poly K)
    (coefficients : ∀ i,i<2^(n+p) → polynomial.coeff i=
      mobiusCoefficients (n+p) (fun j => values (j%2^n) (j/2^n)) i) :
    coefficientTableFunctional (n+p) [packedDualWeight n p point current next] [polynomial]=
      cubeSum p (fun col => current col*genericRowMLE n (fun row => values row col) point+
        next col*genericRowNextMLE n (fun row => values row col) point) := by
  apply packed_current_next_functional n p point current next values polynomial
  intro i hi
  rw [coefficients i hi,packed_mobius_tensor]

end NearCompression
