import NearCompression.FunctionalBatchRepresentative

/-! Exact finite dual transforms, in little-endian coefficient order.
These recursive transforms specify the mathematical lower/upper zeta maps;
identification with an in-place array implementation is a separate refinement. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def cubeSum (n : Nat) (f : Nat → K) : K := ((List.range (2^n)).map f).sum

def lowerZeta : Nat → (Nat → K) → Nat → K
  | 0,c,_ => c 0
  | n+1,c,i => if i%2=0 then lowerZeta n (fun j => c (2*j)) (i/2)
      else lowerZeta n (fun j => c (2*j)+c (2*j+1)) (i/2)

def upperZeta : Nat → (Nat → K) → Nat → K
  | 0,w,_ => w 0
  | n+1,w,i => if i%2=0 then upperZeta n (fun j => w (2*j)+w (2*j+1)) (i/2)
      else upperZeta n (fun j => w (2*j+1)) (i/2)

def mobiusCoefficients : Nat → (Nat → K) → Nat → K
  | 0,v,_ => v 0
  | n+1,v,i => if i%2=0 then mobiusCoefficients n (fun j => v (2*j)) (i/2)
      else mobiusCoefficients n (fun j => v (2*j+1)-v (2*j)) (i/2)

private theorem sum_add (indices : List Nat) (f g : Nat → K) :
    (indices.map (fun i => f i+g i)).sum=(indices.map f).sum+(indices.map g).sum := by
  induction indices with
  | nil => simp; grind
  | cons i indices ih => simp only [List.map_cons,List.sum_cons,ih]; grind

private theorem sum_scale (indices : List Nat) (a : K) (f : Nat → K) :
    (indices.map (fun i => a*f i)).sum=a*(indices.map f).sum := by
  induction indices with
  | nil => simp; grind
  | cons i indices ih => simp only [List.map_cons,List.sum_cons,ih]; grind

private theorem sum_pairs (N : Nat) (f : Nat → K) :
    ((List.range (2*N)).map f).sum=
      ((List.range N).map (fun i => f (2*i)+f (2*i+1))).sum := by
  induction N generalizing f with
  | zero => rfl
  | succ N ih =>
    have size : 2*(N+1)=2*N+1+1 := by omega
    rw [size,List.range_succ_eq_map,List.map_cons,List.map_map,
      List.range_succ_eq_map,List.map_cons,List.map_map]
    simp only [Function.comp_def,List.sum_cons]
    rw [ih]
    rw [List.range_succ_eq_map,List.map_cons,List.map_map]
    simp only [Function.comp_def,List.sum_cons]
    have same : (fun i => f (2*i+1+1)+f (2*i+1+1+1))=
        (fun i => f (2*(i+1))+f (2*(i+1)+1)) := by funext i; congr 2 <;> omega
    rw [same]
    grind

theorem cube_sum_split (n : Nat) (f : Nat → K) :
    cubeSum (n+1) f=cubeSum n (fun i => f (2*i))+cubeSum n (fun i => f (2*i+1)) := by
  unfold cubeSum
  rw [Nat.pow_succ,Nat.mul_comm (2^n),sum_pairs,sum_add]

theorem lower_zeta_add (n : Nat) (a b : Nat → K) (i : Nat) :
    lowerZeta n (fun j => a j+b j) i=lowerZeta n a i+lowerZeta n b i := by
  induction n generalizing a b i with
  | zero => rfl
  | succ n ih =>
    simp only [lowerZeta]
    split
    · exact ih _ _ _
    · have eq : (fun j => a (2*j)+b (2*j)+(a (2*j+1)+b (2*j+1)))=
          (fun j => (a (2*j)+a (2*j+1))+(b (2*j)+b (2*j+1))) := by funext j; grind
      rw [eq,ih]

theorem upper_zeta_add (n : Nat) (a b : Nat → K) (i : Nat) :
    upperZeta n (fun j => a j+b j) i=upperZeta n a i+upperZeta n b i := by
  induction n generalizing a b i with
  | zero => rfl
  | succ n ih =>
    simp only [upperZeta]
    split
    · have eq : (fun j => a (2*j)+b (2*j)+(a (2*j+1)+b (2*j+1)))=
          (fun j => (a (2*j)+a (2*j+1))+(b (2*j)+b (2*j+1))) := by funext j; grind
      rw [eq,ih]
    · exact ih _ _ _

/-- Upper zeta is the transpose of coefficient evaluation on Boolean rows. -/
theorem dual_zeta_dot (n : Nat) (weights coefficients : Nat → K) :
    cubeSum n (fun i => upperZeta n weights i*coefficients i)=
      cubeSum n (fun i => weights i*lowerZeta n coefficients i) := by
  induction n generalizing weights coefficients with
  | zero => simp [cubeSum,upperZeta,lowerZeta]
  | succ n ih =>
    rw [cube_sum_split,cube_sum_split]
    have evenmod : ∀ i,(2*i)%2=0 := by intro i; omega
    have oddmod : ∀ i,(2*i+1)%2=1 := by intro i; omega
    have evendiv : ∀ i,(2*i)/2=i := by intro i; omega
    have odddiv : ∀ i,(2*i+1)/2=i := by intro i; omega
    simp only [upperZeta,lowerZeta,evenmod,oddmod,evendiv,odddiv,Nat.reduceEqDiff,ite_true,ite_false]
    simp only [upper_zeta_add,lower_zeta_add]
    have distribution : ∀ a b c : Nat → K,
        cubeSum n (fun i => (a i+b i)*c i)=cubeSum n (fun i => a i*c i)+cubeSum n (fun i => b i*c i) := by
      intro a b c
      have eq : (fun i => (a i+b i)*c i)=(fun i => a i*c i+b i*c i) := by funext i; grind
      rw [eq]
      exact sum_add _ _ _
    rw [distribution,ih,ih,ih]
    have eq : (fun i => weights (2*i+1)*(lowerZeta n (fun j => coefficients (2*j)) i+
        lowerZeta n (fun j => coefficients (2*j+1)) i))=
      (fun i => weights (2*i+1)*lowerZeta n (fun j => coefficients (2*j)) i+
        weights (2*i+1)*lowerZeta n (fun j => coefficients (2*j+1)) i) := by funext i; grind
    rw [eq]
    unfold cubeSum
    rw [sum_add]
    grind

/-- The inverse transform really reconstructs the supplied Boolean table. -/
theorem lower_zeta_mobius (n : Nat) (values : Nat → K) (i : Nat) (bound : i<2^n) :
    lowerZeta n (mobiusCoefficients n values) i=values i := by
  induction n generalizing values i with
  | zero =>
    have h : i=0 := by simpa using bound
    subst i
    rfl
  | succ n ih =>
    have half : i/2<2^n := by rw [Nat.pow_succ] at bound; omega
    have even : (fun j => mobiusCoefficients (n+1) values (2*j))=
        mobiusCoefficients n (fun j => values (2*j)) := by
      funext j
      have hm : (2*j)%2=0 := by omega
      have hd : (2*j)/2=j := by omega
      simp [mobiusCoefficients,hm,hd]
    have odd : (fun j => mobiusCoefficients (n+1) values (2*j+1))=
        mobiusCoefficients n (fun j => values (2*j+1)-values (2*j)) := by
      funext j
      have hm : (2*j+1)%2=1 := by omega
      have hd : (2*j+1)/2=j := by omega
      simp [mobiusCoefficients,hm,hd]
    rw [lowerZeta]
    split
    · rw [even,ih _ _ half]
      congr 1
      omega
    · have sumEq : (fun j => mobiusCoefficients (n+1) values (2*j)+mobiusCoefficients (n+1) values (2*j+1))=
          (fun j => mobiusCoefficients n (fun j => values (2*j)) j+
            mobiusCoefficients n (fun j => values (2*j+1)-values (2*j)) j) := by
        funext j
        rw [congrFun even j,congrFun odd j]
      rw [sumEq,lower_zeta_add,ih _ _ half,ih _ _ half]
      have index : 2*(i/2)+1=i := by omega
      rw [index]
      grind

theorem dual_mobius_dot (n : Nat) (weights values : Nat → K) :
    cubeSum n (fun i => upperZeta n weights i*mobiusCoefficients n values i)=
      cubeSum n (fun i => weights i*values i) := by
  rw [dual_zeta_dot]
  unfold cubeSum
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [lower_zeta_mobius n values i (List.mem_range.mp hi)]

def rowEqualityWeight : Nat → (Nat → K) → Nat → K
  | 0,_,_ => 1
  | n+1,point,i => (if i%2=0 then 1-point 0 else point 0)*
      rowEqualityWeight n (fun j => point (j+1)) (i/2)

/-- The row equality basis is exactly the existing AIR row interpolation. -/
theorem row_equality_dot (n : Nat) (point values : Nat → K) :
    cubeSum n (fun i => rowEqualityWeight n point i*values i)=genericRowMLE n values point := by
  induction n generalizing point values with
  | zero => simp [cubeSum,rowEqualityWeight,genericRowMLE]; grind
  | succ n ih =>
    rw [cube_sum_split]
    have evenmod : ∀ i,(2*i)%2=0 := by intro i; omega
    have oddmod : ∀ i,(2*i+1)%2=1 := by intro i; omega
    have evendiv : ∀ i,(2*i)/2=i := by intro i; omega
    have odddiv : ∀ i,(2*i+1)/2=i := by intro i; omega
    simp only [rowEqualityWeight,evenmod,oddmod,evendiv,odddiv,Nat.reduceEqDiff,ite_true,ite_false]
    have move : ∀ a : K,∀ f g : Nat → K,
        cubeSum n (fun i => (a*f i)*g i)=a*cubeSum n (fun i => f i*g i) := by
      intro a f g
      have same : (fun i => (a*f i)*g i)=(fun i => a*(f i*g i)) := by funext i; grind
      rw [same]
      exact sum_scale _ _ _
    rw [move,move,ih,ih]
    rfl

theorem current_dual_mobius (n : Nat) (point values : Nat → K) :
    cubeSum n (fun i => upperZeta n (rowEqualityWeight n point) i*mobiusCoefficients n values i)=
      genericRowMLE n values point := by
  rw [dual_mobius_dot,row_equality_dot]

private theorem sum_append (a b : List K) : (a++b).sum=a.sum+b.sum := by
  induction a with
  | nil => simp only [List.nil_append,List.sum_nil]; grind
  | cons x xs ih => simp only [List.cons_append,List.sum_cons,ih]; grind

/-- Exact cyclic permutation of a finite sum; no off-cube challenge addition. -/
theorem cyclic_sum_successor (N : Nat) (positive : 0<N) (f : Nat → K) :
    ((List.range N).map (fun i => f ((i+1)%N))).sum=((List.range N).map f).sum := by
  cases N with
  | zero => omega
  | succ m =>
    have expand : ((List.range (m+1)).map (fun i => f ((i+1)%(m+1)))).sum=
        ((List.range m).map (fun i => f ((i+1)%(m+1)))).sum+f 0 := by
      rw [List.range_succ,List.map_append,sum_append]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.mod_self]
      grind
    rw [expand]
    have same : ((List.range m).map (fun i => f ((i+1)%(m+1))))=
        (List.range m).map (fun i => f (i+1)) := by
      apply List.map_congr_left
      intro i hi
      rw [Nat.mod_eq_of_lt (by have h := List.mem_range.mp hi; omega)]
    rw [same,List.range_succ_eq_map,List.map_cons,List.map_map]
    simp only [List.sum_cons,Function.comp_def]
    grind

theorem cyclic_predecessor_dot (N : Nat) (positive : 0<N) (weights values : Nat → K) :
    ((List.range N).map (fun i => weights ((i+N-1)%N)*values i)).sum=
      ((List.range N).map (fun i => weights i*values ((i+1)%N))).sum := by
  have perm := cyclic_sum_successor N positive (fun j => weights ((j+N-1)%N)*values j)
  rw [←perm]
  congr 1
  apply List.map_congr_left
  intro i hi
  have bound := List.mem_range.mp hi
  have inverse : (((i+1)%N+N-1)%N)=i := by
    by_cases last : i+1=N
    · rw [last,Nat.mod_self,Nat.zero_add,Nat.mod_eq_of_lt (by omega : N-1<N)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega : i+1<N)]
      have eq : i+1+N-1=i+N := by omega
      rw [eq,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod,Nat.mod_eq_of_lt bound]
  rw [inverse]

def cyclicRowWeight (n : Nat) (point : Nat → K) (i : Nat) : K :=
  rowEqualityWeight n point ((i+2^n-1)%(2^n))

/-- The upper-zeta of eq(point,row-1) opens the actual cyclic-next row MLE. -/
theorem next_dual_mobius (n : Nat) (point values : Nat → K) :
    cubeSum n (fun i => upperZeta n (cyclicRowWeight n point) i*mobiusCoefficients n values i)=
      genericRowNextMLE n values point := by
  rw [dual_mobius_dot]
  change ((List.range (2^n)).map (fun i => rowEqualityWeight n point ((i+2^n-1)%(2^n))*values i)).sum=_
  rw [cyclic_predecessor_dot (2^n) (Nat.two_pow_pos n)]
  exact row_equality_dot n point _

/-- Reusable one-lane current/next linear functional. The coefficients must be
those of the same original Boolean table; a separate source commitment cannot
be substituted for the next-row term. -/
theorem current_next_dual_mobius (n : Nat) (point values : Nat → K) (a b : K) :
    cubeSum n (fun i => (a*upperZeta n (rowEqualityWeight n point) i+
      b*upperZeta n (cyclicRowWeight n point) i)*mobiusCoefficients n values i)=
      a*genericRowMLE n values point+b*genericRowNextMLE n values point := by
  have eq : (fun i => (a*upperZeta n (rowEqualityWeight n point) i+
      b*upperZeta n (cyclicRowWeight n point) i)*mobiusCoefficients n values i)=
      (fun i => a*(upperZeta n (rowEqualityWeight n point) i*mobiusCoefficients n values i)+
        b*(upperZeta n (cyclicRowWeight n point) i*mobiusCoefficients n values i)) := by funext i; grind
  rw [eq]
  change ((List.range (2^n)).map _).sum=_
  rw [sum_add,sum_scale,sum_scale]
  rw [show ((List.range (2^n)).map (fun i => upperZeta n (rowEqualityWeight n point) i*
      mobiusCoefficients n values i)).sum=genericRowMLE n values point from current_dual_mobius n point values]
  rw [show ((List.range (2^n)).map (fun i => upperZeta n (cyclicRowWeight n point) i*
      mobiusCoefficients n values i)).sum=genericRowNextMLE n values point from next_dual_mobius n point values]

/-- Direct interface to the actual sumcheck coefficient functional for one lane.
Only bounded coefficient equality is needed, allowing canonical zero padding. -/
theorem current_next_coefficient_functional (n : Nat) (point values : Nat → K)
    (a b : K) (p : Poly K)
    (coefficients : ∀ i,i<2^n → p.coeff i=mobiusCoefficients n values i) :
    coefficientTableFunctional n
      [fun i => a*upperZeta n (rowEqualityWeight n point) i+b*upperZeta n (cyclicRowWeight n point) i] [p]=
      a*genericRowMLE n values point+b*genericRowNextMLE n values point := by
  have same : coefficientTableFunctional n
      [fun i => a*upperZeta n (rowEqualityWeight n point) i+b*upperZeta n (cyclicRowWeight n point) i] [p]=
      cubeSum n (fun i => (a*upperZeta n (rowEqualityWeight n point) i+
        b*upperZeta n (cyclicRowWeight n point) i)*mobiusCoefficients n values i) := by
    unfold coefficientTableFunctional cubeSum
    congr 1
    apply List.map_congr_left
    intro i hi
    simp only [List.map_cons,List.map_nil,weightedLaneValues]
    rw [coefficients i (List.mem_range.mp hi)]
    grind
  rw [same,current_next_dual_mobius]

end NearCompression
