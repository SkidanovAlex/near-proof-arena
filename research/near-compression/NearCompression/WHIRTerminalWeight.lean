import ZkFormal.Air.Basic

/-! Terminal algebra of verify_whir_scheduled.py. Coefficients use little-endian
monomial tensor order, not an evaluation table. No PCS binding, Fiat--Shamir,
query soundness, or security theorem is asserted here. -/
set_option autoImplicit false
namespace NearCompression
open Lean.Grind
variable {K : Type} [CommRing K]

def whirEq (x y : K) : K := (1-x)*(1-y)+x*y

def whirTensor : List K → (Nat → K) → K
  | [],c => c 0
  | x::xs,c => whirTensor xs (fun i => c (2*i)) + x*whirTensor xs (fun i => c (2*i+1))

def whirCubeSum : Nat → (List K → K) → K
  | 0,f => f []
  | n+1,f => whirCubeSum n (fun xs => f (0::xs)) + whirCubeSum n (fun xs => f (1::xs))

def whirKernel : List K → List K → K
  | [],[] => 1
  | x::xs,y::ys => whirEq x y * whirKernel xs ys
  | _,_ => 0

theorem whir_cube_congr (n : Nat) (f g : List K → K)
    (h : ∀ xs,xs.length=n → f xs=g xs) : whirCubeSum n f=whirCubeSum n g := by
  induction n generalizing f g with
  | zero => exact h [] rfl
  | succ n ih =>
    simp only [whirCubeSum]
    rw [ih _ _ (fun xs hx => h (0::xs) (by simp [hx])),
        ih _ _ (fun xs hx => h (1::xs) (by simp [hx]))]

theorem whir_cube_scale (n : Nat) (w : K) (f : List K → K) :
    whirCubeSum n (fun xs => w*f xs)=w*whirCubeSum n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [whirCubeSum,ih]; grind

theorem whir_cube_add (n : Nat) (f g : List K → K) :
    whirCubeSum n (fun xs => f xs+g xs)=whirCubeSum n f+whirCubeSum n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp only [whirCubeSum,ih]; grind

/-- The verifier's final tensor polynomial is reproduced by its Boolean
equality-weighted sum, with exactly the little-endian coefficient ordering. -/
theorem whir_tensor_reproducing (point : List K) (c : Nat → K) :
    whirCubeSum point.length (fun bits => whirTensor bits c*whirKernel point bits)=
      whirTensor point c := by
  induction point generalizing c with
  | nil => simp only [List.length_nil,whirCubeSum,whirTensor,whirKernel]; grind
  | cons x xs ih =>
    simp only [List.length_cons,whirCubeSum,whirTensor,whirKernel]
    have a : (fun bits => (whirTensor bits (fun i => c (2*i))+0*whirTensor bits (fun i => c (2*i+1)))*
        (whirEq x 0*whirKernel xs bits)) =
      (fun bits => (1-x)*(whirTensor bits (fun i => c (2*i))*whirKernel xs bits)) := by
      funext bits; unfold whirEq; grind
    have b : (fun bits => (whirTensor bits (fun i => c (2*i))+1*whirTensor bits (fun i => c (2*i+1)))*
        (whirEq x 1*whirKernel xs bits)) =
      (fun bits => x*((whirTensor bits (fun i => c (2*i))*whirKernel xs bits)+
        (whirTensor bits (fun i => c (2*i+1))*whirKernel xs bits))) := by
      funext bits; unfold whirEq; grind
    rw [a,b,whir_cube_scale,whir_cube_scale,whir_cube_add,ih,ih]
    grind
theorem whir_tensor_linear (point : List K) (a b : Nat → K) (w : K) :
    whirTensor point (fun i => a i+w*b i)=whirTensor point a+w*whirTensor point b := by
  induction point generalizing a b with
  | nil => rfl
  | cons x xs ih => simp only [whirTensor,ih]; grind

/-- Matches one adjacent-pair iteration of Python tensor_eval. -/
theorem whir_tensor_fold (x : K) (xs : List K) (c : Nat → K) :
    whirTensor (x::xs) c=whirTensor xs (fun i => c (2*i)+x*c (2*i+1)) := by
  rw [whir_tensor_linear]; rfl

def whirPowerPoint : K → Nat → List K
  | _,0 => []
  | a,n+1 => a::whirPowerPoint (a*a) n

def whirAdvance : K → Nat → K
  | a,0 => a
  | a,n+1 => whirAdvance (a*a) n

def whirPowerKernel : K → List K → K
  | _,[] => 1
  | a,x::xs => whirEq a x*whirPowerKernel (a*a) xs

theorem whir_power_length (a : K) (n : Nat) : (whirPowerPoint a n).length=n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [whirPowerPoint,ih]

theorem whir_power_kernel (a : K) (xs : List K) :
    whirPowerKernel a xs=whirKernel (whirPowerPoint a xs.length) xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp only [List.length_cons,whirPowerPoint,whirKernel,whirPowerKernel,ih]

/-- Squaring advances only through coordinates after the injection offset. -/
theorem whir_power_kernel_append (a : K) (pre tail : List K) :
    whirPowerKernel a (pre++tail)=whirPowerKernel a pre*
      whirPowerKernel (whirAdvance a pre.length) tail := by
  induction pre generalizing a with
  | nil => simp only [List.nil_append,List.length_nil,whirAdvance,whirPowerKernel]; grind
  | cons x xs ih =>
    simp only [List.cons_append,List.length_cons,whirPowerKernel,whirAdvance,ih]
    grind

/-- One concrete OOD/query contribution in the verifier's final weight loop.
The start index is measured in already drawn challenges, exactly as Python's
point[start:] and terms.append((len(challenges),anchor,power)). -/
theorem whir_injected_terminal (n : Nat) (c : Nat → K) (challenges : List K)
    (start : Nat) (anchor power : K) :
    whirCubeSum n (fun tail => whirTensor tail c *
      (power*whirPowerKernel anchor (challenges.drop start++tail))) =
    (power*whirPowerKernel anchor (challenges.drop start))*
      whirTensor (whirPowerPoint (whirAdvance anchor (challenges.drop start).length) n) c := by
  let a := whirAdvance anchor (challenges.drop start).length
  let w := power*whirPowerKernel anchor (challenges.drop start)
  have pointLength : (whirPowerPoint a n).length=n := whir_power_length a n
  calc
    _ = whirCubeSum n (fun tail => w*(whirTensor tail c*whirKernel (whirPowerPoint a n) tail)) := by
      apply whir_cube_congr
      intro tail htail
      rw [whir_power_kernel_append,whir_power_kernel (whirAdvance anchor (challenges.drop start).length) tail,htail]
      dsimp [a,w]; grind
    _ = w*whirTensor (whirPowerPoint a n) c := by
      have rep := whir_tensor_reproducing (whirPowerPoint a n) c
      rw [pointLength] at rep
      rw [whir_cube_scale,rep]
    _ = _ := rfl

structure WhirInjection (K : Type) where
  start : Nat
  anchor : K
  power : K

def whirInjectedWeight (challenges tail : List K) : List (WhirInjection K) → K
  | [] => 0
  | t::ts => t.power*whirPowerKernel t.anchor (challenges.drop t.start++tail)+
      whirInjectedWeight challenges tail ts

def whirInjectedTerminal (n : Nat) (c : Nat → K) (challenges : List K) : List (WhirInjection K) → K
  | [] => 0
  | t::ts => (t.power*whirPowerKernel t.anchor (challenges.drop t.start))*
      whirTensor (whirPowerPoint (whirAdvance t.anchor (challenges.drop t.start).length) n) c+
      whirInjectedTerminal n c challenges ts

theorem whir_cube_zero (n : Nat) : whirCubeSum n (fun _ : List K => 0)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [whirCubeSum,ih]; grind

/-- Arbitrarily many intermediate stages' OOD/query terms compose additively. -/
theorem whir_injected_terminal_list (n : Nat) (c : Nat → K) (challenges : List K)
    (terms : List (WhirInjection K)) :
    whirCubeSum n (fun tail => whirTensor tail c*whirInjectedWeight challenges tail terms)=
      whirInjectedTerminal n c challenges terms := by
  induction terms with
  | nil =>
    simp only [whirInjectedWeight,whirInjectedTerminal]
    have h : (fun tail => whirTensor tail c*(0:K))=(fun _ => 0) := by funext; grind
    rw [h,whir_cube_zero]
  | cons t ts ih =>
    simp only [whirInjectedWeight,whirInjectedTerminal]
    have h : (fun tail => whirTensor tail c*(t.power*whirPowerKernel t.anchor
        (challenges.drop t.start++tail)+whirInjectedWeight challenges tail ts))=
      (fun tail => whirTensor tail c*(t.power*whirPowerKernel t.anchor
        (challenges.drop t.start++tail))+whirTensor tail c*whirInjectedWeight challenges tail ts) := by
      funext; grind
    rw [h,whir_cube_add,whir_injected_terminal,ih]
theorem whir_kernel_append (left right tailLeft tailRight : List K)
    (same : left.length=right.length) :
    whirKernel (left++tailLeft) (right++tailRight)=whirKernel left right*whirKernel tailLeft tailRight := by
  induction left generalizing right with
  | nil =>
    have hr : right=[] := by cases right <;> simp_all
    subst right
    simp only [List.nil_append,whirKernel]; grind
  | cons x xs ih =>
    cases right with
    | nil => simp at same
    | cons y ys =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at same
      simp only [List.cons_append,whirKernel,ih ys same]
      grind

theorem whir_original_terminal (c : Nat → K) (zPrefix zTail challenges : List K)
    (same : zPrefix.length=challenges.length) :
    whirCubeSum zTail.length (fun tail => whirTensor tail c*
      whirKernel (zPrefix++zTail) (challenges++tail))=
    whirKernel zPrefix challenges*whirTensor zTail c := by
  have h : (fun tail => whirTensor tail c*whirKernel (zPrefix++zTail) (challenges++tail))=
    (fun tail => whirKernel zPrefix challenges*(whirTensor tail c*whirKernel zTail tail)) := by
    funext tail
    rw [whir_kernel_append _ _ _ _ same]
    grind
  rw [h,whir_cube_scale,whir_tensor_reproducing]

/-- Exact algebra of the verifier's final nested tail sum, including the
original opening weight and every intermediate OOD/query injection. This is
an identity of concrete operations, not a premise that a proof verified. -/
theorem whir_terminal_weight_identity (c : Nat → K) (zPrefix zTail challenges : List K)
    (same : zPrefix.length=challenges.length) (terms : List (WhirInjection K)) :
    whirCubeSum zTail.length (fun tail => whirTensor tail c*
      (whirKernel (zPrefix++zTail) (challenges++tail)+whirInjectedWeight challenges tail terms)) =
    whirKernel zPrefix challenges*whirTensor zTail c+
      whirInjectedTerminal zTail.length c challenges terms := by
  have h : (fun tail => whirTensor tail c*
      (whirKernel (zPrefix++zTail) (challenges++tail)+whirInjectedWeight challenges tail terms))=
    (fun tail => whirTensor tail c*whirKernel (zPrefix++zTail) (challenges++tail)+
      whirTensor tail c*whirInjectedWeight challenges tail terms) := by funext; grind
  rw [h,whir_cube_add,whir_original_terminal _ _ _ _ same,whir_injected_terminal_list]
/-- Literal point[start:] weighting in the scheduled Python verifier. -/
def whirScheduledWeight (point : List K) : List (WhirInjection K) → K
  | [] => 0
  | t::ts => t.power*whirPowerKernel t.anchor (point.drop t.start)+whirScheduledWeight point ts

theorem whir_scheduled_weight_split (challenges tail : List K) (terms : List (WhirInjection K))
    (offsets : ∀ t∈terms,t.start≤challenges.length) :
    whirScheduledWeight (challenges++tail) terms=whirInjectedWeight challenges tail terms := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    simp only [whirScheduledWeight,whirInjectedWeight]
    rw [List.drop_append_of_le_length (offsets t (by simp)),
      ih (fun t ht => offsets t (by simp [ht]))]

/-- Final loop identity with literal scheduled offset slicing. Its only shape
premises are equal prefix lengths and offsets within already drawn challenges. -/
theorem whir_scheduled_terminal_identity (c : Nat → K) (zPrefix zTail challenges : List K)
    (same : zPrefix.length=challenges.length) (terms : List (WhirInjection K))
    (offsets : ∀ t∈terms,t.start≤challenges.length) :
    whirCubeSum zTail.length (fun tail => whirTensor tail c*
      (whirKernel (zPrefix++zTail) (challenges++tail)+whirScheduledWeight (challenges++tail) terms)) =
    whirKernel zPrefix challenges*whirTensor zTail c+
      whirInjectedTerminal zTail.length c challenges terms := by
  simp only [whir_scheduled_weight_split challenges _ terms offsets]
  exact whir_terminal_weight_identity c zPrefix zTail challenges same terms
end NearCompression
