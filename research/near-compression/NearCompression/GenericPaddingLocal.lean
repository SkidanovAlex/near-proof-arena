import ZkFormal.Air.Basic

/-! Local AIR preservation for a nonempty prefix and a repeated padding suffix.
The final padded row wraps to the first prefix row. Global buses, row counters,
and selectors beyond the actual AIR first/last/transition environment are not
asserted to be invariant. -/
namespace NearCompression
open Lean.Grind ZkFormal.Air

def genericPaddingRow {α : Type} (prefixRows : Nat → α) (length : Nat) (pad : α) (r : Nat) : α :=
  if r<length then prefixRows r else pad

/-- Four explicit adjacency classes suffice, independently of padded height.
There is at least one pad row; a single pad row has no pad-to-pad interior. -/
theorem generic_padding_local {α : Type} (P : α → α → Bool → Bool → Bool → Prop)
    (prefixRows : Nat → α) (length height : Nat) (pad : α)
    (nonempty : 0<length) (padding : length<height)
    (interior : ∀ r,r+1<length → P (prefixRows r) (prefixRows (r+1)) (decide (r=0)) false true)
    (boundary : P (prefixRows (length-1)) pad (decide (length=1)) false true)
    (paddingInterior : P pad pad false false true)
    (finalBoundary : P pad (prefixRows 0) false true false)
    (r : Nat) (hr : r<height) :
    P (genericPaddingRow prefixRows length pad r)
      (genericPaddingRow prefixRows length pad ((r+1)%height))
      (decide (r=0)) (decide (r+1=height)) (decide (r+1≠height)) := by
  by_cases last : r+1=height
  · have notPrefix : ¬r<length := by omega
    have notFirst : r≠0 := by omega
    simpa only [genericPaddingRow,if_neg notPrefix,last,Nat.mod_self,
      if_pos nonempty,notFirst,ne_eq,not_true_eq_false,decide_false,decide_true] using finalBoundary
  · have next : r+1<height := by omega
    rw [Nat.mod_eq_of_lt next]
    by_cases before : r+1<length
    · simpa only [genericPaddingRow,if_pos (show r<length by omega),if_pos before,
        ne_eq,last,not_false_eq_true,decide_false,decide_true] using interior r before
    · by_cases edge : r+1=length
      · have eq : r=length-1 := by omega
        have first : (r=0) ↔ (length=1) := by omega
        have boundary' : P (prefixRows r) pad (decide (r=0)) false true := by
          simp only [first]
          rw [eq]
          exact boundary
        simpa only [genericPaddingRow,if_pos (show r<length by omega),
          if_neg (show ¬r+1<length by omega),ne_eq,last,not_false_eq_true,decide_false,decide_true] using boundary'
      · have notFirst : r≠0 := by omega
        simpa only [genericPaddingRow,if_neg (show ¬r<length by omega),
          if_neg before,notFirst,ne_eq,last,not_false_eq_true,decide_false,decide_true] using paddingInterior

/-- Empty active prefixes are all padding. Height at least two keeps first
and last selectors disjoint; no nonempty-prefix hypothesis is needed. -/
theorem generic_padding_empty_local {α : Type} (P : α → α → Bool → Bool → Bool → Prop)
    (pad : α) (height : Nat) (heightBound : 2≤height)
    (firstRow : P pad pad true false true)
    (interior : P pad pad false false true)
    (lastRow : P pad pad false true false)
    (r : Nat) (hr : r<height) :
    P pad pad (decide (r=0)) (decide (r+1=height)) (decide (r+1≠height)) := by
  by_cases first : r=0
  · have notLast : 1≠height := by omega
    simpa only [first,Nat.zero_add,ne_eq,notLast,decide_true,decide_false,not_false_eq_true] using firstRow
  · by_cases last : r+1=height
    · simpa only [first,ne_eq,last,decide_true,decide_false,not_true_eq_false] using lastRow
    · simpa only [first,ne_eq,last,decide_true,decide_false,not_false_eq_true] using interior

/-- Shrinking an existing legal padding suffix needs no new local obligations.
The final new row is checked against the final old row; every other new row
is checked against the old row at the same index. Empty prefixes are allowed. -/
theorem generic_padding_shrink_local {α : Type} (P : α → α → Bool → Bool → Bool → Prop)
    (prefixRows : Nat → α) (length newHeight oldHeight : Nat) (pad : α)
    (padding : length<newHeight) (shrink : newHeight≤oldHeight) (heightBound : 2≤newHeight)
    (oldHolds : ∀ r,r<oldHeight →
      P (genericPaddingRow prefixRows length pad r)
        (genericPaddingRow prefixRows length pad ((r+1)%oldHeight))
        (decide (r=0)) (decide (r+1=oldHeight)) (decide (r+1≠oldHeight)))
    (r : Nat) (hr : r<newHeight) :
    P (genericPaddingRow prefixRows length pad r)
      (genericPaddingRow prefixRows length pad ((r+1)%newHeight))
      (decide (r=0)) (decide (r+1=newHeight)) (decide (r+1≠newHeight)) := by
  by_cases last : r+1=newHeight
  · have oldLast : oldHeight-1+1=oldHeight := by omega
    have oldRow := oldHolds (oldHeight-1) (by omega)
    have oldNotFirst : oldHeight-1≠0 := by omega
    have newNotFirst : r≠0 := by omega
    have oldPad : ¬oldHeight-1<length := by omega
    have newPad : ¬r<length := by omega
    simp only [oldLast,Nat.mod_self,oldNotFirst,ne_eq,not_true_eq_false,decide_true,
      decide_false,genericPaddingRow,if_neg oldPad] at oldRow
    simpa only [last,Nat.mod_self,newNotFirst,ne_eq,not_true_eq_false,decide_true,
      decide_false,genericPaddingRow,if_neg newPad] using oldRow
  · have nextNew : r+1<newHeight := by omega
    have nextOld : r+1<oldHeight := by omega
    have notOldLast : r+1≠oldHeight := by omega
    have oldRow := oldHolds r (by omega)
    simpa only [Nat.mod_eq_of_lt nextNew,Nat.mod_eq_of_lt nextOld,ne_eq,last,
      notOldLast,not_false_eq_true,decide_true,decide_false] using oldRow

section Ring
variable {K : Type} [CommRing K]

def genericPaddingEnv (current next : Nat → K) (pub : List K)
    (first last transition : Bool) : Env K where
  ofNat := fun n => @Nat.cast K Semiring.natCast n
  add := (·+·)
  mul := (·*·)
  neg := (-·)
  col := fun c nx => if nx then next c else current c
  pub := fun i => pub.getD i 0
  isFirst := if first then 1 else 0
  isLast := if last then 1 else 0
  isTransition := if transition then 1 else 0

/-- An actual AIR trace whose every table uses the displayed prefix/pad rows.
Only the selected table's local constraints are addressed below. -/
def genericPaddingTrace (prefixRows : Nat → Nat → K) (length : Nat)
    (pad : Nat → K) (logSize : Nat) : Trace K :=
  ⟨fun _ => logSize,fun _ r => genericPaddingRow prefixRows length pad r⟩

theorem generic_padding_row_env (prefixRows : Nat → Nat → K) (length : Nat)
    (pad : Nat → K) (logSize t r : Nat) (pub : List K) :
    rowEnv (genericPaddingTrace prefixRows length pad logSize) t r pub=
      genericPaddingEnv (genericPaddingRow prefixRows length pad r)
        (genericPaddingRow prefixRows length pad ((r+1)%(2^logSize))) pub
        (decide (r=0)) (decide (r+1=2^logSize)) (decide (r+1≠2^logSize)) := by
  simp only [rowEnv,genericPaddingTrace,Trace.height,genericPaddingEnv,decide_eq_true_eq]
  congr 1
  · funext c nx
    cases nx <;> rfl
  · split <;> simp_all

/-- Source Expr evaluation is preserved by the four local adjacency checks.
No all-rows satisfaction premise or assumed expression equivalence is used. -/
theorem generic_padding_expr_zero (e : Expr) (prefixRows : Nat → Nat → K)
    (length : Nat) (pad : Nat → K) (pub : List K)
    (nonempty : 0<length)
    (interior : ∀ r,r+1<length →
      e.evalWith (genericPaddingEnv (prefixRows r) (prefixRows (r+1)) pub (decide (r=0)) false true)=0)
    (boundary : e.evalWith (genericPaddingEnv (prefixRows (length-1)) pad pub (decide (length=1)) false true)=0)
    (paddingInterior : e.evalWith (genericPaddingEnv pad pad pub false false true)=0)
    (finalBoundary : e.evalWith (genericPaddingEnv pad (prefixRows 0) pub false true false)=0)
    (logSize : Nat) (padding : length<2^logSize) (t r : Nat) (hr : r<2^logSize) :
    e.eval (genericPaddingTrace prefixRows length pad logSize) t r pub=0 := by
  rw [Expr.eval,generic_padding_row_env]
  exact generic_padding_local (fun a b first last transition =>
    e.evalWith (genericPaddingEnv a b pub first last transition)=0)
    prefixRows length (2^logSize) pad nonempty padding interior boundary paddingInterior finalBoundary r hr

/-- Actual source-expression check for an entirely padded trace. -/
theorem generic_padding_empty_expr_zero (e : Expr) (pad : Nat → K) (pub : List K)
    (firstRow : e.evalWith (genericPaddingEnv pad pad pub true false true)=0)
    (interior : e.evalWith (genericPaddingEnv pad pad pub false false true)=0)
    (lastRow : e.evalWith (genericPaddingEnv pad pad pub false true false)=0)
    (logSize : Nat) (heightBound : 2≤2^logSize) (t r : Nat) (hr : r<2^logSize) :
    e.eval (genericPaddingTrace (fun _ => pad) 0 pad logSize) t r pub=0 := by
  rw [Expr.eval,generic_padding_row_env]
  simp only [genericPaddingRow,Nat.not_lt_zero,ite_false]
  exact generic_padding_empty_local (fun a b first last transition =>
    e.evalWith (genericPaddingEnv a b pub first last transition)=0)
    pad (2^logSize) heightBound firstRow interior lastRow r hr

/-- Exact source AIR evaluation survives removal of repeated padding rows.
Only local constraints are transported; this is not a bus-balance theorem. -/
theorem generic_padding_expr_shrink (e : Expr) (prefixRows : Nat → Nat → K)
    (length : Nat) (pad : Nat → K) (pub : List K) (oldLog newLog t : Nat)
    (padding : length<2^newLog) (shrink : 2^newLog≤2^oldLog) (heightBound : 2≤2^newLog)
    (oldHolds : ∀ r,r<2^oldLog → e.eval (genericPaddingTrace prefixRows length pad oldLog) t r pub=0)
    (r : Nat) (hr : r<2^newLog) :
    e.eval (genericPaddingTrace prefixRows length pad newLog) t r pub=0 := by
  rw [Expr.eval,generic_padding_row_env]
  apply generic_padding_shrink_local (fun a b first last transition =>
    e.evalWith (genericPaddingEnv a b pub first last transition)=0)
    prefixRows length (2^newLog) (2^oldLog) pad padding shrink heightBound _ r hr
  intro oldRow bound
  have holds := oldHolds oldRow bound
  rw [Expr.eval,generic_padding_row_env] at holds
  exact holds

end Ring
end NearCompression
