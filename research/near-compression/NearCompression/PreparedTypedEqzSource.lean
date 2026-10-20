import NearCompression.PreparedTypedSource
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def preparedTypedSelectedLimb (limb : Nat) : Expr :=
  preparedBalancedSum (fun i=>.mul (.col (32+(i+1)) false)
    (preparedCodeBits (preparedTypedStackBase i limb))) 3 0

def preparedTypedSelectedSum : Expr :=
  preparedBalancedSum preparedTypedSelectedLimb 2 0

def preparedTypedSelectedInverse : Expr :=
  .add (.mul preparedTypedSelectedSum (.col 1283 false)) (.neg (.add (.const 1) (.neg (.col 1284 false))))
def preparedTypedSelectedZero : Expr :=
  .add (.mul preparedTypedSelectedSum (.col 1284 false)) (.neg (.const 0))

private theorem eqz_at : ∀count:Fin 5,
    (preparedTypedLiteralExec count)[1563+66*(4-count.val)]?=some preparedTypedSelectedInverse ∧
    (preparedTypedLiteralExec count)[1564+66*(4-count.val)]?=some preparedTypedSelectedZero := by decide

theorem prepared_typed_selected_limb (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (sp limb : Nat) (hs : sp<9) (positive : 0<sp)
    (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    (preparedTypedSelectedLimb limb).eval tr t r pub=preparedTypedStackLimb (tr.cell t r) (sp-1) limb := by
  let word (i : Nat) := (preparedCodeBits (preparedTypedStackBase i limb)).eval tr t r pub
  change ((tr.cell t r 33*word 0+tr.cell t r 34*word 1)+
      (tr.cell t r 35*word 2+tr.cell t r 36*word 3))+
      ((tr.cell t r 37*word 4+tr.cell t r 38*word 5)+
      (tr.cell t r 39*word 6+tr.cell t r 40*word 7))=_
  have h1:=hot 1 (by decide);have h2:=hot 2 (by decide)
  have h3:=hot 3 (by decide);have h4:=hot 4 (by decide)
  have h5:=hot 5 (by decide);have h6:=hot 6 (by decide)
  have h7:=hot 7 (by decide);have h8:=hot 8 (by decide)
  rw [h1,h2,h3,h4,h5,h6,h7,h8]
  have choices : sp=1 ∨ sp=2 ∨ sp=3 ∨ sp=4 ∨ sp=5 ∨ sp=6 ∨ sp=7 ∨ sp=8:=by omega
  rcases choices with z|z|z|z|z|z|z|z <;> subst sp
  all_goals simp only [Nat.reduceEqDiff,ite_true,ite_false,Nat.reduceSub]
  all_goals simp only [word,prepared_code_bits_eval,Bool.false_eq_true,ite_false,preparedTypedStackLimb]
  all_goals grind

theorem prepared_typed_selected_sum (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (sp : Nat) (hs : sp<9) (positive : 0<sp)
    (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    preparedTypedSelectedSum.eval tr t r pub=
      (preparedTypedStackLimb (tr.cell t r) (sp-1) 0+preparedTypedStackLimb (tr.cell t r) (sp-1) 1)+
      (preparedTypedStackLimb (tr.cell t r) (sp-1) 2+preparedTypedStackLimb (tr.cell t r) (sp-1) 3) := by
  change ((preparedTypedSelectedLimb 0).eval tr t r pub+(preparedTypedSelectedLimb 1).eval tr t r pub)+
    ((preparedTypedSelectedLimb 2).eval tr t r pub+(preparedTypedSelectedLimb 3).eval tr t r pub)=_
  rw [prepared_typed_selected_limb tr t r pub sp 0 hs positive hot,
      prepared_typed_selected_limb tr t r pub sp 1 hs positive hot,
      prepared_typed_selected_limb tr t r pub sp 2 hs positive hot,
      prepared_typed_selected_limb tr t r pub sp 3 hs positive hot]

/-- The eqz auxiliary is constrained to the actual selected top64-bit word.
All ranges come from literal bit constraints, not external operand bounds. -/
theorem prepared_typed_source_eqz (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (sp : Nat) (hs : sp<9) (positive : 0<sp)
    (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    tr.cell t r 1284=if preparedTypedStackWord (tr.cell t r) (sp-1)=0 then 1 else 0 := by
  have source:=eqz_at ⟨count,by omega⟩
  have inverse:=localH.constr r hr _ (List.mem_of_getElem? source.1)
  have zero:=localH.constr r hr _ (List.mem_of_getElem? source.2)
  change preparedTypedSelectedSum.eval tr t r pub*tr.cell t r 1283+ -((1:Fp)+ -tr.cell t r 1284)=0 at inverse
  change preparedTypedSelectedSum.eval tr t r pub*tr.cell t r 1284+ -(0:Fp)=0 at zero
  let limb:=preparedTypedStackLimb (tr.cell t r) (sp-1)
  have selected:=prepared_typed_selected_sum tr t r pub sp hs positive hot
  have h0:=prepared_typed_stack_limb_bound count hc tr t r pub localH hr (sp-1) 0 (by omega) (by decide)
  have h1:=prepared_typed_stack_limb_bound count hc tr t r pub localH hr (sp-1) 1 (by omega) (by decide)
  have h2:=prepared_typed_stack_limb_bound count hc tr t r pub localH hr (sp-1) 2 (by omega) (by decide)
  have h3:=prepared_typed_stack_limb_bound count hc tr t r pub localH hr (sp-1) 3 (by omega) (by decide)
  change (limb 0).toNat<65536 at h0
  change (limb 1).toNat<65536 at h1
  change (limb 2).toNat<65536 at h2
  change (limb 3).toNat<65536 at h3
  have noWrap : (preparedTypedSelectedSum.eval tr t r pub).toNat=
      (limb 0).toNat+(limb 1).toNat+((limb 2).toNat+(limb 3).toNat) := by
    rw [selected]
    change (Fp.add (Fp.add (limb 0) (limb 1)) (Fp.add (limb 2) (limb 3))).toNat=_
    simp only [Fp.toNat_add]
    rw [Nat.mod_eq_of_lt (show (limb 0).toNat+(limb 1).toNat<ZkFormal.Algebra.P by unfold ZkFormal.Algebra.P;omega),
      Nat.mod_eq_of_lt (show (limb 2).toNat+(limb 3).toNat<ZkFormal.Algebra.P by unfold ZkFormal.Algebra.P;omega),
      Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P;omega)]
  have iffZero : preparedTypedSelectedSum.eval tr t r pub=0 ↔ preparedTypedStackWord (tr.cell t r) (sp-1)=0 := by
    constructor
    · intro z
      rw [z] at noWrap
      change 0=_ at noWrap
      change (limb 0).toNat+65536*(limb 1).toNat+4294967296*(limb 2).toNat+281474976710656*(limb 3).toNat=0
      omega
    · intro z
      apply Fp.ext
      change _=0
      rw [noWrap]
      change (limb 0).toNat+65536*(limb 1).toNat+4294967296*(limb 2).toNat+281474976710656*(limb 3).toNat=0 at z
      omega
  split
  · rename_i eq
    rw [iffZero.mpr eq] at inverse
    grind
  · rename_i ne
    have nonzero : preparedTypedSelectedSum.eval tr t r pub≠0:=by intro z;exact ne (iffZero.mp z)
    grind
end NearCompression
