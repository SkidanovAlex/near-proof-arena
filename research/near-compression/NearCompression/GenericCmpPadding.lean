import NearCompression.GenericPaddingLocal
import ZkFormal.NearV3.Render.PaddedSched

/-! Concrete comparator-renderer instantiation of padding shrinkage. This
module transports actual comparator local constraints; it does not assert
preservation of global bus traffic or modify the production renderer. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Complete
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Render

/-- Actual generated comparison rows, before the renderer appends padding. -/
def genericCmpPrefix (cmps : List (Nat × Nat × Nat)) (r c : Nat) : Fp :=
  Fp.ofNat (((Gen.Cmp.rows cmps).getD r #[]).getD c 0)

/-- Actual comparator padding row, including its nonzero comparison bit. -/
def genericCmpPad (c : Nat) : Fp := Fp.ofNat (Gen.Cmp.padRow.getD c 0)

def genericCmpShrunkTrace (cmps : List (Nat × Nat × Nat)) (logSize : Nat) : Trace Fp :=
  genericPaddingTrace (genericCmpPrefix cmps) cmps.length genericCmpPad logSize

/-- The function-backed comparator renderer is exactly prefix plus constant
padding, including empty comparison lists. -/
theorem generic_cmp_padding_cells (cmps : List (Nat × Nat × Nat)) (t r c : Nat) :
    (CmpHeight.trace cmps).cell t r c=
      genericPaddingRow (genericCmpPrefix cmps) cmps.length genericCmpPad r c := by
  change Fp.ofNat (natCell (Gen.Cmp.rows cmps) (fun _ => Gen.Cmp.padRow) r c)=_
  by_cases hr : r<cmps.length
  · rw [genericPaddingRow,if_pos hr]
    unfold natCell
    have bound : r<(Gen.Cmp.rows cmps).size := by rw [rows_size]; exact hr
    rw [natRow_lt _ _ bound]
    simp only [genericCmpPrefix,gd,Array.getD_eq_getD_getElem?,Array.getElem?_eq_getElem bound,Option.getD_some]
  · rw [genericPaddingRow,if_neg hr]
    unfold natCell
    rw [natRow_ge _ _ (by rw [rows_size]; omega)]
    rfl

/-- Exact cell representation for the actual array-backed aligned renderer,
restricted to its physical row domain. No huge array is evaluated here. -/
theorem generic_cmp_aligned_padding_cells (cmps : List (Nat × Nat × Nat)) (t r c : Nat)
    (hr : r<2^22) :
    (cmpTraceAligned cmps).cell t r c=
      genericPaddingRow (genericCmpPrefix cmps) cmps.length genericCmpPad r c := by
  have aligned := schedTraceAligned_cells (Gen.Cmp.rows cmps) (fun _ => Gen.Cmp.padRow) t r hr c
  exact aligned.symm.trans (generic_cmp_padding_cells cmps t r c)

/-- Actual Expr evaluation on the aligned renderer equals the generic padding
representation at its original height. -/
theorem generic_cmp_aligned_padding_eval (cmps : List (Nat × Nat × Nat))
    (e : Expr) (t r : Nat) (pub : List Fp) (hr : r<2^22) :
    e.eval (genericCmpShrunkTrace cmps 22) t r pub=e.eval (cmpTraceAligned cmps) t r pub := by
  apply eval_congr_rows (tr₁ := genericCmpShrunkTrace cmps 22) (tr₂ := cmpTraceAligned cmps) rfl
    (fun row bound col => (generic_cmp_aligned_padding_cells cmps t row col bound).symm) e r hr pub

/-- Honest comparator inputs yield legal source-table constraints at any smaller
power-of-two height retaining at least one padding row. This derives legality
from the existing renderer completeness theorem, not a new-height premise. -/
theorem generic_cmp_padding_constraints (cmps : List (Nat × Nat × Nat))
    (honest : ∀ q ∈ cmps,CmpOk q) (logSize : Nat)
    (logBounds : 1≤logSize ∧ logSize≤22) (fits : cmps.length<2^logSize)
    (t r : Nat) (pub : List Fp) (hr : r<2^logSize)
    (e : Expr) (member : e ∈ (Cmp.table ZkFormal.NearV3.Sched.B_SCMP).constraints) :
    e.eval (genericCmpShrunkTrace cmps logSize) t r pub=0 := by
  have heightBound : 2^logSize≤2^22 := Nat.pow_le_pow_right (by decide) logBounds.2
  have atLeastTwo : 2≤2^logSize := Nat.pow_le_pow_right (by decide : 0<2) logBounds.1
  have oldLocal := (cmp_aligned_complete cmps honest (by omega) t pub).1
  apply generic_padding_expr_shrink e (genericCmpPrefix cmps) cmps.length genericCmpPad pub
    22 logSize t fits heightBound atLeastTwo _ r hr
  intro oldRow bound
  rw [←show genericCmpShrunkTrace cmps 22=
    genericPaddingTrace (genericCmpPrefix cmps) cmps.length genericCmpPad 22 from rfl,
    generic_cmp_aligned_padding_eval cmps e t oldRow pub bound]
  exact oldLocal.constr oldRow bound e member

/-- The comparator multiplicity is its current-row active bit, so the exact
old-renderer Booleanity theorem also survives the height change. -/
theorem generic_cmp_padding_bits (cmps : List (Nat × Nat × Nat)) (logSize : Nat)
    (logBound : logSize≤22) (t r : Nat) (pub : List Fp) (hr : r<2^logSize)
    (i : Interaction) (member : i ∈ (Cmp.table ZkFormal.NearV3.Sched.B_SCMP).interactions)
    (b : Expr) (bitMember : b ∈ i.mult) :
    b.eval (genericCmpShrunkTrace cmps logSize) t r pub=0 ∨
      b.eval (genericCmpShrunkTrace cmps logSize) t r pub=1 := by
  have oldBound : r<(CmpHeight.trace cmps).height t := by
    have bound := Nat.pow_le_pow_right (by decide : 1≤2) logBound
    change r<2^22
    omega
  have old := CmpHeight.cmp_bits cmps ZkFormal.NearV3.Sched.B_SCMP t r pub oldBound i member b bitMember
  simp only [Cmp.table,Cmp.interactions,List.mem_cons,List.not_mem_nil,or_false] at member
  subst i
  simp only [List.mem_cons,List.not_mem_nil,or_false] at bitMember
  subst b
  change genericPaddingRow (genericCmpPrefix cmps) cmps.length genericCmpPad r Cmp.colAct=0 ∨
    genericPaddingRow (genericCmpPrefix cmps) cmps.length genericCmpPad r Cmp.colAct=1
  rw [←generic_cmp_padding_cells cmps t r Cmp.colAct]
  exact old

/-- Full local table legality, including multiplicity-bit Booleanity and log
bounds. Global comparator bus traffic remains a separate obligation. -/
theorem generic_cmp_padding_local (cmps : List (Nat × Nat × Nat))
    (honest : ∀ q ∈ cmps,CmpOk q) (logSize : Nat)
    (logBounds : 1≤logSize ∧ logSize≤22) (fits : cmps.length<2^logSize)
    (t : Nat) (pub : List Fp) :
    ZkFormal.Near.TableLocal (Cmp.table ZkFormal.NearV3.Sched.B_SCMP)
      (genericCmpShrunkTrace cmps logSize) t pub := by
  exact ⟨logBounds.1,logBounds.2,
    fun r hr e he => generic_cmp_padding_constraints cmps honest logSize logBounds fits t r pub hr e he,
    fun r hr i hi b hb => generic_cmp_padding_bits cmps logSize logBounds.2 t r pub hr i hi b hb⟩

end NearCompression
