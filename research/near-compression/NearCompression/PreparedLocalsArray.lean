import NearCompression.PreparedLocalsUpdate
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def preparedLocalsStackWord (row : Nat→Fp) (slot : Nat) : Nat :=
  (preparedCodeLimb row (43+32*slot)).toNat+65536*(preparedCodeLimb row (59+32*slot)).toNat

theorem prepared_locals_top_selected (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (sp limb : Nat) (depth : sp<9) (positive : 0<sp)
    (hot : ∀j,j<9 → tr.cell t r (32+j)=if j=sp then 1 else 0) :
    (preparedLocalsTop limb).eval tr t r pub=preparedCodeLimb (tr.cell t r) (43+32*(sp-1)+16*limb) := by
  have decoded:=prepared_code_bits_eval tr t r pub (43+32*(sp-1)+16*limb) false
  simp only [Bool.false_eq_true,ite_false] at decoded
  rw [←decoded]
  have h1:=hot 1 (by decide);have h2:=hot 2 (by decide)
  have h3:=hot 3 (by decide);have h4:=hot 4 (by decide)
  have h5:=hot 5 (by decide);have h6:=hot 6 (by decide)
  have h7:=hot 7 (by decide);have h8:=hot 8 (by decide)
  change (((tr.cell t r 33*(preparedCodeBits (43+32*0+16*limb)).eval tr t r pub+
    tr.cell t r 34*(preparedCodeBits (43+32*1+16*limb)).eval tr t r pub)+
    (tr.cell t r 35*(preparedCodeBits (43+32*2+16*limb)).eval tr t r pub+
    tr.cell t r 36*(preparedCodeBits (43+32*3+16*limb)).eval tr t r pub))+
    ((tr.cell t r 37*(preparedCodeBits (43+32*4+16*limb)).eval tr t r pub+
    tr.cell t r 38*(preparedCodeBits (43+32*5+16*limb)).eval tr t r pub)+
    (tr.cell t r 39*(preparedCodeBits (43+32*6+16*limb)).eval tr t r pub+
    tr.cell t r 40*(preparedCodeBits (43+32*7+16*limb)).eval tr t r pub)))=_
  have cases : sp=1 ∨ sp=2 ∨ sp=3 ∨ sp=4 ∨ sp=5 ∨ sp=6 ∨ sp=7 ∨ sp=8 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [Nat.reduceAdd,Nat.reduceEqDiff,ite_true,ite_false] at h1 h2 h3 h4 h5 h6 h7 h8
  all_goals rw [h1,h2,h3,h4,h5,h6,h7,h8]
  all_goals simp only [Nat.reduceSub,Nat.reduceMul,Nat.reduceAdd]
  all_goals grind

/-- Actual local write equations select exactly one array element; they
preserve every other local and read the real selected operand-stack top. -/
theorem prepared_locals_words_write (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub)
    (nonlast : r+1<tr.height t) (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (writeOp : tr.cell t r 684+tr.cell t r 685=1)
    (index sp : Nat) (hs : sp<9) (positive : 0<sp)
    (selected : ∀j,j<4 → tr.cell t r (814+j)=if j=index then 1 else 0)
    (stack : ∀j,j<9 → tr.cell t r (32+j)=if j=sp then 1 else 0)
    (slot : Nat) (bound : slot<4) :
    preparedLocalsWord (tr.cell t (r+1)) slot=
      if slot=index then preparedLocalsStackWord (tr.cell t r) (sp-1) else preparedLocalsWord (tr.cell t r) slot := by
  have write : (preparedLocalsWrite slot).eval tr t r pub=if slot=index then 1 else 0 := by
    change ((1:Fp)+ -tr.cell t r 41)*(1+ -tr.cell t r 430)*
      ((tr.cell t r 684+tr.cell t r 685)*tr.cell t r (814+slot))=_
    rw [active,charged,writeOp,selected slot bound]
    grind
  have lo:=prepared_locals_limb_step count tr t r pub localH nonlast slot 0 bound (by decide)
  have hi:=prepared_locals_limb_step count tr t r pub localH nonlast slot 1 bound (by decide)
  rw [write,prepared_locals_top_selected tr t r pub sp 0 hs positive stack] at lo
  rw [write,prepared_locals_top_selected tr t r pub sp 1 hs positive stack] at hi
  simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one] at lo hi
  by_cases eq:slot=index
  · rw [ite_eq_left eq] at lo hi ⊢
    have lo' : preparedCodeLimb (tr.cell t (r+1)) (686+32*slot)=preparedCodeLimb (tr.cell t r) (43+32*(sp-1)) := by grind
    have hi' : preparedCodeLimb (tr.cell t (r+1)) (702+32*slot)=preparedCodeLimb (tr.cell t r) (59+32*(sp-1)) := by
      have a : 686+32*slot+16=702+32*slot := by omega
      have b : 43+32*(sp-1)+16=59+32*(sp-1) := by omega
      rw [a,b] at hi;grind
    simp only [preparedLocalsWord,preparedLocalsStackWord,lo',hi']
  · rw [ite_eq_right eq] at lo hi ⊢
    have lo' : preparedCodeLimb (tr.cell t (r+1)) (686+32*slot)=preparedCodeLimb (tr.cell t r) (686+32*slot) := by grind
    have hi' : preparedCodeLimb (tr.cell t (r+1)) (702+32*slot)=preparedCodeLimb (tr.cell t r) (702+32*slot) := by
      have a : 686+32*slot+16=702+32*slot := by omega
      rw [a] at hi;grind
    simp only [preparedLocalsWord,lo',hi']

/-- Decoded array equality with actual interpreter set!, given pointwise
word updates. The source theorem above supplies those updates. -/
theorem prepared_locals_array_set (row next : Nat→Fp) (count index value : Nat)
    (valid : index<count)
    (words : ∀j,j<count → preparedLocalsWord next j=if j=index then value else preparedLocalsWord row j) :
    preparedLocalsArray next count=(preparedLocalsArray row count).set! index (.i32 (UInt32.ofNat value)) := by
  apply Array.ext_getElem?
  intro j
  by_cases inside:j<count
  · rw [prepared_locals_lookup next count j inside]
    simp only [Array.set!_eq_setIfInBounds]
    by_cases same:j=index
    · subst j
      rw [Array.getElem?_setIfInBounds_self_of_lt (by simp [preparedLocalsArray,valid])]
      rw [words index valid,ite_eq_left rfl]
    · rw [Array.getElem?_setIfInBounds_ne (Ne.symm same),prepared_locals_lookup row count j inside]
      rw [words j inside,ite_eq_right same]
  · have left : (preparedLocalsArray next count)[j]?=none := by simp [preparedLocalsArray,inside]
    have right : ((preparedLocalsArray row count).set! index (.i32 (UInt32.ofNat value)))[j]?=none := by
      apply Array.getElem?_eq_none
      simp only [Array.size_set!,preparedLocalsArray,List.size_toArray,List.length_map,List.length_range]
      omega
    rw [left,right]
/-- Composition of the literal local-write equations with exact array set!.
This carries no assumed next-local-array equality. -/
theorem prepared_locals_array_write (count : Nat) (bounded : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub)
    (nonlast : r+1<tr.height t) (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (writeOp : tr.cell t r 684+tr.cell t r 685=1)
    (index sp : Nat) (valid : index<count) (hs : sp<9) (positive : 0<sp)
    (selected : ∀j,j<4 → tr.cell t r (814+j)=if j=index then 1 else 0)
    (stack : ∀j,j<9 → tr.cell t r (32+j)=if j=sp then 1 else 0) :
    preparedLocalsArray (tr.cell t (r+1)) count=
      (preparedLocalsArray (tr.cell t r) count).set! index
        (.i32 (UInt32.ofNat (preparedLocalsStackWord (tr.cell t r) (sp-1)))) := by
  apply prepared_locals_array_set _ _ count index _ valid
  intro slot hslot
  exact prepared_locals_words_write count tr t r pub localH nonlast active charged writeOp
    index sp hs positive selected stack slot (by omega)
end NearCompression
