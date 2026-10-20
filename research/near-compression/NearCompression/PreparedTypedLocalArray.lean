import NearCompression.PreparedTypedLocalUpdate
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm

theorem prepared_typed_local_lookup (row : Nat→Fp) (count index : Nat) (valid : index<count) :
    (preparedTypedLocalArray row count)[index]?=some (preparedTypedLocalValue row index) := by
  simp [preparedTypedLocalArray,valid]

theorem prepared_typed_local_array_set (row next : Nat→Fp) (count index : Nat) (value : Val)
    (valid : index<count)
    (values : ∀j,j<count → preparedTypedLocalValue next j=if j=index then value else preparedTypedLocalValue row j) :
    preparedTypedLocalArray next count=(preparedTypedLocalArray row count).set! index value := by
  apply Array.ext_getElem?
  intro j
  by_cases inside:j<count
  · rw [prepared_typed_local_lookup next count j inside]
    simp only [Array.set!_eq_setIfInBounds]
    by_cases same:j=index
    · subst j
      rw [Array.getElem?_setIfInBounds_self_of_lt (by simp [preparedTypedLocalArray,valid])]
      rw [values index valid,ite_eq_left rfl]
    · rw [Array.getElem?_setIfInBounds_ne (Ne.symm same),prepared_typed_local_lookup row count j inside]
      rw [values j inside,ite_eq_right same]
  · have left : (preparedTypedLocalArray next count)[j]?=none:=by simp [preparedTypedLocalArray,inside]
    have right : ((preparedTypedLocalArray row count).set! index value)[j]?=none := by
      apply Array.getElem?_eq_none
      simp only [Array.size_set!,preparedTypedLocalArray,List.size_toArray,List.length_map,List.length_range]
      omega
    rw [left,right]

theorem prepared_typed_local_array_write (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (write : tr.cell t r 684+tr.cell t r 685=1)
    (sp index : Nat) (sb : sp<9) (positive : 0<sp) (valid : index<count)
    (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0)
    (selected : ∀i,i<4 → tr.cell t r (814+i)=if i=index then 1 else 0) :
    preparedTypedLocalArray (tr.cell t (r+1)) count=
      (preparedTypedLocalArray (tr.cell t r) count).set! index (preparedTypedStackValue (tr.cell t r) (sp-1)) := by
  apply prepared_typed_local_array_set _ _ count index _ valid
  intro slot hs
  exact prepared_typed_local_store_value count hc tr t r pub localH nonlast active charged write sp index sb positive
    (by omega) hot selected slot (by omega)
end NearCompression
