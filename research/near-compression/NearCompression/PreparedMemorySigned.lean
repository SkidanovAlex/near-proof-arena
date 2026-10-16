import NearCompression.PreparedMemoryUnsigned
import NearCompression.PreparedMemorySignExtension
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Sha.View ZkFormal.Sha.Sound NearSpecV3.Wasm

theorem prepared_memory_raw_prefix (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedMemoryLiteralTable tr t pub) (hr:r<tr.height t)
    (selected : Fin 19) (hot:∀i,i<19→tr.cell t r i=if i=selected.val then 1 else 0) :
    preparedMemoryWord (tr.cell t r) 293=
      ofBits (fun b=>(tr.cell t r (293+b)).toNat) (8*preparedMemoryWidth selected) := by
  have wb : 8*preparedMemoryWidth selected≤64 := by
    have all : ∀i:Fin 19,8*preparedMemoryWidth i≤64 := by decide
    exact all selected
  rw [←prepared_memory_bits_prefix _ _ 64 wb]
  apply ofBits_congr
  intro b hb
  split
  · rfl
  · rename_i high
    rw [prepared_memory_raw_high_zero tr t r pub localH hr selected hot b hb (by omega)]
    rfl

theorem prepared_memory_signed_word (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedMemoryLiteralTable tr t pub) (hr:r<tr.height t)
    (selected : Fin 19) (hot:∀i,i<19→tr.cell t r i=if i=selected.val then 1 else 0)
    (load:selected.val<12) (signed:preparedMemorySigned selected=true) :
    preparedMemoryWord (tr.cell t r) 357=
      Num.extendS (if preparedMemoryIs64 selected then 64 else 32) (8*preparedMemoryWidth selected)
        (preparedMemoryWord (tr.cell t r) 293) := by
  let k:=8*preparedMemoryWidth selected
  let n:=if preparedMemoryIs64 selected then 64 else 32
  have valid : ∀i:Fin 19,i.val<12→preparedMemorySigned i=true→
      8*preparedMemoryWidth i∈[8,16,32] ∧ 8*preparedMemoryWidth i≤(if preparedMemoryIs64 i then 64 else 32) := by decide
  obtain ⟨ks,kn⟩:=valid selected load signed
  have kp : 0<k := by
    change k∈[8,16,32] at ks
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ks;omega
  have ns : n∈[32,64] := by dsimp [n];split <;> simp
  have write : preparedMemoryWrite selected=false := by simp only [preparedMemoryWrite,decide_eq_false_iff_not];omega
  have bits : ∀b,b<k→(tr.cell t r (293+b)).toNat≤1 := by
    intro b hb
    have source:=prepared_memory_literal_bounds tr t r pub localH hr
    have small:n≤64:=by simp only [List.mem_cons,List.not_mem_nil,or_false] at ns;omega
    exact prepared_memory_address_boolean _ source.1 _ (by change k≤n at kn;omega)
  rw [prepared_memory_raw_prefix tr t r pub localH hr selected hot]
  rw [←prepared_memory_sign_extension (fun b=>(tr.cell t r (293+b)).toNat) k n bits ks ns kn]
  apply ofBits_congr
  intro b hb
  have eq:=prepared_memory_result_bits tr t r pub localH hr selected hot b hb
  have signIndex : 293+k-1=293+(k-1):=by omega
  by_cases low:b<k
  · have fits:¬n≤b:=by change k≤n at kn;omega
    simp only [preparedMemoryResultBit,write,Bool.false_or,signed] at eq
    change tr.cell t r (357+b)=(if decide (n≤b) then Expr.const 0 else
      if b<k then Expr.col (293+b) false else Expr.col (293+k-1) false).evalWith (preparedGasEnv (tr.cell t r) []) at eq
    rw [decide_eq_false fits,if_neg Bool.false_ne_true,if_pos low] at eq
    rw [if_pos low]
    exact congrArg Fp.toNat eq
  · simp only [preparedMemoryResultBit,write,Bool.false_or,signed] at eq
    change tr.cell t r (357+b)=(if decide (n≤b) then Expr.const 0 else
      if b<k then Expr.col (293+b) false else Expr.col (293+k-1) false).evalWith (preparedGasEnv (tr.cell t r) []) at eq
    rw [if_neg low] at eq ⊢
    by_cases inside:b<n
    · rw [decide_eq_false (by omega),if_neg Bool.false_ne_true,signIndex] at eq
      rw [if_pos inside]
      exact congrArg Fp.toNat eq
    · rw [decide_eq_true (by omega),if_pos rfl] at eq
      rw [if_neg inside]
      exact congrArg Fp.toNat eq

/-- All twelve legal integer load results match the actual Wasm value
constructor, including signed extension and i32 versus i64 tagging. -/
theorem prepared_memory_load_value (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedMemoryLiteralTable tr t pub) (hr:r<tr.height t)
    (selected : Fin 19) (hot:∀i,i<19→tr.cell t r i=if i=selected.val then 1 else 0)
    (load:selected.val<12) :
    preparedMemoryResultValue (tr.cell t r) selected=
      preparedMemoryLoadedValue (preparedMemoryOpcode selected) (preparedMemoryWord (tr.cell t r) 293) := by
  cases signed : preparedMemorySigned selected with
  | false=>exact prepared_memory_unsigned_value tr t r pub localH hr selected hot load signed
  | true=>
    unfold preparedMemoryResultValue preparedMemoryLoadedValue
    rw [prepared_memory_load_spec selected load,signed]
    rw [prepared_memory_signed_word tr t r pub localH hr selected hot load signed]
    rfl
end NearCompression
