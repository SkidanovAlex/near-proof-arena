import NearCompression.PreparedMemoryWords
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Sha.View ZkFormal.Sha.Sound NearSpecV3.Wasm

/-- Actual loadSpec descriptor of each selected legal integer load. -/
theorem prepared_memory_load_spec (selected : Fin 19) (load:selected.val<12) :
    loadSpec (preparedMemoryOpcode selected)=
      (preparedMemoryWidth selected,preparedMemorySigned selected,preparedMemoryIs64 selected) := by
  have all : ∀i:Fin 19,i.val<12→loadSpec (preparedMemoryOpcode i)=
      (preparedMemoryWidth i,preparedMemorySigned i,preparedMemoryIs64 i) := by decide
  exact all selected load

def preparedMemoryResultValue (row : Nat→Fp) (selected : Nat) : Val :=
  if preparedMemoryIs64 selected then .i64 (UInt64.ofNat (preparedMemoryWord row 357))
  else .i32 (UInt32.ofNat (preparedMemoryWord row 357))

theorem prepared_memory_unsigned_word (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedMemoryLiteralTable tr t pub) (hr:r<tr.height t)
    (selected : Fin 19) (hot:∀i,i<19→tr.cell t r i=if i=selected.val then 1 else 0)
    (load:selected.val<12) (unsigned:preparedMemorySigned selected=false) :
    preparedMemoryWord (tr.cell t r) 357=preparedMemoryWord (tr.cell t r) 293 := by
  have sizes : ∀i:Fin 19,i.val<12→8*preparedMemoryWidth i≤(if preparedMemoryIs64 i then 64 else 32) := by decide
  have size:=sizes selected load
  have write : preparedMemoryWrite selected=false := by simp only [preparedMemoryWrite,decide_eq_false_iff_not];omega
  apply ofBits_congr
  intro b hb
  have eq:=prepared_memory_result_bits tr t r pub localH hr selected hot b hb
  by_cases low:b<8*preparedMemoryWidth selected
  · have fits:¬(if preparedMemoryIs64 selected then 64 else 32)≤b:=by omega
    simp only [preparedMemoryResultBit,write,Bool.false_or,decide_eq_false fits,ite_false,if_pos low] at eq
    exact congrArg Fp.toNat eq
  · have zero:=prepared_memory_raw_high_zero tr t r pub localH hr selected hot b hb (by omega)
    have out : tr.cell t r (357+b)=0 := by
      change tr.cell t r (357+b)=Fp.ofNat 0
      simpa only [preparedMemoryResultBit,write,Bool.false_or,if_neg low,unsigned,Bool.false_eq_true,ite_false,
        ite_self,Expr.evalWith,preparedGasEnv,instructionAddEnv] using eq
    rw [out,zero]

/-- Unsigned load result agrees with the actual interpreter value constructor. -/
theorem prepared_memory_unsigned_value (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedMemoryLiteralTable tr t pub) (hr:r<tr.height t)
    (selected : Fin 19) (hot:∀i,i<19→tr.cell t r i=if i=selected.val then 1 else 0)
    (load:selected.val<12) (unsigned:preparedMemorySigned selected=false) :
    preparedMemoryResultValue (tr.cell t r) selected=
      preparedMemoryLoadedValue (preparedMemoryOpcode selected) (preparedMemoryWord (tr.cell t r) 293) := by
  unfold preparedMemoryResultValue preparedMemoryLoadedValue
  rw [prepared_memory_load_spec selected load,unsigned]
  rw [prepared_memory_unsigned_word tr t r pub localH hr selected hot load unsigned]
  rfl
end NearCompression
