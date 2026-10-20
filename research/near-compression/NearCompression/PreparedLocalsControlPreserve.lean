import NearCompression.PreparedLocalsOpcode
import NearCompression.PreparedLocalsFrameWrite
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm

theorem prepared_locals_control_array_preserved (count : Nat) (bounded : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub)
    (nonlast : r+1<tr.height t) (tag : Nat) (bound : tag<6)
    (chosen : tr.cell t r (preparedControlOpcodeColumn tag)=1) :
    preparedLocalsArray (tr.cell t (r+1)) count=preparedLocalsArray (tr.cell t r) count := by
  have zero:=(prepared_locals_control_opcode_exclusive count tr t r pub localH (by omega) tag bound chosen).2
  apply prepared_locals_array_preserved count bounded tr t r pub localH nonlast
  intro slot hs
  change preparedLocalsSuccess.eval tr t r pub*((tr.cell t r 684+tr.cell t r 685)*tr.cell t r (814+slot))=0
  rw [zero 1 (by decide),zero 2 (by decide)]
  grind
end NearCompression
