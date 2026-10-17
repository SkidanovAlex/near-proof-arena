import NearCompression.PreparedTypedEqzStack
import NearCompression.PreparedTypedEqzDepth
import NearCompression.PreparedTypedSequential
import NearCompression.PreparedTypedGas
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private def smallSum (f : Nat→Expr) : Nat→Expr
 | 0=>.const 0
 | 1=>f 0
 | 2=>.add (f 0) (f 1)
 | 3=>.add (.add (f 0) (f 1)) (f 2)
 | 4=>preparedBalancedSum f 2 0
 | 5=>.add (preparedBalancedSum f 2 0) (f 4)
 | 6=>.add (preparedBalancedSum f 2 0) (.add (f 4) (f 5))
 | 7=>.add (preparedBalancedSum f 2 0) (.add (.add (f 4) (f 5)) (f 6))
 | _=>preparedBalancedSum f 3 0
private def constOp : Expr := .add (.col 466 false) (.col 1280 false)
private def addOp : Expr := .add (.col 467 false) (.col 1281 false)
private def push (slot : Nat) : Expr := .mul preparedExecGasSuccess (.mul (.add constOp (.col 683 false)) (.col (32+slot) false))
private def write (slot : Nat) : Expr := .mul preparedExecGasSuccess (.mul addOp (if slot+2≤8 then .col (34+slot) false else .const 0))
private def clear (slot : Nat) : Expr := .mul preparedExecGasSuccess (.mul (.add (.add (.add addOp (.col 468 false)) (.col 606 false)) (.col 684 false)) (.col (33+slot) false))
private def zero (slot : Nat) : Expr := .mul preparedExecGasSuccess (.mul (.col 1282 false) (.col (33+slot) false))
private def retain (slot : Nat) : Expr := .add (.const 1) (.neg (.add (.add (.add (push slot) (write slot)) (clear slot)) (zero slot)))
private def below (slot : Nat) : Expr := smallSum (fun i=>.col (640+(slot+1+i)) false) (8-slot)
private def localType : Expr := preparedBalancedSum (fun i=>.mul (.col (814+i) false) (.col (1210+i) false)) 2 0
private def pushed (limb : Nat) : Expr := .add (.mul constOp (preparedCodeBits ((if limb<2 then 470 else 1214)+16*(limb%2))))
  (.mul (.col 683 false) (preparedBalancedSum (fun i=>.mul (.col (814+i) false) (preparedCodeBits ((if limb<2 then 686 else 1082)+32*i+16*(limb%2)))) 2 0))
def preparedTypedFrameStackWrite (slot limb : Nat) : Expr :=
  let old:=preparedCodeBits (preparedTypedStackBase slot limb)
  let linear:=.add (.mul (retain slot) old) (.add (.add (.mul (push slot) (pushed limb))
    (.mul (write slot) (preparedCodeBits ((if limb<2 then 431 else 1246)+16*(limb%2)))))
    (.mul (zero slot) (if limb=0 then .col 1284 false else .const 0)))
  .mul .isTransition (.add (preparedCodeBits (preparedTypedStackBase slot limb) true)
    (.neg (.add (.mul preparedControlTaken (.mul (below slot) old))
      (.mul (.add (.const 1) (.neg preparedControlTaken)) linear))))
def preparedTypedFrameTypeWrite (slot : Nat) : Expr :=
  .mul .isTransition (.add (.col (1074+slot) true)
    (.neg (.add (.mul preparedControlTaken (.mul (below slot) (.col (1074+slot) false)))
      (.mul (.add (.const 1) (.neg preparedControlTaken))
        (.add (.mul (retain slot) (.col (1074+slot) false))
          (.add (.mul (push slot) (.add (.col 1280 false) (.mul (.col 683 false) localType)))
            (.mul (write slot) (.col 1281 false))))))))
private theorem writes_at : ∀count:Fin 5,∀slot:Fin 8,∀limb:Fin 4,
    (preparedTypedLiteralExec count)[1738+66*(4-count.val)+12*slot.val+2*limb.val+(limb.val-1)]?=
      some (preparedTypedFrameStackWrite slot limb) := by decide
private theorem types_at : ∀count:Fin 5,∀slot:Fin 8,
    (preparedTypedLiteralExec count)[1748+66*(4-count.val)+12*slot.val]?=some (preparedTypedFrameTypeWrite slot) := by decide

theorem prepared_typed_frame_stack_limb (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (tag : Nat) (which : tag=3 ∨ tag=4) (opcode : tr.cell t r (preparedTypedOpcodeColumn tag)=1)
    (slot limb : Nat) (hs : slot<8) (hl : limb<4) :
    preparedTypedStackLimb (tr.cell t (r+1)) slot limb=preparedTypedStackLimb (tr.cell t r) slot limb := by
  have h:=localH.constr r (by omega) _ (List.mem_of_getElem? (writes_at ⟨count,by omega⟩ ⟨slot,hs⟩ ⟨limb,hl⟩))
  have be (base : Nat) (nx : Bool) : (preparedCodeBits base nx).evalWith (rowEnv tr t r pub)=
      preparedCodeLimb (tr.cell t (if nx then (r+1)%tr.height t else r)) base :=
    prepared_code_bits_eval tr t r pub base nx
  have flags:=prepared_typed_opcode_selected count hc tr t r pub localH (by omega) tag (by omega) opcode
  have z0 : tr.cell t r 466=0 := by
    have h:=flags 0 (by decide)
    change tr.cell t r 466=(if 0=tag then 1 else 0) at h
    simpa only [show ¬0=tag by omega,ite_false] using h
  have z1 : tr.cell t r 467=0 := by
    have h:=flags 1 (by decide)
    change tr.cell t r 467=(if 1=tag then 1 else 0) at h
    simpa only [show ¬1=tag by omega,ite_false] using h
  have z2 : tr.cell t r 468=0 := by
    have h:=flags 2 (by decide)
    change tr.cell t r 468=(if 2=tag then 1 else 0) at h
    simpa only [show ¬2=tag by omega,ite_false] using h
  have z5 : tr.cell t r 606=0 := by
    have h:=flags 5 (by decide)
    change tr.cell t r 606=(if 5=tag then 1 else 0) at h
    simpa only [show ¬5=tag by omega,ite_false] using h
  have z6 : tr.cell t r 683=0 := by
    have h:=flags 6 (by decide)
    change tr.cell t r 683=(if 6=tag then 1 else 0) at h
    simpa only [show ¬6=tag by omega,ite_false] using h
  have z7 : tr.cell t r 684=0 := by
    have h:=flags 7 (by decide)
    change tr.cell t r 684=(if 7=tag then 1 else 0) at h
    simpa only [show ¬7=tag by omega,ite_false] using h
  have z9 : tr.cell t r 1280=0 := by
    have h:=flags 9 (by decide)
    change tr.cell t r 1280=(if 9=tag then 1 else 0) at h
    simpa only [show ¬9=tag by omega,ite_false] using h
  have z10 : tr.cell t r 1281=0 := by
    have h:=flags 10 (by decide)
    change tr.cell t r 1281=(if 10=tag then 1 else 0) at h
    simpa only [show ¬10=tag by omega,ite_false] using h
  have z11 : tr.cell t r 1282=0 := by
    have h:=flags 11 (by decide)
    change tr.cell t r 1282=(if 11=tag then 1 else 0) at h
    simpa only [show ¬11=tag by omega,ite_false] using h
  simp only [preparedTypedFrameStackWrite,retain,push,write,clear,zero,constOp,addOp,pushed,
    preparedControlTaken,Expr.eval,be,Expr.evalWith] at h
  simp only [rowEnv,Bool.false_eq_true,ite_false,ite_true,show ¬r+1=tr.height t by omega,
    Nat.mod_eq_of_lt nonlast,←Fp.ofNat_def,z0,z1,z2,z5,z6,z7,z9,z10,z11] at h
  unfold preparedTypedStackLimb
  grind

theorem prepared_typed_frame_stack_tag (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (tag : Nat) (which : tag=3 ∨ tag=4) (opcode : tr.cell t r (preparedTypedOpcodeColumn tag)=1)
    (slot : Nat) (hs : slot<8) : tr.cell t (r+1) (1074+slot)=tr.cell t r (1074+slot) := by
  have h:=localH.constr r (by omega) _ (List.mem_of_getElem? (types_at ⟨count,by omega⟩ ⟨slot,hs⟩))
  have flags:=prepared_typed_opcode_selected count hc tr t r pub localH (by omega) tag (by omega) opcode
  have z0 : tr.cell t r 466=0 := by
    have h:=flags 0 (by decide)
    change tr.cell t r 466=(if 0=tag then 1 else 0) at h
    simpa only [show ¬0=tag by omega,ite_false] using h
  have z1 : tr.cell t r 467=0 := by
    have h:=flags 1 (by decide)
    change tr.cell t r 467=(if 1=tag then 1 else 0) at h
    simpa only [show ¬1=tag by omega,ite_false] using h
  have z2 : tr.cell t r 468=0 := by
    have h:=flags 2 (by decide)
    change tr.cell t r 468=(if 2=tag then 1 else 0) at h
    simpa only [show ¬2=tag by omega,ite_false] using h
  have z5 : tr.cell t r 606=0 := by
    have h:=flags 5 (by decide)
    change tr.cell t r 606=(if 5=tag then 1 else 0) at h
    simpa only [show ¬5=tag by omega,ite_false] using h
  have z6 : tr.cell t r 683=0 := by
    have h:=flags 6 (by decide)
    change tr.cell t r 683=(if 6=tag then 1 else 0) at h
    simpa only [show ¬6=tag by omega,ite_false] using h
  have z7 : tr.cell t r 684=0 := by
    have h:=flags 7 (by decide)
    change tr.cell t r 684=(if 7=tag then 1 else 0) at h
    simpa only [show ¬7=tag by omega,ite_false] using h
  have z9 : tr.cell t r 1280=0 := by
    have h:=flags 9 (by decide)
    change tr.cell t r 1280=(if 9=tag then 1 else 0) at h
    simpa only [show ¬9=tag by omega,ite_false] using h
  have z10 : tr.cell t r 1281=0 := by
    have h:=flags 10 (by decide)
    change tr.cell t r 1281=(if 10=tag then 1 else 0) at h
    simpa only [show ¬10=tag by omega,ite_false] using h
  have z11 : tr.cell t r 1282=0 := by
    have h:=flags 11 (by decide)
    change tr.cell t r 1282=(if 11=tag then 1 else 0) at h
    simpa only [show ¬11=tag by omega,ite_false] using h
  simp only [preparedTypedFrameTypeWrite,retain,push,write,clear,zero,constOp,addOp,
    preparedControlTaken,Expr.eval,Expr.evalWith] at h
  simp only [rowEnv,Bool.false_eq_true,ite_false,ite_true,show ¬r+1=tr.height t by omega,
    Nat.mod_eq_of_lt nonlast,←Fp.ofNat_def,z0,z1,z2,z5,z6,z7,z9,z10,z11] at h
  grind

theorem prepared_typed_frame_stack_value (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (tag : Nat) (which : tag=3 ∨ tag=4) (opcode : tr.cell t r (preparedTypedOpcodeColumn tag)=1)
    (slot : Nat) (hs : slot<8) :
    preparedTypedStackValue (tr.cell t (r+1)) slot=preparedTypedStackValue (tr.cell t r) slot := by
  have tagEq:=prepared_typed_frame_stack_tag count hc tr t r pub localH nonlast tag which opcode slot hs
  have limb (i : Nat) (hi : i<4):=prepared_typed_frame_stack_limb count hc tr t r pub localH nonlast tag which opcode slot i hs hi
  have word : preparedTypedStackWord (tr.cell t (r+1)) slot=preparedTypedStackWord (tr.cell t r) slot := by
    unfold preparedTypedStackWord instructionAdd64Word
    rw [limb 0 (by decide),limb 1 (by decide),limb 2 (by decide),limb 3 (by decide)]
  simp only [preparedTypedStackValue,tagEq,word]
end NearCompression
