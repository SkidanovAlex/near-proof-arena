import NearCompression.PreparedTypedEqzGuard
import NearCompression.PreparedTypedOpcode
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
def preparedTypedStackWrite (slot limb : Nat) : Expr :=
  let old:=preparedCodeBits (preparedTypedStackBase slot limb)
  let linear:=.add (.mul (retain slot) old) (.add (.add (.mul (push slot) (pushed limb))
    (.mul (write slot) (preparedCodeBits ((if limb<2 then 431 else 1246)+16*(limb%2)))))
    (.mul (zero slot) (if limb=0 then .col 1284 false else .const 0)))
  .mul .isTransition (.add (preparedCodeBits (preparedTypedStackBase slot limb) true)
    (.neg (.add (.mul preparedControlTaken (.mul (below slot) old))
      (.mul (.add (.const 1) (.neg preparedControlTaken)) linear))))
def preparedTypedTypeWrite (slot : Nat) : Expr :=
  .mul .isTransition (.add (.col (1074+slot) true)
    (.neg (.add (.mul preparedControlTaken (.mul (below slot) (.col (1074+slot) false)))
      (.mul (.add (.const 1) (.neg preparedControlTaken))
        (.add (.mul (retain slot) (.col (1074+slot) false))
          (.add (.mul (push slot) (.add (.col 1280 false) (.mul (.col 683 false) localType)))
            (.mul (write slot) (.col 1281 false))))))))
private theorem writes_at : ∀count:Fin 5,∀slot:Fin 8,∀limb:Fin 4,
    (preparedTypedLiteralExec count)[1738+66*(4-count.val)+12*slot.val+2*limb.val+(limb.val-1)]?=
      some (preparedTypedStackWrite slot limb) := by decide
private theorem types_at : ∀count:Fin 5,∀slot:Fin 8,
    (preparedTypedLiteralExec count)[1748+66*(4-count.val)+12*slot.val]?=some (preparedTypedTypeWrite slot) := by decide

/-- Exact next-stack limb update for successful eqz; every untouched slot is
preserved by the literal write constraints. -/
theorem prepared_typed_eqz_stack_limb (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (opcode : tr.cell t r 1282=1)
    (sp : Nat) (hs : sp<9) (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0)
    (slot limb : Nat) (hslot : slot<8) (hlimb : limb<4) :
    preparedTypedStackLimb (tr.cell t (r+1)) slot limb=
      if slot+1=sp then (if limb=0 then tr.cell t r 1284 else 0)
      else preparedTypedStackLimb (tr.cell t r) slot limb := by
  have h:=localH.constr r (by omega) _ (List.mem_of_getElem? (writes_at ⟨count,by omega⟩ ⟨slot,hslot⟩ ⟨limb,hlimb⟩))
  have flags:=prepared_typed_opcode_selected count hc tr t r pub localH (by omega) 11 (by decide) opcode
  have f0:=flags 0 (by decide);have f1:=flags 1 (by decide);have f2:=flags 2 (by decide)
  have f5:=flags 5 (by decide);have f6:=flags 6 (by decide);have f7:=flags 7 (by decide)
  have f9:=flags 9 (by decide);have f10:=flags 10 (by decide)
  simp only [preparedTypedOpcodeColumn,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Nat.reduceEqDiff,ite_false] at f0 f1 f2 f5 f6 f7 f9 f10
  change tr.cell t r 466=0 at f0
  change tr.cell t r 467=0 at f1
  change tr.cell t r 468=0 at f2
  change tr.cell t r 606=0 at f5
  change tr.cell t r 683=0 at f6
  change tr.cell t r 684=0 at f7
  change tr.cell t r 1280=0 at f9
  change tr.cell t r 1281=0 at f10
  have nh : (r+1)%tr.height t=r+1:=Nat.mod_eq_of_lt nonlast
  have nt : ¬r+1=tr.height t:=by omega
  have top:=hot (slot+1) (by omega)
  have be (base : Nat) (nx : Bool) : (preparedCodeBits base nx).evalWith (rowEnv tr t r pub)=
      preparedCodeLimb (tr.cell t (if nx then (r+1)%tr.height t else r)) base :=
    prepared_code_bits_eval tr t r pub base nx
  simp only [preparedTypedStackWrite,retain,push,write,clear,zero,constOp,addOp,pushed,
    preparedControlTaken,preparedExecGasSuccess,Expr.eval,be,Expr.evalWith] at h
  simp only [rowEnv] at h
  simp only [Bool.false_eq_true,ite_false,ite_true,nt,nh,active,charged,opcode,
    f0,f1,f2,f5,f6,f7,f9,f10,←Fp.ofNat_def] at h

  change preparedCodeLimb (tr.cell t (r+1)) (preparedTypedStackBase slot limb)=_ 
  rw [show 33+slot=32+(slot+1) by omega,top] at h
  split <;> rename_i eq
  all_goals by_cases l:limb=0 <;> simp only [eq,l,ite_true,ite_false] at h ⊢
  all_goals try simp only [preparedTypedStackLimb]
  all_goals simp only [Expr.evalWith,ite_false,Bool.false_eq_true,←Fp.ofNat_def] at h
  all_goals grind
theorem prepared_typed_eqz_stack_tag (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (opcode : tr.cell t r 1282=1)
    (sp : Nat) (hs : sp<9) (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0)
    (slot : Nat) (hslot : slot<8) :
    tr.cell t (r+1) (1074+slot)=
      if slot+1=sp then 0 else tr.cell t r (1074+slot) := by
  have h:=localH.constr r (by omega) _ (List.mem_of_getElem? (types_at ⟨count,by omega⟩ ⟨slot,hslot⟩))
  have flags:=prepared_typed_opcode_selected count hc tr t r pub localH (by omega) 11 (by decide) opcode
  have f0:=flags 0 (by decide);have f1:=flags 1 (by decide);have f2:=flags 2 (by decide)
  have f5:=flags 5 (by decide);have f6:=flags 6 (by decide);have f7:=flags 7 (by decide)
  have f9:=flags 9 (by decide);have f10:=flags 10 (by decide)
  simp only [preparedTypedOpcodeColumn,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Nat.reduceEqDiff,ite_false] at f0 f1 f2 f5 f6 f7 f9 f10
  change tr.cell t r 466=0 at f0
  change tr.cell t r 467=0 at f1
  change tr.cell t r 468=0 at f2
  change tr.cell t r 606=0 at f5
  change tr.cell t r 683=0 at f6
  change tr.cell t r 684=0 at f7
  change tr.cell t r 1280=0 at f9
  change tr.cell t r 1281=0 at f10
  have nh : (r+1)%tr.height t=r+1:=Nat.mod_eq_of_lt nonlast
  have nt : ¬r+1=tr.height t:=by omega
  have top:=hot (slot+1) (by omega)
  simp only [preparedTypedTypeWrite,retain,push,write,clear,zero,constOp,addOp,pushed,
    preparedControlTaken,preparedExecGasSuccess,Expr.eval,Expr.evalWith] at h
  simp only [rowEnv] at h
  simp only [Bool.false_eq_true,ite_false,ite_true,nt,nh,active,charged,opcode,
    f0,f1,f2,f5,f6,f7,f9,f10,←Fp.ofNat_def] at h

  rw [show 33+slot=32+(slot+1) by omega,top] at h
  split <;> rename_i eq
  all_goals simp only [eq,ite_true,ite_false] at h ⊢ <;> grind


/-- Typed successor values: eqz writes an i32 result at the top and preserves
all other slots, including their tags. -/
theorem prepared_typed_eqz_stack_value (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (opcode : tr.cell t r 1282=1)
    (sp : Nat) (hs : sp<9) (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0)
    (slot : Nat) (hslot : slot<8) :
    preparedTypedStackValue (tr.cell t (r+1)) slot=
      if slot+1=sp then .i32 (UInt32.ofNat (tr.cell t r 1284).toNat)
      else preparedTypedStackValue (tr.cell t r) slot := by
  have tag:=prepared_typed_eqz_stack_tag count hc tr t r pub localH nonlast active charged opcode sp hs hot slot hslot
  have limb (i : Nat) (hi : i<4):=prepared_typed_eqz_stack_limb count hc tr t r pub localH nonlast active charged opcode sp hs hot slot i hslot hi
  have a:=limb 0 (by decide);have b:=limb 1 (by decide)
  have c:=limb 2 (by decide);have d:=limb 3 (by decide)
  by_cases top:slot+1=sp
  · simp only [top,ite_true,Nat.reduceEqDiff,ite_false] at a b c d tag ⊢
    have word : preparedTypedStackWord (tr.cell t (r+1)) slot=(tr.cell t r 1284).toNat := by
      change (preparedTypedStackLimb (tr.cell t (r+1)) slot 0).toNat+
        65536*(preparedTypedStackLimb (tr.cell t (r+1)) slot 1).toNat+
        4294967296*(preparedTypedStackLimb (tr.cell t (r+1)) slot 2).toNat+
        281474976710656*(preparedTypedStackLimb (tr.cell t (r+1)) slot 3).toNat=_
      rw [a,b,c,d];rfl
    simp only [preparedTypedStackValue,tag,ite_true,word]
  · simp only [top,ite_false] at a b c d tag ⊢
    have word : preparedTypedStackWord (tr.cell t (r+1)) slot=preparedTypedStackWord (tr.cell t r) slot := by
      unfold preparedTypedStackWord instructionAdd64Word
      rw [a,b,c,d]
    simp only [preparedTypedStackValue,tag,word]


/-- Source-derived stack projection for successful eqz. The opcode, affordable
execution and nonfinal row are explicit; no operand or next-stack premise is used. -/
theorem prepared_typed_eqz_stack_projection (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (opcode : tr.cell t r 1282=1) :
    ∃sp,sp<9 ∧ 0<sp ∧
      (∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) ∧
      preparedTypedStackValue (tr.cell t r) (sp-1)=
        .i64 (UInt64.ofNat (preparedTypedStackWord (tr.cell t r) (sp-1))) ∧
      (∀slot,slot<8 → preparedTypedStackValue (tr.cell t (r+1)) slot=
        if slot+1=sp then .i32 (if preparedTypedStackWord (tr.cell t r) (sp-1)=0 then 1 else 0)
        else preparedTypedStackValue (tr.cell t r) slot) := by
  obtain ⟨sp,hs,positive,hot,tag,result⟩:=prepared_typed_eqz_operand count hc tr t r pub localH (by omega) active charged opcode
  refine ⟨sp,hs,positive,hot,?_,?_⟩
  · simp only [preparedTypedStackValue,tag]
    have ne : (1:Fp)≠0:=by decide
    simp only [ne,ite_false]
  · intro slot hslot
    rw [prepared_typed_eqz_stack_value count hc tr t r pub localH nonlast active charged opcode sp hs hot slot hslot,result]
    by_cases z:preparedTypedStackWord (tr.cell t r) (sp-1)=0 <;> simp only [z,ite_true,ite_false] <;> rfl

end NearCompression
