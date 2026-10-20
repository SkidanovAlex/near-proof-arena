import NearCompression.PreparedMemorySource
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def preparedMemoryOpcode (i : Nat) : Nat :=
  [40,41,44,45,46,47,48,49,50,51,52,53,54,55,58,59,60,61,62].getD i 0
def preparedMemoryIs64 (i : Nat) : Bool :=
  [false,true,false,false,false,false,true,true,true,true,true,true,false,true,false,false,true,true,true].getD i false
def preparedMemorySigned (i : Nat) : Bool :=
  [false,false,true,false,true,false,true,false,true,false,true,false,false,false,false,false,false,false,false].getD i false
def preparedMemoryWrite (i : Nat) : Bool := decide (12≤i)

def preparedMemoryResultBit (selected bit : Nat) : Expr :=
  if preparedMemoryWrite selected || decide ((if preparedMemoryIs64 selected then 64 else 32)≤bit) then .const 0
  else if bit<8*preparedMemoryWidth selected then .col (293+bit) false
  else if preparedMemorySigned selected then .col (293+8*preparedMemoryWidth selected-1) false
  else .const 0

private def addSimple (a b : Expr) : Expr :=
  match a,b with
  | .const 0,b=>b
  | a,.const 0=>a
  | a,b=>.add a b
private def mulSimple (a b : Expr) : Expr :=
  match a,b with
  | .const 0,_=>.const 0
  | _,.const 0=>.const 0
  | .const 1,b=>b
  | a,.const 1=>a
  | a,b=>.mul a b
private def negSimple (a : Expr) : Expr := match a with
  | .const 0=>.const 0
  | a=>.neg a
private def opReduce (selected : Nat) : Expr→Expr
  | .col c false=>if c<19 then .const (if c=selected then 1 else 0) else .col c false
  | .add a b=>addSimple (opReduce selected a) (opReduce selected b)
  | .mul a b=>mulSimple (opReduce selected a) (opReduce selected b)
  | .neg a=>negSimple (opReduce selected a)
  | e=>e
private theorem add_eval (a b : Expr) (row : Nat→Fp) :
    (addSimple a b).evalWith (preparedGasEnv row [])=
      a.evalWith (preparedGasEnv row [])+b.evalWith (preparedGasEnv row []) := by
  have z : Fp.ofNat 0=(0:Fp):=rfl
  unfold addSimple
  split <;> simp_all [Expr.evalWith,preparedGasEnv,instructionAddEnv] <;> try simp_all only [z]
  all_goals grind
private theorem mul_eval (a b : Expr) (row : Nat→Fp) :
    (mulSimple a b).evalWith (preparedGasEnv row [])=
      a.evalWith (preparedGasEnv row [])*b.evalWith (preparedGasEnv row []) := by
  have z : Fp.ofNat 0=(0:Fp):=rfl
  have o : Fp.ofNat 1=(1:Fp):=rfl
  unfold mulSimple
  split <;> simp_all [Expr.evalWith,preparedGasEnv,instructionAddEnv] <;> try simp_all only [z,o]
  all_goals grind
private theorem neg_eval (a : Expr) (row : Nat→Fp) :
    (negSimple a).evalWith (preparedGasEnv row [])= -a.evalWith (preparedGasEnv row []) := by
  have z : Fp.ofNat 0=(0:Fp):=rfl
  unfold negSimple
  split <;> simp_all [Expr.evalWith,preparedGasEnv,instructionAddEnv] <;> try simp_all only [z]
  all_goals grind
private theorem reduce_eval (e : Expr) (row : Nat→Fp) (selected : Nat)
    (hot:∀i,i<19→row i=if i=selected then 1 else 0) :
    (opReduce selected e).evalWith (preparedGasEnv row [])=e.evalWith (preparedGasEnv row []) := by
  induction e with
  | const n=>rfl
  | col c nx=>
    cases nx
    · simp only [opReduce]
      split
      · rename_i small
        change Fp.ofNat (if c=selected then 1 else 0)=row c
        rw [hot c small]
        split <;> rfl
      · rfl
    · rfl
  | add a b ia ib=>rw [opReduce,add_eval,ia,ib];rfl
  | mul a b ia ib=>rw [opReduce,mul_eval,ia,ib];rfl
  | neg a ia=>rw [opReduce,neg_eval,ia];rfl
  | pub _ | isFirst | isLast | isTransition=>rfl

private theorem result_shape : ∀selected:Fin 19,∀bit:Fin 64,
    opReduce selected (preparedMemoryLiteralConstraints[488+4*bit.val]'(by change 488+4*bit.val<741;omega))=
      addSimple (.col (357+bit.val) false) (negSimple (preparedMemoryResultBit selected bit)) := by decide

private theorem raw_shape : ∀selected:Fin 19,∀bit:Fin 64,
    bit.val≥8*preparedMemoryWidth selected→
    opReduce selected (preparedMemoryLiteralConstraints[485+4*bit.val]'(by change 485+4*bit.val<741;omega))=.col (293+bit.val) false := by decide

private theorem result_local : ∀b:Fin 64,instructionLocalExpr (preparedMemoryLiteralConstraints[488+4*b.val]'(by change 488+4*b.val<741;omega)) := by decide

/-- Selected-opcode simplification is checked against the exact literal
result equations, including sign replication and the i32 high-half zeros. -/
theorem prepared_memory_result_bits (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedMemoryLiteralTable tr t pub) (hr:r<tr.height t)
    (selected : Fin 19) (hot:∀i,i<19→tr.cell t r i=if i=selected.val then 1 else 0)
    (bit : Nat) (hb:bit<64) :
    tr.cell t r (357+bit)=(preparedMemoryResultBit selected bit).evalWith (preparedGasEnv (tr.cell t r) []) := by
  let e:=preparedMemoryLiteralConstraints[488+4*bit]'(by change 488+4*bit<741;omega)
  have h:=localH.constr r hr e (List.getElem_mem (by change 488+4*bit<741;omega))
  have red:=reduce_eval e (tr.cell t r) selected hot
  have loc : instructionLocalExpr e := by
    exact result_local ⟨bit,hb⟩
  rw [instruction_local_eval e tr t r pub loc] at h
  have zero : (opReduce selected e).evalWith (preparedGasEnv (tr.cell t r) [])=0 := red.trans h
  rw [result_shape selected ⟨bit,hb⟩,add_eval,neg_eval] at zero
  change tr.cell t r (357+bit)+ -((preparedMemoryResultBit selected bit).evalWith (preparedGasEnv (tr.cell t r) []))=0 at zero
  grind

private theorem raw_local : ∀b:Fin 64,instructionLocalExpr
    (preparedMemoryLiteralConstraints[485+4*b.val]'(by change 485+4*b.val<741;omega)) := by decide
private theorem store_shape : ∀selected:Fin 19,∀bit:Fin 64,12≤selected.val→
    opReduce selected (preparedMemoryLiteralConstraints[486+4*bit.val]'(by change 486+4*bit.val<741;omega))=
      addSimple (.col (293+bit.val) false) (negSimple
        (if bit.val<8*preparedMemoryWidth selected then .col (229+bit.val) false else .const 0)) := by decide
private theorem store_local : ∀b:Fin 64,instructionLocalExpr
    (preparedMemoryLiteralConstraints[486+4*b.val]'(by change 486+4*b.val<741;omega)) := by decide

theorem prepared_memory_raw_high_zero (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedMemoryLiteralTable tr t pub) (hr:r<tr.height t)
    (selected : Fin 19) (hot:∀i,i<19→tr.cell t r i=if i=selected.val then 1 else 0)
    (bit : Nat) (hb:bit<64) (high:8*preparedMemoryWidth selected≤bit) :
    tr.cell t r (293+bit)=0 := by
  let e:=preparedMemoryLiteralConstraints[485+4*bit]'(by change 485+4*bit<741;omega)
  have h:=localH.constr r hr e (List.getElem_mem (by change 485+4*bit<741;omega))
  rw [instruction_local_eval e tr t r pub (raw_local ⟨bit,hb⟩)] at h
  have zero : (opReduce selected e).evalWith (preparedGasEnv (tr.cell t r) [])=0 :=
    (reduce_eval e (tr.cell t r) selected hot).trans h
  rw [raw_shape selected ⟨bit,hb⟩ high] at zero
  exact zero

theorem prepared_memory_store_raw_bits (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedMemoryLiteralTable tr t pub) (hr:r<tr.height t)
    (selected : Fin 19) (hot:∀i,i<19→tr.cell t r i=if i=selected.val then 1 else 0)
    (store:12≤selected.val) (bit : Nat) (hb:bit<64) :
    tr.cell t r (293+bit)=if bit<8*preparedMemoryWidth selected then tr.cell t r (229+bit) else 0 := by
  let e:=preparedMemoryLiteralConstraints[486+4*bit]'(by change 486+4*bit<741;omega)
  have h:=localH.constr r hr e (List.getElem_mem (by change 486+4*bit<741;omega))
  rw [instruction_local_eval e tr t r pub (store_local ⟨bit,hb⟩)] at h
  have zero : (opReduce selected e).evalWith (preparedGasEnv (tr.cell t r) [])=0 :=
    (reduce_eval e (tr.cell t r) selected hot).trans h
  rw [store_shape selected ⟨bit,hb⟩ store,add_eval,neg_eval] at zero
  by_cases low:bit<8*preparedMemoryWidth selected
  · simp only [if_pos low] at zero ⊢
    change tr.cell t r (293+bit)+ -tr.cell t r (229+bit)=0 at zero
    grind
  · simp only [if_neg low] at zero ⊢
    change tr.cell t r (293+bit)+ -(0:Fp)=0 at zero
    grind
end NearCompression
