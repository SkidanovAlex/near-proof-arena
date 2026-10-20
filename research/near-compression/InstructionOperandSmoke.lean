import NearCompression.InstructionOperandSequence
import NearCompression.InstructionStackPair
open NearCompression NearSpecV3.Wasm ZkFormal.Air ZkFormal.Algebra

def ensureOperand (b : Bool) (label : String) : IO Unit :=
  unless b do throw (IO.userError label)

def operandTrace (log : Nat) (rows : Array (Nat → Fp)) : Trace Fp :=
  { log := fun _ => log, cell := fun _ r => rows[r]?.getD (fun _ => 0) }

def checkOperandTable (table : Table) (tr : Trace Fp) : Bool :=
  (List.range (tr.height 0)).all fun r =>
    table.constraints.all fun e => decide (e.eval tr 0 r [] = 0)

def main : IO Unit := do
  let honest := operandTrace 2 #[instructionAdd32ControlWitness 4 5 65534 5,
    instructionAdd32ControlWitness 3 9 65535 4,
    instructionAdd32ControlWitness 2 12 65536 3,
    instructionAdd32ControlWitness 1 14 65537 2]
  ensureOperand (checkOperandTable instructionAdd32OperandTable honest) "honest operand chain rejected"
  let oldForgery := operandTrace 1 #[instructionAdd32ControlWitness 1 2 0 3,
    instructionAdd32ControlWitness 4 5 1 2]
  ensureOperand (checkOperandTable instructionAdd32SequenceTable oldForgery) "old gap changed"
  ensureOperand (!(checkOperandTable instructionAdd32OperandTable oldForgery)) "old operand forgery accepted"
  for changed in [4,65539,4294967295] do
    let bad := operandTrace 1 #[instructionAdd32ControlWitness 1 2 0 3,
      instructionAdd32ControlWitness 4 (UInt32.ofNat changed) 1 2]
    ensureOperand (checkOperandTable instructionAdd32SequenceTable bad) "forgery is not locally valid"
    ensureOperand (!(checkOperandTable instructionAdd32OperandTable bad)) "coherent right-operand forgery accepted"
  -- The new links do not authenticate the remaining initial stack values.
  let leftForgery := operandTrace 1 #[instructionAdd32ControlWitness 1 2 0 3,
    instructionAdd32ControlWitness 99 3 1 2]
  ensureOperand (checkOperandTable instructionAdd32OperandTable leftForgery)
    "left-binding gap changed; revise scope"
  ensureOperand (instructionAddWord (leftForgery.cell 0 1) 4 5 == 102) "forged result mismatch"
  let baseState : St := {
    stack := #[.i64 77], pages := #[], globals := #[], table := #[], tableMax := 0,
    elems := #[], datas := #[], stackRem := 1000, gas := Gas.init 1000 }
  let initial := pushV (pushV (pushV baseState (.i32 4)) (.i32 1)) (.i32 2)
  match instructionTwoAdds initial with
  | .ok result =>
    ensureOperand (topCount result == 7 && result.stack.size == 2) "actual stack result mismatch"
    match result.stack[0]? with
    | some (.i64 77) => pure ()
    | _ => throw (IO.userError "stack prefix changed")
  | .error e => throw (IO.userError e)
  IO.println "PASS: honest operand chain, known gap plus 3 coherent right-operand forgeries rejected, actual two-add stack result7; left-binding gap reproduced (claimed102)."
