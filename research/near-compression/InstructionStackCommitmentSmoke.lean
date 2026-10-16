import NearCompression.InstructionStackCommitment
import NearCompression.InstructionOperandSequence
import NearSpecV3.SHA512
open NearSpec NearSpecV3.Wasm NearCompression ZkFormal.Algebra

def stackHash (bs : Bytes) : ByteArray := ⟨(NearSpecV3.sha512 bs).toArray⟩
def ensureStack (b : Bool) (label : String) : IO Unit :=
  unless b do throw (IO.userError label)

def main : IO Unit := do
  let opening : InstructionStackOpening := ⟨#[.i64 77],4,1,2⟩
  let actual := instructionStackOpeningStack opening
  let root := stackHash (encodeInstructionStack actual)
  -- Independently computed with Python hashlib and explicit little-endian encoding.
  ensureStack (hex root == "bb7f65548b4d035cf1375051318247b98d54380b8a0bd5bd96e6adc69a7634e6d26e2a2ec07348502323af0f3305e20c6f0810b6d98f30fe6524faf12f2b76c6")
    "independent stack encoding/SHA512 mismatch"
  let first := instructionAdd32ControlWitness 1 2 0 4
  let second := instructionAdd32ControlWitness 4 3 1 3
  ensureStack (checkInstructionStackPair stackHash root first second opening) "honest stack pair rejected"
  let forged := instructionAdd32ControlWitness 99 3 1 3
  ensureStack (!(checkInstructionStackPair stackHash root first forged opening)) "forged left operand accepted"
  ensureStack (!(checkInstructionStackPair stackHash root first forged {opening with a := 99}))
    "forged operand and opening accepted"
  let wrongRight := instructionAdd32ControlWitness 1 5 0 4
  ensureStack (!(checkInstructionStackPair stackHash root wrongRight second opening)) "forged initial right accepted"
  for changed in [
      {opening with «prefix» := #[.i32 77]},
      {opening with «prefix» := #[]},
      {opening with «prefix» := #[.i64 77, .i32 0]},
      {opening with b := 2, c := 1}] do
    ensureStack (!(checkInstructionStackOpening stackHash root changed)) "changed stack opening accepted"
  ensureStack (!(checkInstructionStackOpening stackHash (stackHash (encodeStackWire actual)) opening))
    "domain separation missing"
  let wrongHeight := instructionAdd32ControlWitness 1 2 0 3
  ensureStack (!(checkInstructionStackPair stackHash root wrongHeight second opening))
    "unbound first stack height"
  let wrongSecondHeight := instructionAdd32ControlWitness 4 3 1 2
  ensureStack (!(checkInstructionStackPair stackHash root first wrongSecondHeight opening))
    "unbound second stack height"
  let validRef : InstructionStackOpening := ⟨#[.ref (some 0)],4,1,2⟩
  let invalidRef : InstructionStackOpening := ⟨#[.ref (some (2^64))],4,1,2⟩
  let validRoot := stackHash (encodeInstructionStack (instructionStackOpeningStack validRef))
  ensureStack (validRoot == stackHash (encodeInstructionStack (instructionStackOpeningStack invalidRef)))
    "test no longer exercises truncated reference encoding"
  ensureStack (checkInstructionStackOpening stackHash validRoot validRef) "valid reference rejected"
  ensureStack (!(checkInstructionStackOpening stackHash validRoot invalidRef))
    "hash-equal out-of-range reference accepted"
  IO.println s!"stack_message_bytes={(encodeInstructionStack actual).length} digest={hex root}"
  IO.println "PASS: honest stack pair and valid reference; 11 forged/malformed checks rejected, including hash-equal out-of-range reference."
