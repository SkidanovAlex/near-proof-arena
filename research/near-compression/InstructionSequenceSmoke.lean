import NearCompression.InstructionSequence
open NearCompression NearSpecV3.Wasm ZkFormal.Air ZkFormal.Algebra

def ensureSequence (b : Bool) (label : String) : IO Unit :=
  unless b do throw (IO.userError label)

def sequenceTrace (log : Nat) (rows : Array (Nat → Fp)) : Trace Fp :=
  { log := fun _ => log, cell := fun _ r => rows[r]?.getD (fun _ => 0) }

def checkTraceTable (table : Table) (tr : Trace Fp) : Bool :=
  (List.range (tr.height 0)).all fun r =>
    table.constraints.all fun e => decide (e.eval tr 0 r [] = 0)

def sequenceRows : Array (Nat → Fp) := #[
  instructionAdd32ControlWitness 4 5 65534 5,
  instructionAdd32ControlWitness 3 9 65535 4,
  instructionAdd32ControlWitness 2 12 65536 3,
  instructionAdd32ControlWitness 1 14 65537 2]

/-- Direct execution check on the actual Wasm numeric interpreter. -/
def checkActualReduction : IO Unit := do
  let mut s : St := {
    stack := #[.i32 1, .i32 2, .i32 3, .i32 4, .i32 5],
    pages := #[], globals := #[], table := #[], tableMax := 0,
    elems := #[], datas := #[], stackRem := 1000, gas := Gas.init 1000 }
  for r in List.range 4 do
    match execNum s 0x6A with
    | .ok t =>
      let row := sequenceRows[r]!
      ensureSequence (topCount t == instructionAddWord row 4 5) "actual reduction output mismatch"
      ensureSequence (t.stack.size == (row 111).toNat) "actual reduction height mismatch"
      s := t
    | .error e => throw (IO.userError e)
  ensureSequence (topCount s == 15 && s.stack.size == 1) "actual reduction final mismatch"

def main : IO Unit := do
  let tr := sequenceTrace 2 sequenceRows
  ensureSequence (checkTraceTable instructionAdd32SequenceTable tr) "honest trace rejected"
  checkActualReduction
  let badPc := sequenceRows.set! 2 (instructionAdd32ControlWitness 2 12 100 3)
  let badHeight := sequenceRows.set! 2 (instructionAdd32ControlWitness 2 12 65536 4)
  for rows in [badPc,badHeight] do
    let bad := sequenceTrace 2 rows
    ensureSequence (checkTraceTable instructionAdd32ControlTable bad) "discontinuity broke local row"
    ensureSequence (!(checkTraceTable instructionAdd32SequenceTable bad)) "discontinuity accepted"
  -- The last row's post-PC differs from the first row's pre-PC. The selector
  -- must disable cyclic wraparound rather than force the trace into a loop.
  ensureSequence (instructionAddWord (tr.cell 0 3) 107 108 !=
    instructionAddWord (tr.cell 0 0) 105 106) "test has no wrap mismatch"
  for e in instructionSequenceConstraints instructionAdd32SequencePairs do
    ensureSequence (decide (e.eval tr 0 3 [] = 0)) "final-row link not disabled"
  -- Expected acceptance documents a remaining gap: PC/height continuity does
  -- not authenticate operands. Actual second addition should use prior result3.
  let disconnected := sequenceTrace 1 #[instructionAdd32ControlWitness 1 2 0 3,
    instructionAdd32ControlWitness 4 5 1 2]
  ensureSequence (checkTraceTable instructionAdd32SequenceTable disconnected)
    "operand-gap regression changed; update expected scope"
  ensureSequence (instructionAddWord (disconnected.cell 0 1) 4 5 == 9)
    "disconnected witness output mismatch"
  ensureSequence (decide (Num.binop 32 0 4 3 = some 7)) "actual connected result mismatch"
  IO.println "PASS: 4-row trace and actual reduction, 2 locally-valid discontinuities rejected, 3 final-row links disabled; operand-binding gap reproduced."
