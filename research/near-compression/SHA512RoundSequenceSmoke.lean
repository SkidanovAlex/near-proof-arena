import NearCompression.SHA512RoundWitness
import NearCompression.InstructionSequence
import NearCompression.SHA512RoundSequence
import NearCompression.SHA512SequenceRun
open NearCompression ZkFormal.Air ZkFormal.Algebra
open NearSpecV3.SHA512

def seqEnsure (b : Bool) (msg : String) : IO Unit :=
  unless b do throw (IO.userError msg)

def seqRow (v : Vars) (k w : Nat) : Array Fp :=
  ((List.range 2608).map (sha512RoundWitness v k w)).toArray

def seqCell (rows : Array (Array Fp)) (r c : Nat) : Fp :=
  (rows[r]?.getD #[])[c]?.getD 0

def seqTrace (rows : Array (Array Fp)) : Trace Fp :=
  ⟨fun _ => 2, fun _ r c => seqCell rows r c⟩

def seqWordPairs : List (Nat × Nat) :=
  [(2336,0),(0,64),(64,128),(128,2416),(2544,576),(576,640),(640,704),(704,1168)]
def seqPairs : List (Nat × Nat) :=
  seqWordPairs.flatMap fun p => (List.range 64).map fun bit => (p.1+bit,p.2+bit)
def seqConstraints : List Expr :=
  sha512RoundConstraints ++ instructionSequenceConstraints seqPairs

def seqLocal (rows : Array (Array Fp)) (r : Nat) : Bool :=
  sha512RoundConstraints.all fun e => decide (e.eval (seqTrace rows) 0 r [] = 0)
def seqLinks (rows : Array (Array Fp)) : Bool :=
  (List.range 4).all fun r => (instructionSequenceConstraints seqPairs).all fun e =>
    decide (e.eval (seqTrace rows) 0 r [] = 0)

def seqAlter (v : Vars) (i : Nat) : Vars :=
  let bump := fun n => (n+1)%2^64
  match i with
  | 0 => {v with a := bump v.a}
  | 1 => {v with b := bump v.b}
  | 2 => {v with c := bump v.c}
  | 3 => {v with d := bump v.d}
  | 4 => {v with e := bump v.e}
  | 5 => {v with f := bump v.f}
  | 6 => {v with g := bump v.g}
  | _ => {v with h := bump v.h}

def seqValues (v : Vars) : List Nat := [v.a,v.b,v.c,v.d,v.e,v.f,v.g,v.h]

def seqTest (initial : Vars) : IO Unit := do
  let mut states : Array Vars := #[]
  let mut rows : Array (Array Fp) := #[]
  let mut v := initial
  for i in List.range 4 do
    states := states.push v
    rows := rows.push (seqRow v (i+1) (i+5))
    v := round v (i+1) (i+5)
  for r in List.range 4 do
    seqEnsure (seqConstraints.all fun e => decide (e.eval (seqTrace rows) 0 r [] = 0))
      "honest sequence rejected"
  for r in List.range' 1 3 do
    for word in List.range 8 do
      let altered := seqAlter (states[r]?.getD initial) word
      let forged := rows.set! r (seqRow altered (r+1) (r+5))
      seqEnsure (seqLocal forged r) "coherent state forgery is locally invalid"
      seqEnsure (!(seqLinks forged)) "disconnected state word accepted"
  -- Noncyclic gating must erase every final-row link, even for unrelated row zero.
  let unrelated := rows.set! 0 (seqRow ⟨9,8,7,6,5,4,3,2⟩ 123 456)
  seqEnsure ((instructionSequenceConstraints seqPairs).all fun e =>
    decide (e.eval (seqTrace unrelated) 0 3 [] = 0)) "final-row links did not vanish"
  -- These are deliberate remaining gaps: final-row k/w are free inputs.
  let last := states[3]?.getD initial
  let freeK := rows.set! 3 (seqRow last 99 8)
  let freeW := rows.set! 3 (seqRow last 4 99)
  seqEnsure (seqLocal freeK 3 && seqLinks freeK) "unexpected constant binding"
  seqEnsure (seqLocal freeW 3 && seqLinks freeW) "unexpected schedule binding"
  let out := sha512RoundOutput (seqCell rows 3)
  seqEnsure (seqValues out == seqValues v &&
    seqValues (sha512SequenceRun (seqTrace rows) 0 4) == seqValues v)
    "terminal circuit/fold output mismatch"
  if initial.a == 1 then
    seqEnsure (out.a == 2862924533056080847 && out.e == 14174800055401604298) "independent Python fixture mismatch"

def main : IO Unit := do
  seqEnsure (seqPairs == sha512RoundSequencePairs &&
    seqConstraints == sha512RoundSequenceTable.constraints) "formal layout mismatch"
  seqTest ⟨1,2,3,4,5,6,7,8⟩
  let m := 18446744073709551615
  seqTest ⟨m,m,m,m,m,m,m,m⟩
  IO.println "PASS: 2 four-round traces; 48 locally valid state forgeries rejected; final links gated; free k/w gaps confirmed."
