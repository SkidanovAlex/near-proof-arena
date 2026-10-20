import NearCompression.SHA512ScheduleWindow
import NearCompression.SHA512CombinedRun
open NearCompression ZkFormal.Air ZkFormal.Algebra NearSpecV3.SHA512

def combinedEnsure (b : Bool) (msg : String) : IO Unit :=
  unless b do throw (IO.userError msg)
def combinedExtra : List Nat := [2,3,4,5,6,7,8,10,11,12,13,15]
def combinedWindowWitness (window : List Nat) (c : Nat) : Fp :=
  if c < 1776 then sha512ScheduleWitness (window.getD 0 0) (window.getD 1 0)
    (window.getD 9 0) (window.getD 14 0) c
  else Fp.ofNat ((window.getD (combinedExtra.getD ((c-1776)/64) 0) 0) / 2^((c-1776)%64) % 2)
def combinedWitness (v : Vars) (window : List Nat) (k w : Nat) : Array Fp :=
  ((List.range 5152).map fun c => if c < 2544 then combinedWindowWitness window c
    else sha512RoundWitness v k w (c-2544)).toArray

def combinedWires : List Expr := (List.range 64).map fun bit =>
  .add (.col (1440+bit) false) (.neg (.col (4400+bit) false))
def combinedComponents : List Expr := sha512ScheduleWindowSequenceTable.constraints ++
  sha512RoundSequenceTable.constraints.map (sha512RelocateExpr 2544)
def combinedConstraints : List Expr := combinedComponents ++ combinedWires

def combinedCell (rows : Array (Array Fp)) (r c : Nat) : Fp :=
  (rows[r]?.getD #[])[c]?.getD 0
def combinedTrace (rows : Array (Array Fp)) (logSize : Nat) : Trace Fp :=
  ⟨fun _ => logSize,fun _ r c => combinedCell rows r c⟩
def combinedCheck (rows : Array (Array Fp)) (logSize : Nat) (es : List Expr) : Bool :=
  (List.range (2^logSize)).all fun r => es.all fun e =>
    decide (e.eval (combinedTrace rows logSize) 0 r [] = 0)
def combinedVals (v : Vars) : List Nat := [v.a,v.b,v.c,v.d,v.e,v.f,v.g,v.h]

-- badW changes one message input, then recomputes the entire subsequent round chain.
-- Both independent component sequences therefore remain valid.
def combinedRows (initial : Vars) (initialWindow : List Nat) (logSize : Nat)
    (keys : Nat → Nat) (badW : Option Nat := none) : Array (Array Fp) := Id.run do
  let mut v := initial
  let mut window := initialWindow
  let mut rows := #[]
  for r in List.range (2^logSize) do
    let w := if badW == some r then (window.headD 0+1)%2^64 else window.headD 0
    rows := rows.push (combinedWitness v window (keys r) w)
    v := round v (keys r) w
    window := nextWindow window
  return rows

def combinedTest (initial : Vars) (window : List Nat) : IO Unit := do
  let rows := combinedRows initial window 2 (fun r => r+1)
  combinedEnsure (combinedCheck rows 2 combinedConstraints) "honest combined trace rejected"
  for r in List.range 4 do
    let forged := combinedRows initial window 2 (fun r => r+1) (some r)
    combinedEnsure (combinedCheck forged 2 combinedComponents) "forged component sequence invalid"
    combinedEnsure (!(combinedCheck forged 2 combinedWires)) "unrelated round message accepted"
  let changedK := combinedRows initial window 2 (fun r => if r == 2 then 99 else r+1)
  combinedEnsure (combinedCheck changedK 2 combinedConstraints) "unexpected constant binding"

def main : IO Unit := do
  combinedEnsure (combinedConstraints == sha512CombinedTable.constraints) "formal combined layout mismatch"
  combinedTest ⟨1,2,3,4,5,6,7,8⟩ (List.range 16)
  let m := 18446744073709551615
  combinedTest ⟨m,m,m,m,m,m,m,m⟩ (List.replicate 16 m)
  -- Extra rows satisfy the same recurrence; row79 is the 80-round endpoint.
  -- The index/endpoint, standard constants, padding and feed-forward are supplied by this test.
  let initial := ofList H0
  let window := 9223372036854775808 :: List.replicate 15 0
  let rows := combinedRows initial window 7 (fun r => K.getD r 0)
  combinedEnsure (combinedCheck rows 7 combinedConstraints) "128-row combined trace rejected"
  let out := sha512CombinedOutput (combinedCell rows 79)
  combinedEnsure (sha512CombinedKeys (combinedTrace rows 7) 0 0 80 == K) "decoded constant fixture mismatch"
  combinedEnsure (combinedVals out == combinedVals (rounds initial K window)) "actual 80-round mismatch"
  let digestWords := (H0.zip (combinedVals out)).map fun p => add64 p.1 p.2
  combinedEnsure (digestWords == [14953042807679334589, 17389568388844322823, 15429583033687545308, 9508410676032104910, 5174866029046002352, 18411586994116160559, 7185829369460390529, 11905321118701443646]) "independent hashlib empty digest mismatch"
  IO.println "PASS: 2 four-row traces,8 independently valid but disconnected component traces rejected,128-row trace with80-round hashlib fixture;free k gap confirmed."
