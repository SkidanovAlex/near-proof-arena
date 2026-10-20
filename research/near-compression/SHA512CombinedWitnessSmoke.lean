import NearCompression.SHA512ScheduleWindow
import NearCompression.SHA512CombinedRun
import NearCompression.SHA512CombinedWitness
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

def witnessCombinedTest (initial : Vars) (initialWindow : List Nat) (keys : Nat → Nat)
    (logSize : Nat) (mutate : Bool) : IO Unit := do
  let mut v := initial
  let mut window := initialWindow
  let mut states : Array Vars := #[]
  let mut windows : Array (List Nat) := #[]
  let mut rows : Array (Array Fp) := #[]
  for r in List.range (2^logSize) do
    states := states.push v
    windows := windows.push window
    let formal := ((List.range 5152).map (sha512CombinedWitnessRow v window (keys r))).toArray
    let independent := combinedWitness v window (keys r) (window.headD 0)
    combinedEnsure (formal == independent) "formal combined witness column mismatch"
    rows := rows.push formal
    combinedEnsure (combinedVals (sha512CombinedVars (combinedCell rows r)) == combinedVals v &&
      sha512CombinedWindow (combinedCell rows r) == window && sha512CombinedK (combinedCell rows r) == keys r)
      "formal combined input decoding mismatch"
    v := round v (keys r) (window.headD 0)
    window := nextWindow window
  combinedEnsure (combinedCheck rows logSize sha512CombinedTable.constraints) "formal combined trace rejected"
  combinedEnsure (combinedVals (sha512CombinedOutput (combinedCell rows (2^logSize-1))) == combinedVals v)
    "formal combined final output mismatch"
  let trace := sha512CombinedWitnessTrace initial initialWindow keys logSize
  combinedEnsure (trace.log 0 == logSize) "formal combined log mismatch"
  for r in [0,1,2^logSize-1] do
    for col in [0,1440,1712,1776,2543,2544,2608,2672,3120,3184,3248,3712,4116,4400,4880,4960,5088,5151] do
      combinedEnsure (trace.cell 0 r col == combinedCell rows r col) "formal trace constructor mismatch"
  if mutate then
    let digestWords := (H0.zip (combinedVals (sha512CombinedOutput (combinedCell rows 79)))).map fun pair => add64 pair.1 pair.2
    combinedEnsure (digestWords == [14953042807679334589,17389568388844322823,15429583033687545308,
      9508410676032104910,5174866029046002352,18411586994116160559,7185829369460390529,11905321118701443646])
      "independent hashlib empty-message endpoint mismatch"
    for r in [1,79,127] do
      let forged := combinedRows initial initialWindow logSize keys (some r)
      combinedEnsure (combinedCheck forged logSize combinedComponents) "message forgery violates component sequences"
      combinedEnsure (!(combinedCheck forged logSize combinedWires)) "substituted scheduled word accepted"
    let state := states[64]?.getD initial
    for word in List.range 8 do
      let values := combinedVals state
      let altered := ofList ((values.toArray.set! word ((values.getD word 0+1)%2^64)).toList)
      let win := windows[64]?.getD []
      let fresh := ((List.range 5152).map (sha512CombinedWitnessRow altered win (keys 64))).toArray
      let forged := rows.set! 64 fresh
      combinedEnsure (sha512ScheduleWindowTable.constraints.all fun e =>
        decide (e.eval (combinedTrace forged logSize) 0 64 [] = 0)) "forged schedule invalid locally"
      combinedEnsure ((sha512RoundTable.constraints.map (sha512RelocateExpr 2544) ++ combinedWires).all fun e =>
        decide (e.eval (combinedTrace forged logSize) 0 64 [] = 0)) "forged round invalid locally"
      combinedEnsure (!(sha512CombinedTable.constraints.all fun e =>
        decide (e.eval (combinedTrace forged logSize) 0 63 [] = 0))) "disconnected state word accepted"

def main : IO Unit := do
  combinedEnsure (combinedConstraints == sha512CombinedTable.constraints) "formal combined layout mismatch"
  witnessCombinedTest ⟨1,2,3,4,5,6,7,8⟩ (List.range 16) (fun r => (r+1)%2^64) 1 false
  witnessCombinedTest (ofList H0) (9223372036854775808 :: List.replicate 15 0)
    (fun r => K.getD r 0) 7 true
  let m := 18446744073709551615
  witnessCombinedTest ⟨m,m,m,m,m,m,m,m⟩ (List.replicate 16 m) (fun r => (r*123456789+17)%2^64) 7 false
  IO.println "PASS:two128-row andone2-row formal combined witnesses;all5152columns match independent constructor;3coherent message substitutions and8locally valid state forgeries rejected."
