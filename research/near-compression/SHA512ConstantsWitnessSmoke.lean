import NearCompression.SHA512ScheduleWindow
import NearCompression.SHA512CombinedRun
import NearCompression.SHA512Constants
import NearCompression.SHA512ConstantsWitness
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


def constRows (base : Array (Array Fp)) (phase : Nat → Nat → Fp) : Array (Array Fp) :=
  ((List.range base.size).map fun r => (base[r]?.getD #[]) ++
    ((List.range 128).map (phase r)).toArray).toArray

def constHonestPhase (r i : Nat) : Fp := if i == r then 1 else 0

def constFirst : List Expr := (List.range 128).map fun i =>
  .mul .isFirst (.add (.col (5152+i) false) (.neg (.const (if i == 0 then 1 else 0))))
def constStep : List Expr := (List.range 128).map fun i =>
  .mul .isTransition (.add (.col (5152+i) true)
    (.neg (if i == 0 then .const 0 else .col (5152+i-1) false)))
def constLast : Expr := .mul .isLast (.add (.col 5279 false) (.neg (.const 1)))
def constSum (limb : Nat) : Expr := (List.range 128).foldr
  (fun i acc => .add (.mul (.col (5152+i) false) (.const (K.getD i 0 / 65536^limb % 65536))) acc)
  (.const 0)
def constWords : List Expr := (List.range 4).map fun limb =>
  .add (.col (4116+limb) false) (.neg (constSum limb))
def constConstraints : List Expr := constFirst ++ constStep ++ [constLast] ++ constWords

def constFormal : List Expr := sha512ConstantsConstraints.drop sha512CombinedConstraints.length

def constVerify (rows : Array (Array Fp)) (logSize : Nat) (expected : Bool) : IO Unit := do
  combinedEnsure (constFormal.length == constConstraints.length) "constant constraint count mismatch"
  combinedEnsure ((List.range (2^logSize)).all fun r =>
    (List.range constConstraints.length).all fun i =>
      decide ((constConstraints.getD i (.const 0)).eval (combinedTrace rows logSize) 0 r [] =
        (constFormal.getD i (.const 0)).eval (combinedTrace rows logSize) 0 r []))
    "independent and formal constant evaluations disagree"
  combinedEnsure (combinedCheck rows logSize constFormal == expected) "formal constant acceptance mismatch"

def constantsWitnessTest (initial : Vars) (initialWindow : List Nat) (mutate : Bool) : IO Unit := do
  let independent := constRows (combinedRows initial initialWindow 7 (fun r => K.getD r 0)) constHonestPhase
  let mut v := initial
  let mut window := initialWindow
  let mut rows : Array (Array Fp) := #[]
  for r in List.range 128 do
    let formal := ((List.range 5280).map (sha512ConstantsWitnessAt v window r)).toArray
    combinedEnsure (formal == independent[r]?.getD #[]) "formal constant witness column mismatch"
    rows := rows.push formal
    v := round v (K.getD r 0) (window.headD 0)
    window := nextWindow window
  combinedEnsure (combinedCheck rows 7 sha512ConstantsTable.constraints) "formal constant witness rejected"
  constVerify rows 7 true
  let trace := sha512ConstantsWitnessTrace initial initialWindow
  combinedEnsure (trace.log 0 == 7) "constant trace height mismatch"
  for r in [0,1,79,80,127] do
    for c in [0,1440,2544,4116,4117,4118,4119,4880,5151,5152,5231,5279] do
      combinedEnsure (trace.cell 0 r c == combinedCell rows r c) "formal trace/materialized witness mismatch"
  combinedEnsure (combinedVals (sha512CombinedVars (combinedCell rows 0)) == combinedVals initial &&
    sha512CombinedWindow (combinedCell rows 0) == initialWindow) "initial constant trace decoding mismatch"
  combinedEnsure (combinedVals (sha512CombinedOutput (combinedCell rows 79)) ==
    combinedVals (rounds initial K initialWindow)) "actual eighty-round endpoint mismatch"
  if mutate then
    for r in [0,1,79,80,127] do
      let forgedBase := combinedRows initial initialWindow 7
        (fun i => if i == r then (K.getD i 0+1)%2^64 else K.getD i 0)
      let forged := constRows forgedBase constHonestPhase
      combinedEnsure (combinedCheck forged 7 combinedConstraints) "coherent changed key violates combined AIR"
      constVerify forged 7 false
    let phases : List (Nat → Nat → Fp) := [
      (fun r i => constHonestPhase (r+1) i),
      (fun r i => constHonestPhase (if r == 64 then 63 else r) i),
      (fun r i => constHonestPhase (if r == 64 then 65 else r) i),
      (fun r i => if r == 64 && i == 64 then 2 else constHonestPhase r i),
      (fun r i => constHonestPhase (if r == 127 then 126 else r) i)]
    let base := combinedRows initial initialWindow 7 (fun r => K.getD r 0)
    for phase in phases do
      constVerify (constRows base phase) 7 false
    let short := constRows (combinedRows initial initialWindow 6 (fun r => K.getD r 0)) constHonestPhase
    combinedEnsure (combinedCheck short 6 combinedConstraints) "short trace violates old combined AIR"
    constVerify short 6 false

def main : IO Unit := do
  constantsWitnessTest (ofList H0) (9223372036854775808 :: List.replicate 15 0) true
  let m := 18446744073709551615
  constantsWitnessTest ⟨m,m,m,m,m,m,m,m⟩ (List.range 16) false
  IO.println "PASS:two128-row formal constants witnesses;all5280columns match independentconstructor;5coherent key forgeries,5phase forgeries,andshort64-row endpoint rejected."
