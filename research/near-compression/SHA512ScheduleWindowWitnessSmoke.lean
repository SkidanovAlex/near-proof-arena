import NearCompression.SHA512Schedule
import NearCompression.InstructionSequence
import NearCompression.SHA512ScheduleWindowRun
import NearCompression.SHA512ScheduleWindowWitness
open NearCompression ZkFormal.Air ZkFormal.Algebra NearSpecV3.SHA512

def winEnsure (b : Bool) (msg : String) : IO Unit :=
  unless b do throw (IO.userError msg)
def winBases : List Nat :=
  [1440,576,1776,1840,1904,1968,2032,2096,2160,1232,2224,2288,2352,2416,0,2480]
def winExtra : List Nat := [2,3,4,5,6,7,8,10,11,12,13,15]
def winPairs : List (Nat × Nat) :=
  (List.range 16).flatMap fun i => (List.range 64).map fun bit =>
    ((if i < 15 then winBases.getD (i+1) 0 else 1712)+bit, winBases.getD i 0+bit)
def winLocalConstraints : List Expr :=
  sha512ScheduleConstraints ++ (List.range' 1776 768).map instructionBitConstraint
def winConstraints : List Expr := winLocalConstraints ++ instructionSequenceConstraints winPairs

def winWitness (window : List Nat) : Array Fp :=
  ((List.range 2544).map fun c =>
    if c < 1776 then sha512ScheduleWitness (window.getD 0 0) (window.getD 1 0)
      (window.getD 9 0) (window.getD 14 0) c
    else Fp.ofNat ((window.getD (winExtra.getD ((c-1776)/64) 0) 0) / 2^((c-1776)%64) % 2)).toArray

def winCell (rows : Array (Array Fp)) (r c : Nat) : Fp :=
  (rows[r]?.getD #[])[c]?.getD 0
def winTrace (rows : Array (Array Fp)) (logSize : Nat) : Trace Fp :=
  ⟨fun _ => logSize, fun _ r c => winCell rows r c⟩
def winDecode (row : Nat → Fp) : List Nat := winBases.map (sha512BitsWord row)
def winOutput (row : Nat → Fp) : List Nat :=
  (winDecode row).drop 1 ++ [sha512ScheduleOutput row]
def winCheckLocal (rows : Array (Array Fp)) (r : Nat) : Bool :=
  winLocalConstraints.all fun e => decide (e.evalWith (instructionAddEnv (winCell rows r)) = 0)
def winCheckLinks (rows : Array (Array Fp)) (logSize : Nat) : Bool :=
  (List.range (2^logSize)).all fun r => (instructionSequenceConstraints winPairs).all fun e =>
    decide (e.eval (winTrace rows logSize) 0 r [] = 0)

def witnessTest (initial : List Nat) (logSize : Nat) (mutate : Bool) (expectedTerminal : Option (List Nat) := none) : IO Unit := do
  let mut window := initial
  let mut windows : Array (List Nat) := #[]
  let mut rows : Array (Array Fp) := #[]
  for _ in List.range (2^logSize) do
    windows := windows.push window
    let independent := winWitness window
    let formal := ((List.range 2544).map (sha512ScheduleWindowWitness window)).toArray
    winEnsure (formal == independent) "formal witness differs from independent column construction"
    winEnsure (sha512ScheduleWindow (fun c => formal[c]?.getD 0) == window) "formal witness decode mismatch"
    rows := rows.push formal
    window := nextWindow window
  for r in List.range (2^logSize) do
    winEnsure (sha512ScheduleWindowSequenceTable.constraints.all fun e =>
      decide (e.eval (winTrace rows logSize) 0 r [] = 0)) "formal witness trace violates AIR"
  let constructed := sha512ScheduleWindowWitnessTrace initial logSize
  winEnsure (constructed.log 0 == logSize) "formal trace log mismatch"
  for r in [0,1,2^logSize-1] do
    for c in [0,63,576,639,1232,1295,1440,1503,1712,1775,1776,2543] do
      winEnsure (constructed.cell 0 r c == winCell rows r c) "formal trace constructor differs from materialized witness"
  winEnsure (sha512ScheduleWindowOutput (winCell rows (2^logSize-1)) == window)
    "formal terminal expansion mismatch"
  if let some expected := expectedTerminal then
    winEnsure (window == expected) "independent Python terminal schedule mismatch"
  if mutate then
    for r in [1,64,127] do
      for word in List.range 16 do
        let old := windows[r]?.getD []
        let changed := (old.toArray.set! word ((old.getD word 0+1)%2^64)).toList
        let fresh := ((List.range 2544).map (sha512ScheduleWindowWitness changed)).toArray
        let forged := rows.set! r fresh
        winEnsure (winCheckLocal forged r) "coherent forged row does not satisfy local constraints"
        winEnsure (!((instructionSequenceConstraints winPairs).all fun e =>
          decide (e.eval (winTrace forged logSize) 0 (r-1) [] = 0)))
          "coherent changed schedule word accepted by temporal links"
    let changedFirst := rows.set! 0 (winWitness (List.replicate 16 123))
    winEnsure ((instructionSequenceConstraints winPairs).all fun e =>
      decide (e.eval (winTrace changedFirst logSize) 0 127 [] = 0)) "final links unexpectedly wrap"

def main : IO Unit := do
  winEnsure (winPairs == sha512ScheduleWindowPairs && winConstraints == sha512ScheduleWindowSequenceTable.constraints)
    "independent/formal layout mismatch"
  witnessTest (List.range 16) 1 false
  witnessTest (List.replicate 16 0) 7 false
  witnessTest (List.replicate 16 18446744073709551615) 7 false
  witnessTest (List.range 16) 7 true
  witnessTest [0,1,65535,65536,4294967295,4294967296,9223372036854775807,9223372036854775808,
    18446744073709551615,12297829382473034410,6148914691236517205,255,256,16777215,16777216,42] 7 false (some [18179993632001177244, 4327566410839346159, 17469449822333753024, 6080020478662569841, 9236428244578121696, 12165259796427012576, 747979297162142338, 15924547512368706779, 4665175131300306565, 4153677296697539698, 5900877769732514907, 632354568137282458, 15711229704047455330, 9964900647049106862, 10336081602399603133, 5910644392624655973])
  IO.println "PASS:four128-row andone2-row formal witness traces;all2544columns match independent construction;48locally valid temporal forgeries rejected;final links gated."
