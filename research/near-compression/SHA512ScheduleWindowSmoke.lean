import NearCompression.SHA512Schedule
import NearCompression.InstructionSequence
import NearCompression.SHA512ScheduleWindowRun
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

def winTest (initial : List Nat) (logSize : Nat) (mutate : Bool) : IO Unit := do
  let mut window := initial
  let mut windows : Array (List Nat) := #[]
  let mut rows : Array (Array Fp) := #[]
  for _ in List.range (2^logSize) do
    windows := windows.push window
    rows := rows.push (winWitness window)
    window := nextWindow window
  for r in List.range (2^logSize) do
    winEnsure (winConstraints.all fun e => decide (e.eval (winTrace rows logSize) 0 r [] = 0))
      "honest window trace rejected"
    winEnsure (winDecode (winCell rows r) == windows[r]?.getD []) "window decoding mismatch"
  winEnsure (winOutput (winCell rows (2^logSize-1)) == window &&
    sha512ScheduleWindowOutput (winCell rows (2^logSize-1)) == window &&
    sha512ScheduleWindowRun (winDecode (winCell rows 0)) (2^logSize) == window)
    "terminal window mismatch"
  if mutate then
    for r in List.range' 1 (2^logSize-1) do
      for word in List.range 16 do
        let old := windows[r]?.getD []
        let altered := (old.toArray.set! word ((old.getD word 0+1)%2^64)).toList
        let forged := rows.set! r (winWitness altered)
        winEnsure (winCheckLocal forged r) "window forgery invalid locally"
        winEnsure (!(winCheckLinks forged logSize)) "disconnected window word accepted"
  let unrelated := rows.set! 0 (winWitness (List.replicate 16 123))
  winEnsure ((instructionSequenceConstraints winPairs).all fun e =>
    decide (e.eval (winTrace unrelated logSize) 0 (2^logSize-1) [] = 0)) "final window links wrap"
  if logSize == 6 then
    winEnsure (window.getD 15 0 == 7471377847041668307) "independent Python W79 mismatch"

def main : IO Unit := do
  winEnsure (winPairs == sha512ScheduleWindowPairs &&
    winLocalConstraints == sha512ScheduleWindowTable.constraints &&
    winConstraints == sha512ScheduleWindowSequenceTable.constraints)
    "formal window layout mismatch"
  winTest (List.range 16) 2 true
  winTest (List.replicate 16 18446744073709551615) 2 true
  winTest (List.range 16) 6 false
  IO.println "PASS: 2 four-row window traces,96 locally valid window forgeries rejected,64 constrained expansions,final links gated."
