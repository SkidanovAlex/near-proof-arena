import NearCompression.SHA512ScheduleWindow
import NearCompression.SHA512CombinedRun
import NearCompression.SHA512Constants
import NearCompression.SHA512FeedForward
import NearCompression.SHA512BlockDecode
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


def ffInputBases : List Nat := [2544,2608,2672,4960,3120,3184,3248,3712]
def ffOutputBases : List Nat := [4880,2544,2608,2672,5088,3120,3184,3248]
def ffAddConstraints : List Expr := (List.range 8).flatMap fun i =>
  instructionAdd64Constraints.map (sha512RelocateExpr (5280+208*i))
def ffFirst : List Expr := (List.range 8).flatMap fun i => (List.range 64).map fun b =>
  .mul .isFirst (.add (.col (5296+208*i+b) false) (.neg (.col (ffInputBases.getD i 0+b) false)))
def ffStepPairs : List (Nat × Nat) := (List.range 8).flatMap fun i => (List.range 64).map fun b =>
  (5296+208*i+b,5296+208*i+b)
def ffCurrent : List Expr := (List.range 8).flatMap fun i => (List.range 64).map fun b =>
  .add (.col (5360+208*i+b) false) (.neg (.col (ffOutputBases.getD i 0+b) false))
def ffRelations : List Expr := ffFirst ++ instructionSequenceConstraints ffStepPairs ++ ffCurrent
def ffConstraints : List Expr := sha512ConstantsConstraints ++ ffAddConstraints ++ ffRelations

def ffRows (base : Array (Array Fp)) (initialWords : List Nat) : Array (Array Fp) :=
  ((List.range 128).map fun r =>
    let output := combinedVals (sha512CombinedOutput (combinedCell base r))
    (base[r]?.getD #[]) ++ ((List.range 1664).map fun c =>
      instructionAdd64Witness (UInt64.ofNat (initialWords.getD (c/208) 0))
        (UInt64.ofNat (output.getD (c/208) 0)) (c%208)).toArray).toArray

def ffReplace (rows : Array (Array Fp)) (r word a b : Nat) : Array (Array Fp) :=
  let fresh := instructionAdd64Witness (UInt64.ofNat a) (UInt64.ofNat b)
  let base := 5280+208*word
  rows.set! r (((List.range 6944).map fun c =>
    if base ≤ c && c < base+208 then fresh (c-base) else combinedCell rows r c).toArray)

def ffLocal (rows : Array (Array Fp)) (r word : Nat) : Bool :=
  instructionAdd64Constraints.all fun e => decide
    (e.evalWith (instructionAddEnv (fun c => combinedCell rows r (5280+208*word+c))) = 0)

def main : IO Unit := do
  combinedEnsure (ffConstraints == sha512FeedForwardTable.constraints) "formal feed-forward layout mismatch"
  let window := 9223372036854775808 :: List.replicate 15 0
  let base := constRows (combinedRows (ofList H0) window 7 (fun r => K.getD r 0)) constHonestPhase
  let rows := ffRows base H0
  combinedEnsure (combinedCheck rows 7 ffConstraints) "honest feed-forward trace rejected"
  for word in List.range 8 do
    let bumped := (H0.getD word 0+1)%2^64
    let changedH := (H0.toArray.set! word bumped).toList
    let forgedInitial := ffRows base changedH
    for r in List.range 128 do
      combinedEnsure (ffLocal forgedInitial r word) "coherent initial-word forgery invalid locally"
    combinedEnsure (!(combinedCheck forgedInitial 7 ffRelations)) "substituted initial state accepted"
    let b64 := (combinedVals (sha512CombinedOutput (combinedCell rows 64))).getD word 0
    let forgedMiddle := ffReplace rows 64 word bumped b64
    combinedEnsure (ffLocal forgedMiddle 64 word) "coherent middle-word forgery invalid locally"
    combinedEnsure (!(combinedCheck forgedMiddle 7 ffRelations)) "drifting initial word accepted"
    let b79 := (combinedVals (sha512CombinedOutput (combinedCell rows 79))).getD word 0
    let forgedResult := ffReplace rows 79 word (H0.getD word 0) ((b79+1)%2^64)
    combinedEnsure (ffLocal forgedResult 79 word) "coherent result-word forgery invalid locally"
    combinedEnsure (!(combinedCheck forgedResult 7 ffRelations)) "unrelated round result accepted"
  let digestWords := sha512FeedForwardOutput (combinedCell rows 79)
  let block := sha512DecodedBlock (combinedCell rows 0)
  combinedEnsure (block == 128 :: List.replicate 127 0 && block.all (fun b => b < 256))
    "decoded padded empty block mismatch"
  combinedEnsure (digestWords == compress H0 block) "actual compression mismatch"
  combinedEnsure (digestWords == [14953042807679334589,17389568388844322823,15429583033687545308,
    9508410676032104910,5174866029046002352,18411586994116160559,7185829369460390529,11905321118701443646])
    "independent hashlib empty digest mismatch"
  let abcWindow := [7017280570803617792] ++ List.replicate 14 0 ++ [24]
  let abcBase := constRows (combinedRows (ofList H0) abcWindow 7 (fun r => K.getD r 0)) constHonestPhase
  let abcRows := ffRows abcBase H0
  combinedEnsure (combinedCheck abcRows 7 ffConstraints) "honest abc trace rejected"
  let abcBlock := sha512DecodedBlock (combinedCell abcRows 0)
  combinedEnsure (abcBlock == [97,98,99,128] ++ List.replicate 123 0 ++ [24])
    "decoded padded abc block mismatch"
  let abcDigest := sha512FeedForwardOutput (combinedCell abcRows 79)
  combinedEnsure (abcDigest == compress H0 abcBlock) "actual abc compression mismatch"
  combinedEnsure (abcDigest == [15974045371385084602,14718171817514647857,1362051152550133410,
    765311659573367706,2419164356178592168,3943530547489205181,4993722480620005390,3069987439919277215])
    "independent hashlib abc digest mismatch"
  IO.println "PASS:two 128-row feed-forward traces;24 coherent operand forgeries rejected;constrained outputs match hashlib empty and abc digests."
