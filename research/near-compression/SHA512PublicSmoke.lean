import NearCompression.SHA512ScheduleWindow
import NearCompression.SHA512CombinedRun
import NearCompression.SHA512Constants
import NearCompression.SHA512FeedForward
import NearCompression.SHA512BlockDecode
import NearCompression.SHA512Public
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

-- Independent public encoding: four little-endian 16-bit limbs per word.
def publicEncodeWords (words : List Nat) : List Fp :=
  words.flatMap fun w => (List.range 4).map fun limb => Fp.ofNat (w / 65536^limb % 65536)

def publicBitSum (base : Nat) : Expr :=
  ((List.range 16).map fun bit => Expr.mul (.const (2^bit))
    (.col (base+bit) false)).foldr Expr.add (.const 0)

def publicInputConstraints : List Expr :=
  (List.range 96).map fun j =>
    let base := if j < 32 then ffInputBases.getD (j/4) 0
      else ([1440,576,1776,1840,1904,1968,2032,2096,2160,1232,2224,2288,2352,2416,0,2480].getD ((j-32)/4) 0)
    Expr.mul .isFirst (.add (publicBitSum (base+16*(j%4))) (.neg (.pub j)))

def publicOutputConstraints : List Expr :=
  (List.range 32).map fun j =>
    Expr.mul (.col 5231 false) (.add (.col (5288+208*(j/4)+j%4) false) (.neg (.pub (96+j))))

def publicBindings : List Expr := publicInputConstraints ++ publicOutputConstraints

def publicCheckRows (rows : Array (Array Fp)) (pub : List Fp) (indices : List Nat)
    (constraints : List Expr) : Bool :=
  indices.all fun r => constraints.all fun e =>
    decide (e.eval (combinedTrace rows 7) 0 r pub = 0)

def publicFormalBindings : List Expr := sha512PublicStateConstraints ++
  sha512PublicMessageConstraints ++ sha512PublicOutputConstraints

def publicClaim (rows : Array (Array Fp)) (pub : List Fp) : Bool :=
  pub.length == 128 && publicCheckRows rows pub [0,79] publicFormalBindings

def publicMutate (pub : List Fp) (i : Nat) (value : Fp) : List Fp :=
  (pub.toArray.set! i value).toList

def main : IO Unit := do
  combinedEnsure (sha512PublicTable.constraints == ffConstraints ++ publicFormalBindings)
    "formal public table prefix mismatch"
  combinedEnsure (publicBindings.length == publicFormalBindings.length) "binding count mismatch"
  for window in [9223372036854775808 :: List.replicate 15 0,
      [7017280570803617792] ++ List.replicate 14 0 ++ [24]] do
    let base := constRows (combinedRows (ofList H0) window 7 (fun r => K.getD r 0)) constHonestPhase
    let rows := ffRows base H0
    combinedEnsure (combinedCheck rows 7 ffConstraints) "honest underlying trace rejected"
    let result := sha512FeedForwardOutput (combinedCell rows 79)
    let pub := publicEncodeWords (H0 ++ window ++ result)
    combinedEnsure (publicClaim rows pub) "honest public claim rejected"
    combinedEnsure ((List.range 128).all fun r => (publicBindings.zip publicFormalBindings).all fun pair =>
      decide (pair.1.eval (combinedTrace rows 7) 0 r pub = pair.2.eval (combinedTrace rows 7) 0 r pub))
      "independent/formal public constraint evaluation mismatch"
    combinedEnsure (publicCheckRows rows pub (List.range 128) publicFormalBindings)
      "formal public constraints rejected honest trace"
    combinedEnsure (sha512PublicState pub == H0 && sha512PublicOutput pub == result)
      "formal public word decoding mismatch"
    combinedEnsure (sha512PublicBlock pub == sha512DecodedBlock (combinedCell rows 0))
      "formal public block decoding mismatch"
    combinedEnsure (sha512PublicOutput pub == compress (sha512PublicState pub) (sha512PublicBlock pub))
      "public compression specification mismatch"
    combinedEnsure (publicCheckRows rows pub (List.range 128) publicBindings)
      "honest public bindings rejected on inactive rows"
    for i in List.range 128 do
      let changed := publicMutate pub i ((pub.getD i 0)+1)
      combinedEnsure (!(publicClaim rows changed)) "substituted public limb accepted"
    for i in [0,31,32,95,96,127] do
      for value in [65536,2013265920] do
        combinedEnsure (!(publicClaim rows (publicMutate pub i (Fp.ofNat value))))
          "out-of-range public limb accepted"
    let wrongEndpoint := publicEncodeWords (H0 ++ window ++ sha512FeedForwardOutput (combinedCell rows 127))
    combinedEnsure (!(publicClaim rows wrongEndpoint)) "row127 endpoint accepted"
    combinedEnsure (!(publicClaim rows (pub ++ [0]))) "overlong public list accepted"
    combinedEnsure (publicCheckRows rows (pub ++ [0]) [0,79] publicBindings)
      "extra unused input unexpectedly read by AIR"
    combinedEnsure (!(publicClaim rows (pub.take 127))) "short public list accepted"
  IO.println "PASS:two public-bound traces;256 substituted limbs,24 noncanonical limbs,and2 wrong endpoints rejected;explicit public-list length gate checked."
