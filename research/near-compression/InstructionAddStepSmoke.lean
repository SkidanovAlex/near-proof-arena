import NearCompression.InstructionAddRange
open NearSpecV3.Wasm NearCompression ZkFormal.Algebra

def ensureStep (b : Bool) (label : String) : IO Unit :=
  unless b do throw (IO.userError label)

def valView : Val → Nat × Nat
  | .i32 v => (0, v.toNat)
  | .i64 v => (1, v.toNat)
  | .ref none => (2, 0)
  | .ref (some n) => (3, n)

def frameView (f : Frame) :=
  (f.fn, f.pc, f.locals.map valView,
    f.labels.map (fun l => (l.target, l.arity, l.height, l.isLoop)), f.base)

def gasView (g : Gas) :=
  (g.burnt, g.promises, g.prepaid, g.limit, g.g, g.host, g.action, g.special, g.sendCompute)

def testFrame : Frame := ⟨0, 0, #[.i32 9], [⟨2, 1, 1, false⟩], 1⟩

def testState (a b prepaid : Nat) : St := {
  stack := #[.i64 77, .i32 (UInt32.ofNat a), .i32 (UInt32.ofNat b)],
  frames := [testFrame], pages := #[⟨#[19, 23]⟩], globals := #[.i64 11],
  table := #[some 0], tableMax := 3, elems := #[], datas := #[⟨#[31]⟩],
  stackRem := 1000, gas := { Gas.init prepaid with g := prepaid },
  balance := 123, storageUsage := 456, registers := #[(8, ⟨#[42]⟩)] }

/-- Synthetic prepared fixture: exercises step semantics, not preparation validity. -/
def testPrepared (gas : Array (Option (IK × Fee))) : Prepared :=
  { (default : Prepared) with funcs := #[{ (default : PFunc) with
    code := #[.num 0x6A, .end_], gas := gas }] }

def sameOtherFields (s t : St) : Bool :=
  s.pages == t.pages && s.globals.map valView == t.globals.map valView &&
  s.table == t.table && s.tableMax == t.tableMax && s.elems == t.elems &&
  s.datas == t.datas && s.stackRem == t.stackRem && s.balance == t.balance &&
  s.storageUsage == t.storageUsage && s.registers == t.registers

def successCase (a b : Nat) (fee : Option Nat) (prepaid : Nat) : IO Unit := do
  let s := testState a b prepaid
  let p := testPrepared #[fee.map (fun n => (IK.pure, Fee.const n))]
  let row := instructionAdd32RangeWitness (UInt32.ofNat a) (UInt32.ofNat b)
  ensureStep (instructionAdd32RangeConstraints.all fun e =>
    decide (e.evalWith (instructionAddEnv row) = 0)) "honest row rejected"
  match step pv86 p s with
  | .cont t =>
    let expected := (a + b) % 4294967296
    ensureStep (instructionAddWord row 4 5 == expected) "AIR output mismatch"
    ensureStep (t.stack.map valView == #[(1,77),(0,expected)]) "stack mismatch"
    ensureStep (t.frames.map frameView == [frameView { testFrame with pc := 1 }]) "PC/frame mismatch"
    ensureStep (gasView t.gas == gasView {s.gas with g := prepaid - fee.getD 0}) "gas mismatch"
    ensureStep (sameOtherFields s t) "unrelated state changed"
  | _ => throw (IO.userError "expected successful step")

def failureCase (fee : Nat) (expectedError : String) : IO Unit := do
  let s := testState 4294967295 1 99
  let p := testPrepared #[some (.pure, Fee.const fee)]
  match step pv86 p s with
  | .abort t e =>
    ensureStep (e == expectedError) "failure error mismatch"
    ensureStep (t.stack.map valView == s.stack.map valView) "failure executed arithmetic"
    ensureStep (t.frames.map frameView == s.frames.map frameView) "failure advanced PC"
    ensureStep (gasView t.gas == gasView {s.gas with burnt := 99}) "failure gas mismatch"
    ensureStep (sameOtherFields s t) "failure changed unrelated state"
  | _ => throw (IO.userError "expected gas failure")

def malformedCase (p : Prepared) (s : St) (expected : String) : IO Unit := do
  match step pv86 p s with
  | .unmodeled e => ensureStep (e == expected) "fetch failure mismatch"
  | _ => throw (IO.userError "expected malformed fetch rejection")

/-- Valid binary module: () -> i32, i32.const -1; i32.const 1; i32.add. -/
def preparedModuleCase : IO Unit := do
  let bytes : ByteArray := ⟨#[0,97,115,109,1,0,0,0,
    1,5,1,96,0,1,127,3,2,1,0,10,9,1,7,0,65,127,65,1,106,11]⟩
  let p ← match prepare pv86 bytes with
    | .ok p => pure p
    | .prepErr v why => throw (IO.userError s!"prepare failed: {v}: {why}")
    | _ => throw (IO.userError "prepare did not accept valid module")
  let s := {testState 0 0 1000000000000000 with stack := #[.i64 77]}
  let mut current := s
  for _ in List.range 3 do
    match step pv86 p current with
    | .cont t => current := t
    | _ => throw (IO.userError "prepared module step failed")
  ensureStep (current.stack.map valView == #[(1,77),(0,0)]) "prepared module result mismatch"
  ensureStep (current.frames.map frameView == [frameView {testFrame with pc := 3}])
    "prepared module PC mismatch"
  ensureStep (current.gas.g == s.gas.g - 2468268 && current.gas.burnt == 0) "prepared gas not charged"
  ensureStep (sameOtherFields s current) "prepared steps changed unrelated state"
  IO.println s!"prepared_module_steps=3 gas_decrement={s.gas.g - current.gas.g}"

def main : IO Unit := do
  let cases := [(0,0),(1,2),(65535,1),(65536,65536),(4294967295,1),
    (4294967295,4294967295),(2147483648,2147483648),(305419896,2596069104)]
  for (a,b) in cases do
    successCase a b none 0
    successCase a b (some 100) 1000
    successCase a b (some 100) 100
  failureCase 100 errGasExceeded
  failureCase (2^64) errIntOverflow
  let s := testState 1 2 1000
  let p := testPrepared #[none]
  malformedCase {p with funcs := #[]} s "bad frame"
  malformedCase p {s with frames := [{testFrame with pc := 2}]} "pc out of range"
  malformedCase (testPrepared #[]) s "invariant: gas table shorter than the code"
  match step pv86 p {s with frames := []} with
  | .fin t => ensureStep (t.stack.map valView == s.stack.map valView) "finish changed stack"
  | _ => throw (IO.userError "empty frames did not finish")
  preparedModuleCase
  IO.println "PASS: 24 successful actual steps, 2 gas failures, 3 malformed fetches, empty-frame finish, valid prepared binary module."
