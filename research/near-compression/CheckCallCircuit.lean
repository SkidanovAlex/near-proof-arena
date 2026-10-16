import NearCompression.CallCircuitCheck
import NearCompression.DiagnosticExt4Embedding
import Lean
open Lean NearCompression ZkFormal.Algebra
private def need (x : Except String α) : IO α :=
  match x with | .ok a => pure a | .error e => throw (IO.userError e)
private def require (b : Bool) (msg : String) : IO Unit :=
  if b then pure () else throw (IO.userError msg)
private def field (j : Json) (k : String) : IO Json := need (j.getObjVal? k)
private def op (s : String) : IO GKRBinaryOp :=
  match s with
  | "add" => pure .add
  | "sub" => pure .sub
  | "mul" => pure .mul
  | _ => throw (IO.userError "unknown operation")
private def gate (j : Json) : IO GKRWiringGate := do
  let a ← need j.getArr?
  require (a.size==3) "gate arity"
  return ⟨←op (←need a[0]!.getStr?),←need a[1]!.getNat?,←need a[2]!.getNat?⟩
private def scalar (j : Json) : IO Fp4 := do
  let a ← need j.getArr?
  require (a.size==4) "constant width"
  let xs ← a.toList.mapM (fun x => need x.getNat?)
  require (xs.all (· < 2013265921)) "noncanonical constant"
  return ⟨⟨Fp.ofNat xs[0]!,Fp.ofNat xs[2]!⟩,⟨Fp.ofNat xs[1]!,Fp.ofNat xs[3]!⟩⟩
private def node (j : Json) : IO (TerminalDAGNode Fp4) := do
  let a ← need j.getArr?
  require (0<a.size) "empty node"
  let tag ← need a[0]!.getStr?
  if tag=="input" then
    require (a.size==2) "input arity"
    return .input (←need a[1]!.getNat?)
  else if tag=="const" then
    require (a.size==5) "constant arity"
    return .constant (←scalar (Json.arr (a.extract 1 5)))
  else
    require (a.size==3) "binary arity"
    return .binary (←op tag) (←need a[1]!.getNat?) (←need a[2]!.getNat?)

private def terms (j : Json) : IO (List (Nat × Bool)) := do
  (←need j.getArr?).toList.mapM fun t => do
    let a ← need t.getArr?
    require (a.size==2) "term arity"
    return (←need a[0]!.getNat?,←need a[1]!.getBool?)

private def passCert (nodes : List (TerminalDAGNode Fp4)) :
    List (Nat × Bool) → List (Nat × Bool) → IO (TerminalPassCertificate Fp4)
  | [],[] => pure .empty
  | [a],[c] => do
      require (a==c) "changed odd carry"
      return .singleton a
  | a::b::rest,c::out => do
      return .pair a b c .direct (←passCert nodes rest out)
  | _,_ => throw (IO.userError "pass shape")

private def balanceStages (nodes : List (TerminalDAGNode Fp4)) (result : Nat) :
    List (List (Nat × Bool)) → IO (TerminalBalanceCertificate Fp4)
  | [[]] => pure (.empty result)
  | [[(x,true)]] => do
      require (x==result) "positive result"
      return .positive x
  | [[(x,false)]] => do
      let zeroNode := nodes.findIdx (fun n => n==.constant 0)
      return .negative x zeroNode result .direct
  | old::next::rest => do
      return .pass (←passCert nodes old next) (←balanceStages nodes result (next::rest))
  | _ => throw (IO.userError "unfinished balance")

private def balance (nodes : List (TerminalDAGNode Fp4)) (j : Json) : IO (TerminalBalanceCertificate Fp4) := do
  let stages ← (←need (←field j "stages").getArr?).toList.mapM terms
  balanceStages nodes (←need (←field j "result").getNat?) stages


def main (args : List String) : IO Unit := do
  let cases ← need (←need (Json.parse (←IO.FS.readFile args[0]!))).getArr?
  let mut accepted := 0
  let mut rejected := 0
  for testcase in cases do
    let nodes ← (←need (←field testcase "nodes").getArr?).toList.mapM node
    let coefficients ← (←need (←field testcase "coefficients").getArr?).toList.mapM scalar
    let claim ← scalar (←field testcase "claim")
    let capacity ← need (←field testcase "capacity").getNat?
    require (coefficients.length==capacity) "coefficient count"
    let constants ← (←need (←field testcase "constants").getArr?).toList.mapM (fun j=>need j.getNat?)
    let products ← (←need (←field testcase "products").getArr?).toList.mapM (fun j=>need j.getNat?)
    let cert : CallCircuitCertificate Fp4 := ⟨constants,products,
      ←balance nodes (←field testcase "balance"),←need (←field testcase "claim_node").getNat?⟩
    let root ← need (←field testcase "root").getNat?
    let expected ← need (←field testcase "expected").getBool?
    let result:=callCircuitCheck nodes capacity (fun i=>coefficients.getD i 0) claim root cert
    require (result==expected) "call circuit certificate acceptance mismatch"
    if result then accepted:=accepted+1 else rejected:=rejected+1
  IO.println s!"PASS call circuit certificates: {accepted} accepted, {rejected} rejected"
