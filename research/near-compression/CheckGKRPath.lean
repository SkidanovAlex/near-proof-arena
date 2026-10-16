import NearCompression.GKRPathMessageCheck
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

private def tapeSent (rows : List (Poly Fp4)) (history : List Fp4) : Poly Fp4 :=
  rows.getD history.length ⟨[]⟩
private def tapeClaim (initial : Fp4) (rows : List (Poly Fp4)) (history : List Fp4) : Fp4 :=
  match history.getLast? with
  | none=>initial
  | some r=>(rows.getD (history.length-1) ⟨[]⟩).eval r

private abbrev Record := (m : Nat) × (GKRLayerStrategy Fp4 m × GKRBlock Fp4)
private def parseRecord (testcase : Json) : IO Record := do
  let m ← need (←field testcase "m").getNat?
  let initial ← scalar (←field testcase "initial")
  let rows ← (←need (←field testcase "rounds").getArr?).toList.mapM fun j=>do
    let coeffs ← (←need j.getArr?).toList.mapM scalar
    pure (⟨coeffs⟩ : Poly Fp4)
  let point ← (←need (←field testcase "point").getArr?).toList.mapM scalar
  let a ← scalar (←field testcase "a")
  let b ← scalar (←field testcase "b")
  let gamma ← scalar (←field testcase "gamma")
  let gates ← (←need (←field testcase "gates").getArr?).toList.mapM fun j=>do
    let fields ← need j.getArr?
    require (fields.size==4) "weighted gate arity"
    let g ← gate (Json.arr (fields.extract 0 3))
    let w ← scalar fields[3]!
    pure (g,w)
  require (rows.length==2*m) "round count"
  if bound : gates.all (fun e=>decide (e.1.left<2^m ∧ e.1.right<2^m))=true then
    let left:=rows.take m
    let right:=rows.drop m
    let strategy : GKRLayerStrategy Fp4 m := {
      values:=fun _=>0
      gates:=gates
      leftBounds:=by
        intro e he
        have h:=List.all_eq_true.mp bound e he
        exact (_root_.of_decide_eq_true h).1
      rightBounds:=by
        intro e he
        have h:=List.all_eq_true.mp bound e he
        exact (_root_.of_decide_eq_true h).2
      sentLeft:=tapeSent left
      claimLeft:=tapeClaim initial left
      sentRight:=fun _=>tapeSent right
      claimRight:=fun u=>tapeClaim (tapeClaim initial left u) right
      a:=fun _ _=>a
      b:=fun _ _=>b }
    return ⟨m,(strategy,(point.take m,point.drop m,gamma))⟩
  else throw (IO.userError "gate input bounds")

private def emptyStrategy (m : Nat) : GKRLayerStrategy Fp4 m where
  values:=fun _=>0
  gates:=[]
  leftBounds:=by simp
  rightBounds:=by simp
  sentLeft:=fun _=>⟨[]⟩
  claimLeft:=fun _=>0
  sentRight:=fun _ _=>⟨[]⟩
  claimRight:=fun _ _=>0
  a:=fun _ _=>0
  b:=fun _ _=>0

private def replayStrategy (records : List Record) (m : Nat) (history : List (GKRBlock Fp4)) : GKRLayerStrategy Fp4 m :=
  match records[history.length]? with
  | none=>emptyStrategy m
  | some record=>if h:record.1=m then h ▸ record.2.1 else emptyStrategy m

def main (args : List String) : IO Unit := do
  let cases ← need (←need (Json.parse (←IO.FS.readFile args[0]!))).getArr?
  let mut accepted:=0
  let mut rejected:=0
  for testcase in cases do
    let records ← (←need (←field testcase "records").getArr?).toList.mapM parseRecord
    let layers ← (←need (←field testcase "layers").getArr?).toList.mapM fun j=>do
      (←need j.getArr?).toList.mapM gate
    let expected ← need (←field testcase "expected").getBool?
    let result:=gkrPathMessageCheck (replayStrategy records) layers []
      (records.map (fun r=>r.1)) (records.map (fun r=>r.2.2))
    require (result==expected) "path checker result mismatch"
    if result then accepted:=accepted+1 else rejected:=rejected+1
  IO.println s!"PASS GKR paths: {accepted} accepted, {rejected} rejected"
