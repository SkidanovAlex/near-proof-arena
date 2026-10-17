import NearCompression.GKRMessageCheck
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

def main (args : List String) : IO Unit := do
  let cases ← need (←need (Json.parse (←IO.FS.readFile args[0]!))).getArr?
  let mut accepted:=0
  let mut rejected:=0
  for testcase in cases do
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
    let expected ← need (←field testcase "expected").getBool?
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
      let result:=gkrLayerMessageCheck strategy (point.take m,point.drop m,gamma)
      require (result==expected) "message checker result mismatch"
      if result then accepted:=accepted+1 else rejected:=rejected+1
    else throw (IO.userError "gate input bounds")
  IO.println s!"PASS GKR message checks: {accepted} accepted, {rejected} rejected"
