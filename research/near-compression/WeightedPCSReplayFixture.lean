import NearCompression.WeightedPCSReplay
import NearCompression.DiagnosticExt4Embedding
import Lean
open NearCompression ZkFormal.Algebra Lean

def replayField (xs : List Nat) : Fp4 := diagnosticExt4ToTower
  ⟨Fp.ofNat (xs.getD 0 0),Fp.ofNat (xs.getD 1 0),Fp.ofNat (xs.getD 2 0),Fp.ofNat (xs.getD 3 0)⟩
def replayWords (x : Fp4) : List Nat :=
  let a:=diagnosticExt4FromTower x
  [a.c0.toNat,a.c1.toNat,a.c2.toNat,a.c3.toNat]

def main (args : List String) : IO Unit := do
  let j ← match Json.parse (← IO.FS.readFile args[0]!) with | .ok x=>pure x | .error e=>throw (IO.userError e)
  let cases ← match j.getArr? with | .ok x=>pure x | .error e=>throw (IO.userError e)
  let mut out : Array Json:=#[]
  for c in cases do
    let get (α : Type) [FromJson α] (key : String) : IO α :=
      match c.getObjValAs? α key with | .ok x=>pure x | .error e=>throw (IO.userError e)
    let point ← get (List (List Nat)) "point"
    let challenges ← get (List (List Nat)) "challenges"
    let sent ← get (List (List (List Nat))) "sent"
    let initial ← get (List Nat) "initial"
    let terminal ← get (List Nat) "terminal"
    unless point.length≤8 && challenges.length≤8 && sent.length≤8 && sent.all (fun q=>q.length==3) &&
      (point++challenges++sent.flatten++[initial,terminal]).all (fun xs=>xs.length==4 && xs.all (·<2013265921)) do
      throw (IO.userError "canonical bounded replay")
    let u:=point.map replayField
    let rs:=challenges.map replayField
    let qs:=sent.map (fun q : List (List Nat)=>
      (⟨replayField (q.getD 0 []),replayField (q.getD 1 []),replayField (q.getD 2 [])⟩ : WhirQuadratic Fp4))
    let start:=replayField initial
    let last:=replayField terminal
    out:=out.push (Json.mkObj [
      ("checked",toJson (weightedReplayCheck u rs qs start last)),
      ("scales",toJson ((List.range (u.length+1)).map (fun i=>replayWords (weightedReplayScaleLoop u rs i)))),
      ("weights",toJson ((List.range (u.length+1)).map (fun i=>(weightedReplayWeights u rs i).map replayWords))),
      ("claims",toJson ((List.range (u.length+1)).map (fun i=>replayWords (weightedReplayClaim start qs rs i))))])
  IO.FS.writeFile args[1]! (toJson out).compress
