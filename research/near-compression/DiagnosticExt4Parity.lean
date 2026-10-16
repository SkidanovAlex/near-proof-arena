import NearCompression.DiagnosticExt4Embedding
import Lean
open NearCompression ZkFormal.Algebra Lean

def flatOfWords (v : List Nat) : DiagnosticExt4 :=
  ⟨Fp.ofNat (v.getD 0 0),Fp.ofNat (v.getD 1 0),Fp.ofNat (v.getD 2 0),Fp.ofNat (v.getD 3 0)⟩
def flatWords (v : DiagnosticExt4) : List Nat := [v.c0.toNat,v.c1.toNat,v.c2.toNat,v.c3.toNat]
def main (args : List String) : IO Unit := do
  let input ← IO.FS.readFile args[0]!
  let parsed ← match Json.parse input with
    | .ok v => pure v
    | .error e => throw (IO.userError e)
  let cases : List (List (List Nat)) ← match fromJson? parsed with
    | .ok v => pure v
    | .error e => throw (IO.userError e)
  let rows := cases.map fun pair =>
    let a := flatOfWords (pair.getD 0 [])
    let b := flatOfWords (pair.getD 1 [])
    [flatWords (diagnosticExt4Add a b),flatWords (diagnosticExt4Sub a b),
     flatWords (diagnosticExt4Mul a b),
     flatWords (diagnosticExt4FromTower (diagnosticExt4ToTower a*diagnosticExt4ToTower b))]
  IO.FS.writeFile args[1]! ((toJson rows).compress)
