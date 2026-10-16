import NearCompression.SHA384TranscriptCommit
import Lean
open NearCompression Lean

def main (args : List String) : IO Unit := do
  let j ← match Json.parse (← IO.FS.readFile args[0]!) with
    | .ok x=>pure x | .error e=>throw (IO.userError e)
  let rows : List (List Nat × List Nat × List Nat × List Nat) ← match fromJson? j with
    | .ok x=>pure x | .error e=>throw (IO.userError e)
  let mut result : Array Json := #[]
  for (s,l,p,m) in rows do
    unless [s,l,p,m].all (fun xs=>xs.all (·<256)) do throw (IO.userError "noncanonical byte")
    let seed := s.map UInt8.ofNat
    let label := l.map UInt8.ofNat
    let data := p.map UInt8.ofNat
    let msg := m.map UInt8.ofNat
    let checked := sha384CommitOperandCheck seed label data msg
    result := result.push (Json.mkObj [("operands",toJson checked),
      ("next",toJson (if checked then (sha384TranscriptCommit seed label data).map UInt8.toNat else []))])
  IO.FS.writeFile args[1]! (toJson result).compress
