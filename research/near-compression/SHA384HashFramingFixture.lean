import NearCompression.SHA384HashFraming
import Lean
open NearCompression Lean

def main (args : List String) : IO Unit := do
  let j ← match Json.parse (← IO.FS.readFile args[0]!) with
    | .ok x=>pure x | .error e=>throw (IO.userError e)
  let rows : List (List Nat × List (List Nat)) ← match fromJson? j with
    | .ok x=>pure x | .error e=>throw (IO.userError e)
  let mut out := ByteArray.empty
  let mut lengths : Array Nat := #[]
  for (tag,parts) in rows do
    unless tag.all (·<256) && parts.all (fun p=>p.all (·<256)) do
      throw (IO.userError "noncanonical byte")
    unless tag.length<2^32 && parts.length<2^32 && parts.all (fun p=>p.length<2^64) do
      throw (IO.userError "framing length overflow")
    let bytes := sha384HashFrame (tag.map UInt8.ofNat) (parts.map (List.map UInt8.ofNat))
    lengths := lengths.push bytes.length
    out := out ++ ⟨bytes.toArray⟩
  IO.FS.writeBinFile args[1]! out
  IO.FS.writeFile args[2]! (toJson lengths).compress
