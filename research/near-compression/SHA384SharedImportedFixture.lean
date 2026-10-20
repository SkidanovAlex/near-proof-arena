import NearCompression.SHA384SharedCore

open NearCompression ZkFormal.Algebra Lean

def readFixed (path : String) : IO (List (Nat × Nat)) := do
  let parsed ← match Json.parse (← IO.FS.readFile path) with
    | .ok value => pure value
    | .error e => throw (IO.userError e)
  let fixed ← match fromJson? parsed with
    | .ok value => pure value
    | .error e => throw (IO.userError e)
  if !(fixed.all (fun p => p.1<267 && p.2<256)) then throw (IO.userError "framing bounds")
  return fixed

def main (args : List String) : IO Unit := do
  let m0 := (← IO.FS.readBinFile args[0]!).data.toList
  let m1 := (← IO.FS.readBinFile args[1]!).data.toList
  if m0.length != 267 || m1.length != 267 then throw (IO.userError "requires two captured267 messages")
  let f0 ← readFixed args[2]!
  let f1 ← readFixed args[3]!
  let pub := (sha384ChainDigest m0 ++ sha384ChainDigest m1).map UInt8.toNat
  let air := sha384SharedAir f0 f1
  IO.FS.writeFile args[4]! ("{\"air\":" ++ air.exportJson ++ ",\"public\":" ++
    (toJson pub).compress ++ ",\"log_rows\":[9,3,3,3,1,1]}")
  IO.println "shared compression: two actual267 inputs, five unique nodes, six tables; diagnostic component"
