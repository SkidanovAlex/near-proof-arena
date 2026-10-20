import NearCompression.SHA384DirectInput
import NearCompression.SHA384BatchedPublic
import Lean
open NearCompression ZkFormal.Algebra Lean

def main (args : List String) : IO Unit := do
  let message := (← IO.FS.readBinFile (System.FilePath.mk args[0]!)).data.toList
  let parsed ← match Json.parse (← IO.FS.readFile (System.FilePath.mk args[1]!)) with
    | .ok value => pure value
    | .error e => throw (IO.userError e)
  let fixed : List (Nat × Nat) ← match fromJson? parsed with
    | .ok value => pure value
    | .error e => throw (IO.userError e)
  if !(fixed.all (fun p => p.1<message.length && p.2<256)) then throw (IO.userError "fixed framing index/byte")
  if message.length < 1 || 1024 < message.length then throw (IO.userError "bounded profile requires 1..1024 bytes")
  let mut previous : Option Nat := none
  for entry in fixed do
    if let some i := previous then
      if !(i < entry.1) then throw (IO.userError "fixed framing indices must strictly increase")
    previous := some entry.1
  let count := sha384PaddedLength message.length/128
  let pub := (sha384ChainDigest message).map UInt8.toNat ++ [1,0,0,0] ++ sha384BatchIVPayload ++ [1,0,0,0]
  let air := sha384DirectInputAir message.length fixed
  let mut coreLog := 1
  while 2^coreLog<80*count do coreLog := coreLog+1
  let mut blockLog := 1
  while 2^blockLog<count do blockLog := blockLog+1
  IO.FS.writeFile (System.FilePath.mk args[2]!) ("{\"air\":" ++ air.exportJson ++ ",\"public\":" ++
    (toJson pub).compress ++ ",\"log_rows\":" ++ (toJson [coreLog,blockLog,1]).compress ++ "}")
  IO.println s!"direct committed-input hash: {message.length} bytes, {count} blocks, 88 public field elements"
