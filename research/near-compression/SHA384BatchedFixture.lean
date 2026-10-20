import NearCompression.SHA384BatchedPublic
import Lean
open NearCompression ZkFormal.Algebra Lean NearSpecV3.SHA512

def main (args : List String) : IO Unit := do
  let input := System.FilePath.mk (args.headD "/tmp/near-sha384-framed-hash/message.bin")
  let output := System.FilePath.mk (args[1]?.getD "/tmp/near-sha384-batched/spec.json")
  let message := (← IO.FS.readBinFile input).data.toList
  let count := sha384PaddedLength message.length/128
  let pub := sha384BatchedPublicNat message (sha384ChainDigest message)
  let air := sha384BatchedAir message.length
  let mut coreLog := 1
  while 2^coreLog<80*count do coreLog := coreLog+1
  let mut endpointLog := 1
  while 2^endpointLog<count do endpointLog := endpointLog+1
  IO.FS.writeFile output ("{\"air\":" ++ air.exportJson ++ ",\"public\":" ++
    (toJson pub).compress ++ ",\"log_rows\":" ++ (toJson [coreLog,endpointLog]).compress ++ "}")
  IO.println s!"exported {count} blocks in {2^coreLog} core rows; {pub.length} public values"
