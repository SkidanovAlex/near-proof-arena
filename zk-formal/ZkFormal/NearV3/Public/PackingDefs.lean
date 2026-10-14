import NearSpec.Bytes

/-!
# `ZkFormal.NearV3.Public.PackingDefs`

The definitions of `ZkFormal.NearV3.Public.Packing` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Public.Packing` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.Public

abbrev ByteString := List UInt8
abbrev Payload := List ByteString

def payloadBytes (rs : Payload) : ByteString := rs.flatten

def dataBytes (blocks : List Payload) : ByteString := blocks.flatMap payloadBytes

/-- Eight bytes per segment: u32 row count and u32 absolute payload offset. -/
def metadata : Nat → List Payload → ByteString
  | _, [] => []
  | start, rs :: rest => NearSpec.u32 rs.length ++ NearSpec.u32 start ++
      metadata (start + (payloadBytes rs).length) rest

def encode (header : ByteString) (blocks : List Payload) : ByteString :=
  header ++ metadata (header.length + 8 * blocks.length) blocks ++ dataBytes blocks

end ZkFormal.NearV3.Public
