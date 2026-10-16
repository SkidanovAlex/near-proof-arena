import NearCompression.SHA512Chain

open NearSpecV3.SHA512

namespace NearCompression

def sha384ChainIV : List Nat := [0xcbbb9d5dc1059ed8,0x629a292a367cd507,
  0x9159015a3070dd17,0x152fecd8f70e5939,0x67332667ffc00b31,
  0x8eb44a8768581511,0xdb0c2e0d64f98fa7,0x47b5481dbefa4fa4]

def sha384ChainDigest (message : ArenaCore.Bytes) : ArenaCore.Bytes :=
  let input := pad (message.map UInt8.toNat)
  (digestBytes (blocks (input.length/128) sha384ChainIV input)).take 48

/-- Compression facts come from actual per-block AIR claims through the
existing chain theorem; neither compression equalities nor a hash oracle are
new hypotheses. SHA384 changes the IV and final truncation only. -/
theorem sha384_chain_boundary_sound (message : ArenaCore.Bytes) (final : List Nat)
    (items : List SHA512ChainItem) (claims : sha512ChainClaims items)
    (check : sha512ChainBoundaryCheck sha384ChainIV (pad (message.map UInt8.toNat)) final items=true) :
    (digestBytes final).take 48=sha384ChainDigest message := by
  have chain := (sha512_chain_check_iff sha384ChainIV (pad (message.map UInt8.toNat)) final items).mpr ⟨claims,check⟩
  have result := (sha512_chain_sound _ _ _ _ chain).1
  have count := (sha512_chain_consumed _ _ _ _ chain).1
  dsimp only [sha384ChainDigest]
  rw [count,←result]

end NearCompression
