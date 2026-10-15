import ZkFormal.NearV3.D1.VerifierD1Defs
import ArenaCore.SHA256Fast

/-!
`np-lean-verify-v3d1 <pub.bin> <claim.bin> <proof.bin>` (lane v3-d1-tables)

Runs the D1a verifier model `(npVerifierP challengeSpecD1a nearAirV3D1 split prepD1b).toVerifier`
at `auxGroup = 2`, `.deployed pub cb pb`, as `np-lean-verify-v3` does for D0a: claim guard,
hint split, the native `prepD1` (with `Ed25519.verify` on every transaction), the v2 STARK
verifier over the 30-table `nearAirV3D1`.  Prints `accept` (exit 0) or `reject` (exit 1).
-/

open ArenaCore ZkFormal ZkFormal.NearV3.Assembly

local instance : ZkFormal.Prover.Np.G.AuxG := ⟨2, by decide⟩

def deployedVerifyV3D1 (pub cb pb : Bytes) : Bool :=
  (ZkFormal.Prover.Np.G.npVerifierP NearSpecV3.challengeSpecD1a ZkFormal.NearV3.D1.nearAirV3D1 split
    ZkFormal.NearV3.D1.prepD1b).toVerifier.deployed pub cb pb

def readBytes (p : String) : IO Bytes := return (← IO.FS.readBinFile p).toList

def main (args : List String) : IO UInt32 := do
  match args with
  | [pubP, cbP, pbP] =>
    let pub ← readBytes pubP
    let cb ← readBytes cbP
    let pb ← readBytes pbP
    let t0 ← IO.monoNanosNow
    let ok ← IO.lazyPure fun _ => deployedVerifyV3D1 pub cb pb
    let t1 ← IO.monoNanosNow
    IO.eprintln s!"verify-v3d1: claim {cb.length} B, proof {pb.length} B, wall {(t1 - t0) / 1000000} ms"
    IO.println (if ok then "accept" else "reject")
    return (if ok then 0 else 1)
  | _ =>
    IO.eprintln "usage: np-lean-verify-v3d1 <pub.bin> <claim.bin> <proof.bin>"
    return 2
