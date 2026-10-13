import ZkFormal.NearV3.Assembly.NearAdmission
import NearSpecV3.ChallengeD0a
import ArenaCore.SHA256Fast

/-!
`np-lean-verify-v3 <pub.bin> <claim.bin> <proof.bin>`

Runs **the deployed verifier model of `np-udr-stark-v2` for D0a**
(`NpUdrStarkV2.Model.verifier`, `formal/NpUdrStarkV2/Model.lean`):

  `(ZkFormal.Prover.Np.G.npVerifierP challengeSpecD0a nearAirV3 split prepV3b).toVerifier`

at `auxGroup = 2` (the `AuxG` instance of `NearAdmission.lean`), exactly as deployed:
`.deployed pub cb pb` (the hash-query tree run against `Interp.deployedRO`).  The AIR is the
Lean constant `ZkFormal.NearV3.Assembly.nearAirV3` (not a JSON re-import); the claim guard
(`claimOk`), the hint split (`readBorshBytes`), the native preprocessing `prepV3b` and the v2
STARK verifier all run in Lean.  Prints `accept` (exit 0) or `reject` (exit 1); usage errors
exit 2.  Timing goes to stderr.
-/

open ArenaCore ZkFormal ZkFormal.NearV3.Assembly

local instance : ZkFormal.Prover.Np.G.AuxG := ⟨2, by decide⟩

def deployedVerifyV3 (pub cb pb : Bytes) : Bool :=
  (ZkFormal.Prover.Np.G.npVerifierP NearSpecV3.challengeSpecD0a nearAirV3 split prepV3b).toVerifier.deployed
    pub cb pb

def readBytes (p : String) : IO Bytes := return (← IO.FS.readBinFile p).toList

def main (args : List String) : IO UInt32 := do
  match args with
  | [pubP, cbP, pbP] =>
    let pub ← readBytes pubP
    let cb ← readBytes cbP
    let pb ← readBytes pbP
    let t0 ← IO.monoNanosNow
    let ok ← IO.lazyPure fun _ => deployedVerifyV3 pub cb pb
    let t1 ← IO.monoNanosNow
    IO.eprintln s!"verify-v3: claim {cb.length} B, proof {pb.length} B, wall {(t1 - t0) / 1000000} ms"
    IO.println (if ok then "accept" else "reject")
    return (if ok then 0 else 1)
  | _ =>
    IO.eprintln "usage: np-lean-verify-v3 <pub.bin> <claim.bin> <proof.bin>"
    return 2
