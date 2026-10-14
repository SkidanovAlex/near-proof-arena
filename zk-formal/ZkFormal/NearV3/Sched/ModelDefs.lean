import NearSpecV3.BandwidthScheduler

/-!
# `ZkFormal.NearV3.Sched.ModelDefs`

The definitions of `ZkFormal.NearV3.Sched.Model` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Sched.Model` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler NearSpec

/-- A request with resolved shard indices `(s, r)` and its 5-byte bitmap. -/
structure RawReq where
  s : Nat
  r : Nat
  bm : List UInt8
  deriving DecidableEq, Repr

/-- Positions `< 40` of the set bits, ascending. -/
def setBits (bm : List UInt8) : List Nat := (List.range 40).filter (getBit bm)

/-- Increases from the value table over the set bits (`prev` = value of the last set bit). -/
def incsFrom (vals : List Nat) : Nat → List Nat → List Nat
  | _, [] => []
  | prev, c :: cs => (vals.getD c 0 - prev) :: incsFrom vals (vals.getD c 0) cs

def incsOf (p : Params) (bm : List UInt8) : List Nat := incsFrom (requestValues p) p.base (setBits bm)

end ZkFormal.NearV3.Sched
