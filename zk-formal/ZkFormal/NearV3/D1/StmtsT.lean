import ZkFormal.NearV3.D1.PrepD1Lemmas
import ZkFormal.V2.PG.V2Prover

/-!
# `ZkFormal.NearV3.D1.StmtsT` — the D1a soundness / completeness obligations on the verifier's tape

Lane `v3-d1-phase2` (docs/zk-formal/V3-D1-PHASE2.md §4).  Statements only (`Prop` definitions).

`PrepD1Lemmas.ExtractD1Stmt` / `CompleteD1Stmt` (phase 1) state the obligations on the public
tape `preparedBytesD1 p 0`.  The verifier (`VerifierD1Defs.prepD1b` = `preparedTapeD1`) uses
`preparedBytesD1 p (txOverhead h)`: the witness bytes the AIR does not see (the hint's two
transaction vectors) enter `sizeV3`'s `w.size` check through `PH_WOVH`.  With overhead `0` an
accepted trace bounds only the AIR-visible bytes, while the extracted witness also carries the
transactions, so the overhead-`0` soundness statement is not the one the admission needs (and
is presumably false).  The siblings below are stated on the verifier's tape; the completeness
side also carries `headerOk` (as D0a's `RenderV3Stmt`), which the admission theorem consumes.
The phase-1 statements are kept unchanged.
-/

namespace ZkFormal.NearV3.D1

open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra

/-- The deployed auxiliary-group parameter `g = 2` (as `NearAdmission`). -/
local instance auxG2_d1Stmts : ZkFormal.Prover.Np.G.AuxG := ⟨2, by decide⟩

/-- **Soundness obligation** (at the challenge's A7 bound `B0`), on the verifier's tape. -/
def ExtractD1StmtT : Prop :=
  ∀ (cb : Bytes) (h : HintD1) (p : Public.PrepD1) (tr : Trace Fp),
    prepD1 cb h = .ok p →
    (Public.preparedBytesD1 p (txOverhead h)).length < ZkFormal.Algebra.P →
    HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p (txOverhead h))) tr →
    ∃ w, RelD1a B0 cb w

/-- **Completeness obligation**, on the verifier's tape, with an admissible header. -/
def CompleteD1StmtT : Prop :=
  ∀ (cb w : Bytes), checkD1a B0 cb w = .ok () →
    ∃ (h : HintD1) (p : Public.PrepD1) (tr : Trace Fp),
      prepD1 cb h = .ok p ∧
      HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p (txOverhead h))) tr ∧
      h.encode.length < 256 ^ 4 ∧
      (ZkFormal.Prover.Np.G.VdP nearAirV3D1).headerOk
        (ZkFormal.Prover.trHdr nearAirV3D1.toAir tr) = true

end ZkFormal.NearV3.D1
