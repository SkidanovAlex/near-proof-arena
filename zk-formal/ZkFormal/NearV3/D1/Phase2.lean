import ZkFormal.NearV3.D1.Extract.AirD1
import ZkFormal.NearV3.D1.Extract.KibProof
import ZkFormal.NearV3.D1.Extract.PlfProof
import ZkFormal.NearV3.D1.Extract.RidProof
import ZkFormal.NearV3.D1.Prep.TxVerdict
import ZkFormal.NearV3.D1.Prep.LocalNative
import ZkFormal.NearV3.D1.Prep.TxNative
import ZkFormal.NearV3.D1.StmtsT
import ZkFormal.NearV3.D1.Extract.TxProof
import ZkFormal.NearV3.D1.Extract.ViewsD1
import ZkFormal.NearV3.D1.ModelTier
import ZkFormal.NearV3.D1.Extract.Akm.Field
import ZkFormal.NearV3.D1.Extract.AkmProof
import ZkFormal.NearV3.D1.R.View
import ZkFormal.NearV3.D1.M.View
import ZkFormal.NearV3.D1.Public.Split

/-!
# `ZkFormal.NearV3.D1.Phase2` — the D1a phase-2 proof modules (build root)

Lane `v3-d1-phase2`; plan and status: docs/zk-formal/V3-D1-PHASE2.md.  `lake build
ZkFormal.NearV3.D1.Phase2` builds every finished phase-2 module (no `sorry`).  Not imported by
the D0a certificate or by the verifier model.
-/
