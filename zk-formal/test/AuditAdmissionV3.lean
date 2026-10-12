import ZkFormal.NearV3.Assembly.AdmissionV3

/-! Guard the top-level D0a certificate (integration v3-20261012d): `nearV3_admission_final` — the
admission statement from the implementation connection `himpl` only; soundness (`extractV3`) and
completeness (`completeV3`, via `chachaSideV3`) are proved.  Also the intermediate forms from
`ChachaSideV3`. -/

open ZkFormal.NearV3.Assembly NearSpec NearSpecV3 in
/-- info: ZkFormal.NearV3.Assembly.nearV3_admission_final (art : ArenaCore.ArtifactDescription) (pub : List UInt8)
  (hpub : sha256 pub = art.publicDigest)
  (himpl :
    art.impl.Connection challengeParamsD0a.verifyFuel
      (ZkFormal.Prover.Np.G.npVerifierP challengeSpecD0a nearAirV3 split prepV3b).toVerifier) :
  ArenaCore.AdmissionStatement challengeParamsD0a art -/
#guard_msgs(whitespace := lax) in
#check nearV3_admission_final

/-- info: 'ZkFormal.NearV3.Assembly.nearV3_admission_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.nearV3_admission_final

/-- info: 'ZkFormal.NearV3.Assembly.completeV3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.completeV3

/-- info: 'ZkFormal.NearV3.Assembly.chachaSideV3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.chachaSideV3

/-- info: ZkFormal.NearV3.Assembly.completeV3 : ZkFormal.NearV3.Assembly.CompleteV3Stmt -/
#guard_msgs(whitespace := lax) in
#check ZkFormal.NearV3.Assembly.completeV3

/-- info: ZkFormal.NearV3.Assembly.extractV3 : ZkFormal.NearV3.Assembly.ExtractV3Stmt -/
#guard_msgs(whitespace := lax) in
#check ZkFormal.NearV3.Assembly.extractV3

open ZkFormal.NearV3.Assembly NearSpec NearSpecV3 in
/-- info: nearV3_admission_of_chacha' : ChachaSideV3 →
  ∀ (art : ArenaCore.ArtifactDescription) (pub : List UInt8),
    sha256 pub = art.publicDigest →
      art.impl.Connection challengeParamsD0a.verifyFuel
          (ZkFormal.Prover.Np.G.npVerifierP challengeSpecD0a nearAirV3 split prepV3b).toVerifier →
        ArenaCore.AdmissionStatement challengeParamsD0a art -/
#guard_msgs(whitespace := lax) in
#check @nearV3_admission_of_chacha'

/-- info: 'ZkFormal.NearV3.Assembly.nearV3_admission_of_chacha'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.nearV3_admission_of_chacha'

/-- info: 'ZkFormal.NearV3.Assembly.nearV3_admission_of_chacha''' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.nearV3_admission_of_chacha''

/-- info: 'ZkFormal.NearV3.Assembly.extractV3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.extractV3

/-- info: 'ZkFormal.NearV3.Assembly.completeV3_of_chacha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.completeV3_of_chacha

/-- info: 'ZkFormal.NearV3.Assembly.nearV3_sizeMaxAligned' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.nearV3_sizeMaxAligned
