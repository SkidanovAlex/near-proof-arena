import ZkFormal.NearV3.Render.CodecNatRes

/-! Guard NatRes from acceptance and the premise-free table 11 (lane v3-render-sched). -/

/-- info: 'ZkFormal.NearV3.Render.CdcGrant.accepted_prior_core_grants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.CdcGrant.accepted_prior_core_grants

/-- info: 'ZkFormal.NearV3.Render.CdcGrant.natRes_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.CdcGrant.natRes_block

/-- info: 'ZkFormal.NearV3.Render.CdcGrant.codec_accepted_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.CdcGrant.codec_accepted_full
