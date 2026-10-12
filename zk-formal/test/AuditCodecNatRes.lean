import ZkFormal.NearV3.Render.CodecNatRes
import ZkFormal.NearV3.Render.CodecSanity
import ZkFormal.NearV3.Render.CodecAllow

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

/-- info: 'ZkFormal.NearV3.Render.Cdc.codec_bytes_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.codec_bytes_native

/-- info: 'ZkFormal.NearV3.Render.Cdc.codec_digest_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.codec_digest_native

/-- info: 'ZkFormal.NearV3.Render.Cdc.codec_s0f_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.codec_s0f_native

/-- info: 'ZkFormal.NearV3.Render.Cdc.codec_splen_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.codec_splen_native

/-- info: 'ZkFormal.NearV3.Render.Cdc.codec_sha_counts_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.codec_sha_counts_pinned

/-- info: 'ZkFormal.NearV3.Render.CdcAllow.allowances_canon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.CdcAllow.allowances_canon

/-- info: 'ZkFormal.NearV3.Render.CdcAllow.a0s_canon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.CdcAllow.a0s_canon
