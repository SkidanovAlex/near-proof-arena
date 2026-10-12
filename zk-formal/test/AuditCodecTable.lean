import ZkFormal.NearV3.Render.CodecNative

/-! Guard the frozen-codec table assembly (lane v3-render-sched). -/

/-- info: 'ZkFormal.NearV3.Render.Cdc.local_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.local_at

/-- info: 'ZkFormal.NearV3.Render.Cdc.mult_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.mult_bits

/-- info: 'ZkFormal.NearV3.Render.Cdc.table_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.table_local

/-- info: 'ZkFormal.NearV3.Render.Cdc.allDescs_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.allDescs_local

/-- info: 'ZkFormal.NearV3.Render.Cdc.codec_blocks_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.codec_blocks_complete

/-- info: 'ZkFormal.NearV3.Render.codecRenderV3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.codecRenderV3

/-- info: 'ZkFormal.NearV3.Render.Cdc.blkOf_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.blkOf_ok

/-- info: 'ZkFormal.NearV3.Render.codec_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.codec_accepted
