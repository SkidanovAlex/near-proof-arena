import ZkFormal.NearV3.Render.PaddedChacha
import ZkFormal.Chacha.Statements

/-! Guard the assumptions of the aligned ChaCha-lane generators (`nearAirV3` tables 8–10). -/

/-- info: 'ZkFormal.NearV3.Render.chacha_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.chacha_aligned_complete

/-- info: 'ZkFormal.NearV3.Render.chacha_aligned_complete22' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.chacha_aligned_complete22

/-- info: 'ZkFormal.NearV3.Render.rng_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.rng_aligned_complete

/-- info: 'ZkFormal.NearV3.Render.rng_aligned_complete22' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.rng_aligned_complete22

/-- info: 'ZkFormal.NearV3.Render.shuf_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.shuf_aligned_complete

/-- info: 'ZkFormal.NearV3.Render.tableLocal_congr_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.tableLocal_congr_rows

/-- info: 'ZkFormal.NearV3.Render.tableTraffic_congr_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.tableTraffic_congr_rows

/-- info: 'ZkFormal.Chacha.Complete.chacha_completeL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.Chacha.Complete.chacha_completeL

/-- info: 'ZkFormal.Chacha.Rng.Complete.gen_completeL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.Chacha.Rng.Complete.gen_completeL

/-- info: 'ZkFormal.Chacha.Shuffle.Complete.shuffle_completeL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.Chacha.Shuffle.Complete.shuffle_completeL

/-- info: 'ZkFormal.Chacha.Shuffle.Complete.shuffle_trafficL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.Chacha.Shuffle.Complete.shuffle_trafficL


/-- info: 'ZkFormal.NearV3.Render.chacha_v3_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.chacha_v3_aligned_complete

/-- info: 'ZkFormal.NearV3.Render.rng_v3_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.rng_v3_aligned_complete

/-- info: 'ZkFormal.NearV3.Render.shuf_aligned_complete22' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.shuf_aligned_complete22

/-- info: 'ZkFormal.Chacha.shuffle_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.Chacha.shuffle_sound

/-- info: 'ZkFormal.Chacha.shuffleContractStmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.Chacha.shuffleContractStmt
