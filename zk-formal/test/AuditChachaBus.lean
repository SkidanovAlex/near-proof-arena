import ZkFormal.NearV3.Render.ChachaBusBalance

/-! Guard the ChaCha-lane bus balances and the A9 word bound (lane v3-render-chacha). -/

/-- info: 'ZkFormal.NearV3.Render.ChachaBus.replay_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.ChachaBus.replay_inst

/-- info: 'ZkFormal.NearV3.Render.ChachaBus.run_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.ChachaBus.run_rounds

/-- info: 'ZkFormal.NearV3.Render.ChachaBus.table_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.ChachaBus.table_count

/-- info: 'ZkFormal.NearV3.Render.ChachaBus.keyN_leWords' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.ChachaBus.keyN_leWords

/-- info: 'ZkFormal.NearV3.Render.ChachaBus.gen_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.ChachaBus.gen_perm

/-- info: 'ZkFormal.NearV3.Render.ChachaBus.words_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.ChachaBus.words_lane

/-- info: 'ZkFormal.NearV3.Render.ChachaBus.chacha_lane_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.ChachaBus.chacha_lane_perm

/-- info: 'ZkFormal.NearV3.Render.ChachaBus.block_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.ChachaBus.block_words

/-- info: 'ZkFormal.NearV3.Render.ChachaBus.schedIns_native' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.ChachaBus.schedIns_native

/-- info: 'ZkFormal.NearV3.Render.ChachaBus.kfin_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.ChachaBus.kfin_sum

/-- info: 'ZkFormal.NearV3.Render.ChachaBus.kfin_W0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.ChachaBus.kfin_W0

/-- info: 'ZkFormal.NearV3.Render.ChachaBus.runOk_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.ChachaBus.runOk_all

/-- info: 'ZkFormal.NearV3.Assembly.RenderBundleV3.balancedAt_ssin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RenderBundleV3.balancedAt_ssin

/-- info: 'ZkFormal.NearV3.Assembly.RenderBundleV3.balancedAt_ssout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RenderBundleV3.balancedAt_ssout

/-- info: 'ZkFormal.NearV3.Assembly.RenderBundleV3.balancedAt_ssmem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RenderBundleV3.balancedAt_ssmem

/-- info: 'ZkFormal.NearV3.Assembly.RenderBundleV3.balancedAt_sgen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RenderBundleV3.balancedAt_sgen

/-- info: 'ZkFormal.NearV3.Assembly.RenderBundleV3.balancedAt_sshuf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RenderBundleV3.balancedAt_sshuf

/-- info: 'ZkFormal.NearV3.Assembly.RenderBundleV3.balancedAt_schacha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RenderBundleV3.balancedAt_schacha

/-- info: 'ZkFormal.NearV3.Assembly.chacha_buses_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.chacha_buses_balanced
