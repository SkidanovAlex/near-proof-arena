import ZkFormal.NearV3.Render.CodecRecInt
import ZkFormal.NearV3.Render.CodecEndInt
import ZkFormal.NearV3.Render.CodecHeader
import ZkFormal.NearV3.Render.CodecMod

/-! Guard the frozen-codec row lemmas (lane v3-render-sched). -/

/-- info: 'ZkFormal.NearV3.Render.Cdc.hdr_int' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.hdr_int

/-- info: 'ZkFormal.NearV3.Render.Cdc.rec_in_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.rec_in_int

/-- info: 'ZkFormal.NearV3.Render.Cdc.rec_fend_int' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.rec_fend_int

/-- info: 'ZkFormal.NearV3.Render.Cdc.rec_end_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.rec_end_int

/-- info: 'ZkFormal.NearV3.Render.Cdc.rec_last_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.rec_last_int

/-- info: 'ZkFormal.NearV3.Render.Cdc.hdr_last_int' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.hdr_last_int

/-- info: 'ZkFormal.NearV3.Render.Cdc.hash_int' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.hash_int

/-- info: 'ZkFormal.NearV3.Render.Cdc.hash_last_int' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.hash_last_int

/-- info: 'ZkFormal.NearV3.Render.Cdc.ash_int' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.ash_int

/-- info: 'ZkFormal.NearV3.Render.Cdc.ash_last_int' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.ash_last_int

/-- info: 'ZkFormal.NearV3.Render.Cdc.ash_pad_int' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.ash_pad_int

/-- info: 'ZkFormal.NearV3.Render.Cdc.isZ_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.isZ_mod

/-- info: 'ZkFormal.NearV3.Render.Cdc.nzb_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.nzb_mod

/-- info: 'ZkFormal.NearV3.Render.Cdc.wt_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.wt_mod

/-- info: 'ZkFormal.NearV3.Render.Cdc.wt_off' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.wt_off

/-- info: 'ZkFormal.NearV3.Render.Cdc.gate_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Cdc.gate_zero
