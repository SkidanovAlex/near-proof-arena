import ZkFormal.NearV3.Assembly.RenderV3RcptLayout
import ZkFormal.NearV3.Assembly.FactorComplete
import ZkFormal.NearV3.Assembly.FactorSound

/-! Guard the assumptions of A12 (`c.layout_wf`) and its uses. -/

/-- info: 'ZkFormal.NearV3.Assembly.layoutWf_of_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.layoutWf_of_rel

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.bounds_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.bounds_eq

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.prepared_lt_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.prepared_lt_P

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.pubFit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.pubFit

/-- info: 'ZkFormal.NearV3.Assembly.RcptBal.bndp_balanced_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptBal.bndp_balanced_accepted

/-- info: 'ZkFormal.NearV3.Assembly.RcptBal.src_balanced_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptBal.src_balanced_accepted

/-- info: 'ZkFormal.NearV3.Assembly.factorSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.factorSound

/-- info: 'ZkFormal.NearV3.Assembly.factorComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.factorComplete

/-- info: 'ZkFormal.NearV3.Assembly.checkD0a_prepClaim_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.checkD0a_prepClaim_exists

/-- info: 'NearSpecV3.relD0a_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms NearSpecV3.relD0a_iff

/-- info: 'NearSpecV3.relD0a_mono_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms NearSpecV3.relD0a_mono_all
