import ZkFormal.NearV3.Assembly.RenderV3RcptTables
import ZkFormal.NearV3.Render.AcceptedQv
import ZkFormal.NearV3.Render.AcceptedRcpt
import ZkFormal.NearV3.Render.AcceptedMem
import ZkFormal.NearV3.Render.AcceptedSrcp

/-! Guard the receipt-side `TableRenderV3` instances. -/

/-- info: 'ZkFormal.NearV3.Assembly.rcptRenderV3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.rcptRenderV3

/-- info: 'ZkFormal.NearV3.Assembly.srcpRenderV3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.srcpRenderV3

/-- info: 'ZkFormal.NearV3.Assembly.qvRenderV3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.qvRenderV3

/-- info: 'ZkFormal.NearV3.Render.qvNativeOk_of_accept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.qvNativeOk_of_accept

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.rcptOk_of_accept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.rcptOk_of_accept

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.memOk_of_accept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.memOk_of_accept

/-- info: 'ZkFormal.NearV3.Render.acctV3Ok_of_views' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.acctV3Ok_of_views

/-- info: 'ZkFormal.NearV3.Render.accepted_rcl_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.accepted_rcl_balance

/-- info: 'ZkFormal.NearV3.Render.accepted_src_balance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.accepted_src_balance
