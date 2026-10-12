import ZkFormal.NearV3.Render.AcceptedSrcp

/-! Guard the assumptions of the acceptance-only srcp input discharge (widths, RC length). -/

/-- info: 'ZkFormal.NearV3.Render.entry_rc_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.entry_rc_length_le

/-- info: 'ZkFormal.NearV3.Render.acceptedSrcp_ok_of_accept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.acceptedSrcp_ok_of_accept
