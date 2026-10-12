import ZkFormal.NearV3.Assembly.TrieShaEmpty

/-- info: 'ZkFormal.NearV3.Assembly.TrieShaEmpty.native_sha_ofE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.TrieShaEmpty.native_sha_ofE
/-- info: 'ZkFormal.NearV3.Assembly.TrieShaEmpty.sha_bins_ofE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.TrieShaEmpty.sha_bins_ofE
/-- info: 'ZkFormal.NearV3.Assembly.TrieShaEmpty.valueJobsE_digests' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.TrieShaEmpty.valueJobsE_digests

open ZkFormal.NearV3.Assembly.TrieShaEmpty ZkFormal.NearV3.Rcpt.Candidates in
/-- behaviour guard: an empty value record yields a zero-length VPRE job (no bytes, one digest). -/
example (v : ZkFormal.NearV3.ValE) (h : v.bytes = []) :
    nativeValueShaJobsE [v] = [⟨ZkFormal.Near.msgId ZkFormal.Near.K_VPRE v.vid, []⟩] := by
  simp [nativeValueShaJobsE, h]
