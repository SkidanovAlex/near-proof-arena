import ZkFormal.NearV3.Render.CodecVbytesBal

/-! Guard the `VBYTES` (bus 21) and `MPOS` (bus 9) balances of the honest render (lane v3-render-vbytes). -/

#print axioms ZkFormal.NearV3.Assembly.VbytesKeys.buildFor_good
#print axioms ZkFormal.NearV3.Render.CdcGrant.decode_encode'
#print axioms ZkFormal.NearV3.Render.CdcGrant.prior_stateBytes
#print axioms ZkFormal.NearV3.Render.CdcGrant.codec_vbytes_native
#print axioms ZkFormal.NearV3.Assembly.VbytesPart.main_final
#print axioms ZkFormal.NearV3.Assembly.VbytesPart.main_partition
#print axioms ZkFormal.NearV3.Assembly.VbytesPart.forest_partition_bw
#print axioms ZkFormal.NearV3.Assembly.VbytesPart.vbytes_native
#print axioms ZkFormal.NearV3.Assembly.RenderBundleV3.balancedAt_vbytes
#print axioms ZkFormal.NearV3.Assembly.RenderBundleV3.balancedAt_mpos
#print axioms ZkFormal.NearV3.Assembly.TrieSide.trie_side_exact
#print axioms ZkFormal.NearV3.Assembly.RcptTrieSide.rcpt_trie_sched
#print axioms ZkFormal.NearV3.Assembly.RcptTrieSide.rcpt_trie_vbytes
