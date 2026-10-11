import ZkFormal.NearV3.Render.BundleSched
import ZkFormal.NearV3.Candidates.ReceiptPreparedFields
import ZkFormal.NearV3.Sched.View.CodecEnc

/-!
# Table 23 (outcome Merkle tree) from acceptance

For an accepted witness with its native main execution `m` and the native hint
(`nativeHint k w m`), the explicit premises of `mrkRenderV3` hold for the native outcomes
`m.result.outcomes` over the prepared public vector: at most `4481` outcomes (A1 bounds the
receipts), the public count bytes are the bytes of the outcome count (`p.hdr.n` = applied receipts =
outcomes), and the public outcome-root bytes are `outcomeRoot` of the native outcomes.
-/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

theorem mrk_premises_accepted {cb wb : Bytes} {p : Prep} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} (hp : prepD0 cb (nativeHint k w m) = .ok p) (hk : walkD0 cb = .ok k)
    (hw : decodeW wb = .ok w) (hc : checkD0a B0 cb wb = .ok ()) (hm : m.NativeValid k w)
    (overhead : Nat) :
    let pub := ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p overhead)
    m.result.outcomes.length ≤ 4481 ∧
    (∀ i < 4, pub.getD (ZkFormal.NearV3.PH_N + i) 0 = Fp.ofNat (m.result.outcomes.length / 256 ^ i % 256)) ∧
    (∀ i < 32, pub.getD (ZkFormal.NearV3.PH_OUT + i) 0 =
      Fp.ofNat (((NearSpec.outcomeRoot m.result.outcomes).getD i 0).toNat)) := by
  intro pub
  have hrel : RelD0a B0 cb wb := (relD0a_iff B0 cb wb).mpr hc
  have hg : (m.ctx k).gasLimit ≤ maxGasLimitD0 := by
    change k.slotB2.gasLimit ≤ maxGasLimitD0
    simpa only [a1, hk, decide_eq_true_eq] using hrel.2.1
  have hc' := hc
  unfold checkD0a at hc'
  obtain ⟨u, hc0, _⟩ := ReexecV3D0.bind_ok' hc'
  cases u
  have hlen : m.result.outcomes.length = (appliedReceipts k w).length := by
    rw [RcptSkeleton.applyNewChunk_outcomes prims hm.run, List.length_map]
  have hr := prepD0_roots hp
  have hfields := ZkFormal.NearV3.Candidates.ReceiptPreparedFields.native_fields hp hk hw hc0 hm
  refine ⟨?_, ?_, ?_⟩
  · rw [hlen]; exact applyNewChunk_receipt_bound hm.run hg
  · intro i hi
    change (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p overhead)).getD _ 0 = _
    rw [ZkFormal.NearV3.Public.pub_getD,
      ZkFormal.NearV3.Candidates.ReceiptPreparedFields.count_byte p overhead i hr hi, hfields.1, ← hlen]
    unfold ZkFormal.NearV3.Public.byteF
    rw [show u32 m.result.outcomes.length = leN 4 m.result.outcomes.length from rfl,
      ZkFormal.NearV3.Sched.Codec.leN_getD 4 _ i hi]
  · intro i hi
    change (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p overhead)).getD _ 0 = _
    rw [ZkFormal.NearV3.Public.pub_getD, RcptSkeleton.prepared_outcome_byte p overhead i hr hi,
      RcptSkeleton.prepD0_native_outcomeRoot hp hk hw hc0 hm]

/-- **Table 23 from acceptance** (native outcomes, prepared public vector). -/
def mrkRender_accepted {cb wb : Bytes} {p : Prep} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} (hp : prepD0 cb (nativeHint k w m) = .ok p) (hk : walkD0 cb = .ok k)
    (hw : decodeW wb = .ok w) (hc : checkD0a B0 cb wb = .ok ()) (hm : m.NativeValid k w)
    (overhead : Nat) :
    TableRenderV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p overhead)) 23 (by decide) :=
  mrkRenderV3 _ m.result.outcomes (mrk_premises_accepted hp hk hw hc hm overhead).1
    (mrk_premises_accepted hp hk hw hc hm overhead).2.1 (mrk_premises_accepted hp hk hw hc hm overhead).2.2

end ZkFormal.NearV3.Render
