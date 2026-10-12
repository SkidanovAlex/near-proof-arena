import ZkFormal.NearV3.Render.HonestBalanceBnd
import ZkFormal.NearV3.Candidates.ReceiptSourceInputs
import ZkFormal.NearV3.Candidates.ReceiptPreparedFinalPublic
import ZkFormal.NearV3.Assembly.RcptGasPrepared
import ZkFormal.NearV3.Assembly.NativePrepared

/-!
# `RcptOk` from acceptance

An accepted witness gives the honest receipt input: the claim and witness bytes, the native
hint and prepared statement, the native main execution's context, pre-state and result, and
the raw authenticated source lists `sourceInputLists ctx p.lists w.entries` (one per prepared
occurrence, in applied order).  Every field of `RcptOk` on the prepared public vector
`pubOf (preparedBytes p overhead)` follows (`rcptOk_of_accept`); the auxiliary renderer
choices (`accountId`, `accessId`, constants, digests, fallbacks) are free.
-/

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3
open ZkFormal.NearV3.Candidates

/-- The honest receipt input of an accepted witness. -/
def acceptedRcptInput (cb raw : Bytes) (k : WalkD0) (w : StateWitness) (m : MainExecutionV3)
    (p : Prep) (accountId : ReceiptPlan → Nat) (accessId : ReceiptPlan → Option Nat)
    (constants : ReceiptPlan → Nat → Fp) (digests : ReceiptPlan → Nat → List Fp)
    (fallback : ReceiptPlan → Coord → Nat → Fp) (headerFallback : ListPlan → Coord → Nat → Fp) :
    RcptInput :=
  ⟨cb, raw, nativeHint k w m, p, k, w, k.H.shardId, m.ctx k,
    sourceInputLists (m.ctx k) p.lists w.entries, m.pre, m.result,
    accountId, accessId, constants, digests, fallback, headerFallback⟩

/-- **`RcptOk` from acceptance.** -/
theorem rcptOk_of_accept {cb wb raw : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {p : Prep}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B0 cb wb = .ok ())
    (hm : m.NativeValid k w) (hd : decodeStateWitness raw = .ok w)
    (hp : prepD0 cb (nativeHint k w m) = .ok p) (overhead : Nat)
    (accountId : ReceiptPlan → Nat) (accessId : ReceiptPlan → Option Nat)
    (constants : ReceiptPlan → Nat → Fp) (digests : ReceiptPlan → Nat → List Fp)
    (fallback : ReceiptPlan → Coord → Nat → Fp) (headerFallback : ListPlan → Coord → Nat → Fp) :
    RcptOk (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead))
      (acceptedRcptInput cb raw k w m p accountId accessId constants digests fallback headerFallback) := by
  have hrel : RelD0a B0 cb wb := (relD0a_iff B0 cb wb).mpr h
  have hc : checkD0 cb wb = .ok () := by
    have hh := hrel.1
    unfold RelD0 acceptsD0 at hh
    split at hh <;> simp_all
  obtain ⟨hsrc, happ, hwf, hne, hnamed, hflags⟩ :=
    ReceiptSourceInputs.admitted (m.ctx k) hrel hp hk hw hd
  obtain ⟨hgas, hprice⟩ := ReceiptSourceInputs.gas hrel hp hk hm
  have hr : Public.RootsSized p := prepD0_roots hp
  obtain ⟨hn, hb, hown, ht⟩ := ReceiptPreparedFields.native_fields hp hk hw hc hm
  have hrun : applyNewChunk prims (m.ctx k) m.pre
      ((sourceInputLists (m.ctx k) p.lists w.entries).flatten.map Input.receipt) = .ok m.result := by
    rw [happ]; exact hm.run
  refine ⟨hp, hk, hd, hsrc, happ, hwf, hne, hnamed, hflags, hrun, hgas,
    prepD0_native_GasPublicBytes overhead hp hk hm, hprice, ?_, ?_⟩
  · have hlen : p.hdr.n = (sourceInputLists (m.ctx k) p.lists w.entries).flatten.length := by
      rw [hn, ← happ, List.length_map]
    have hbody : p.body.length =
        8 + ((sourceInputLists (m.ctx k) p.lists w.entries).flatten.map refundLength).sum := by
      rw [hb]
      exact applyNewChunk_planned_body_length (m.ctx k) _ hwf hflags hrun
    constructor
    · intro i hi
      rw [Public.pub_getD, ReceiptPreparedFields.count_byte p overhead i hr hi]
      change Fp.ofNat (((u32 p.hdr.n).getD i 0).toNat) = _
      rw [hlen]; rfl
    · intro i hi
      rw [Public.pub_getD, ReceiptPreparedFields.body_byte p overhead i hr hi]
      change Fp.ofNat (((u32 p.body.length).getD i 0).toNat) = _
      rw [hbody]; rfl
    · intro i hi
      rw [Public.pub_getD, ReceiptPreparedFields.burnt_byte p overhead i hr hi]
      change Fp.ofNat (((u128 p.hdr.balanceBurnt).getD i 0).toNat) = _
      rw [ht]; rfl
  · intro i hi
    rw [Public.pub_getD, ReceiptPreparedFields.own_byte p overhead i hr hi]
    change Fp.ofNat (((u64 p.hdr.own).getD i 0).toNat) = _
    rw [hown]; rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
