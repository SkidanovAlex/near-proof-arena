import ZkFormal.NearV3.Render.PaddedQvNative
import ZkFormal.NearV3.Assembly.PrepBodyComplete
import ZkFormal.NearV3.Assembly.QueueCapacity
import ZkFormal.NearV3.Candidates.NativeSizeConstruction
import ZkFormal.NearV3.Candidates.NativeQueueCounters
import ZkFormal.NearV3.Qv.Candidates.CombinedPublic

/-!
# `QvNativeOk` from acceptance

An accepted witness (`checkD0a B0 cb wb = .ok ()`) with its native main execution `m`, its
implicit steps and its prepared statement `p` yields main values `v` such that the honest
queue table over `(m.pre, v, steps.map pre)` satisfies `QvNativeOk` on the prepared public
vector: valid values and records and the row bound (`checkD0a_queue_rows_fit`), and the
public implicit count `= |steps|` (`kPublic_prepared`, `K = |steps|`).
-/

namespace ZkFormal.NearV3.Render
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open ZkFormal.NearV3.Assembly ZkFormal.NearV3.Qv ZkFormal.NearV3.Qv.Candidates
open ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen

theorem qvNativeOk_of_accept {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes} {p : Prep}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B0 cb wb = .ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hp : prepD0 cb (nativeHint k w m) = .ok p) (overhead : Nat) :
    ∃ v : MainValues, QvNativeOk m.pre v (steps.map ImplicitStepV3.pre)
      (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) := by
  obtain ⟨v, hvalid, -, hrecords, hfit⟩ := checkD0a_queue_rows_fit hk hw h hm hv
  have hrel : RelD0a B0 cb wb := (relD0a_iff B0 cb wb).mpr h
  obtain ⟨-, hr, -, hpk⟩ := Candidates.NativeSizeConstruction.public_fields hrel hp hw hk
  have hcheck := h
  unfold checkD0a at hcheck
  obtain ⟨u, hcheck, -⟩ := ReexecV3D0.bind_ok' hcheck
  cases u
  obtain ⟨-, -, -, -, hcnt, hK⟩ := checkD0_native_steps hk hw hcheck
  have hl := hv.length
  simp only [List.length_zip] at hl
  have hcK : steps.length = p.hdr.K := by omega
  have hK32 : p.hdr.K < 256 ^ 4 := by omega
  refine ⟨v, hvalid, hrecords, ?_, ?_⟩
  · unfold qvRows qvNativeWalks qvNativeRecords
    rw [plan_rows_length]
    rw [plan_rows_length] at hfit
    exact hfit
  · intro r
    rw [CombinedTable.kPublic_prepared _ _ _ p overhead hr hK32, List.length_map, hcK]
    rfl

end ZkFormal.NearV3.Render
