import ZkFormal.NearV3.Assembly.UpsS0FAddr
import ZkFormal.NearV3.Assembly.SchedulerSanityPin
import ZkFormal.NearV3.Rcpt.Candidates.NativePayloadSegments
import ZkFormal.NearV3.Rcpt.Candidates.NativeWriteValueIndex

/-!
# Ups `S0F` payloads over the native pre forest (rebasing the main upsert)

The trie side's scheduler upserts run on `oldPost :: steps.pre` (the main upsert rebased onto the
account replay's result); the codec reads `m.pre :: steps.pre`.  The account writes never touch
`keyBwState` and keep the forest's shape, so the `S0F` payloads agree (`s0f_rebase`).
-/
namespace ZkFormal.NearV3.Assembly.UpsS0F
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3.Render Render.UpsGen UpsRows ZkFormal.NearV3.Assembly
open ZkFormal.NearV3.Assembly.CodecDigest Rcpt.Candidates.NodePostUpdate

/-- The ups `S0F` payload of instance `I` at forest position `τ` of `F` is the codec's. -/
def S0FAt (F : List PTrie) (tau : Nat) (I : UpsInst) : Prop :=
  ∀ t, F[tau]? = some t → s0fOf I = s0fPair (F.take tau) t

theorem s0f_rebase {pre oldPost : PTrie} {writes : List (List Nat × Bytes)}
    (h : Rcpt.Candidates.SizedAccountRun pre writes oldPost) (hk : ∀ kv ∈ writes, keyBwState ≠ kv.1)
    (rest : List PTrie) (tau : Nat) (t t' : PTrie)
    (ht : (oldPost :: rest)[tau]? = some t) (ht' : (pre :: rest)[tau]? = some t') :
    s0fPair ((oldPost :: rest).take tau) t = s0fPair ((pre :: rest).take tau) t' := by
  have hsk : Rcpt.Candidates.WriteTreePair pre oldPost := h.forget.skeleton
  cases tau with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ht ht'
    subst ht ht'
    have hf := sized_find_other h keyBwState hk
    have hv := write_value_index hsk keyBwState
    simp only [s0fPair, priorValueId, hf, hv, List.take_zero]
  | succ j =>
    simp only [List.getElem?_cons_succ] at ht ht'
    rw [ht] at ht'
    cases ht'
    have hl := write_vals_count hsk
    simp only [s0fPair, priorValueId, forestLookupVid, forestBytes, List.take_succ_cons, List.flatMap_cons,
      List.length_append, hl]

end ZkFormal.NearV3.Assembly.UpsS0F
