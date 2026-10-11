import ZkFormal.NearV3.Render.AcceptedRcpt
import ZkFormal.NearV3.Candidates.NativeAcceptedAccountViews
import ZkFormal.NearV3.Rcpt.Candidates.NativeOldTreeReconstruct
import ZkFormal.NearV3.Rcpt.Candidates.NativeForestAllocation
import ZkFormal.NearV3.Assembly.NativeUnfold
import ZkFormal.NearV3.Assembly.QueueSeed

/-!
# `MemOk` and the account views from acceptance

With `accountId` pinned to the native account slots, an accepted witness gives the replayed
old-record tree `oldPost` (`newchunk_old_tree_reconstruct`) and the native account views `as`
(`NativeAcceptedAccountViews.accepted`) such that `MemOk` holds; also `|as| ≤ 4481`,
`as = [] ∨ AcctWf as` and byte-valued pre/post values (for `AcctV3Ok`).
-/

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Rcpt.Candidates ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

/-- The native account slot of each planned receipt. -/
def nativeAccountId (pre : PTrie) (lists : List (List Input)) (q : ReceiptPlan) : Nat :=
  accountSlot pre ((lists.flatten.map Input.receipt).map (fun r => accountKeyPath r.receiverId)) q.receiptIndex

theorem memOk_of_accept {cb wb raw : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes} {p : Prep}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B0 cb wb = .ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hd : decodeStateWitness raw = .ok w) (hp : prepD0 cb (nativeHint k w m) = .ok p)
    (accessId : ReceiptPlan → Option Nat)
    (constants : ReceiptPlan → Nat → Fp) (digests : ReceiptPlan → Nat → List Fp)
    (fallback : ReceiptPlan → Coord → Nat → Fp) (headerFallback : ListPlan → Coord → Nat → Fp) :
    ∃ replay as, MemOk (acceptedRcptInput cb raw k w m p
        (nativeAccountId m.pre (sourceInputLists (m.ctx k) p.lists w.entries))
        accessId constants digests fallback headerFallback) replay as ∧
      as.length ≤ 4481 ∧ (as = [] ∨ AcctWf as) ∧ (∀ a ∈ as, ∀ b ∈ a.pre ++ a.post, b < 256) := by
  have hrel : RelD0a B0 cb wb := (relD0a_iff B0 cb wb).mpr h
  obtain ⟨-, happ, -, -, -, -⟩ := ReceiptSourceInputs.admitted (m.ctx k) hrel hp hk hw hd
  have hwell : m.pre.wf = true := by
    rw [hm.pre]
    exact (built_spec w.main.values trieFuel k.slotB2.prevStateRoot _ hm.root_length).2.1
  obtain ⟨writes, oldPost, mid, so, -, -, hr, hpair, -, -, hup⟩ :=
    newchunk_old_tree_reconstruct (TrieShape.of_wf _ hwell) hwell hm.run
  obtain ⟨as, hlen, hwf, hbytes, -, hviews⟩ := NativeAcceptedAccountViews.accepted hk hw h hm hv
  have hcount := (forest_allocation_counts (m.pre :: steps.map ImplicitStepV3.pre)
    (checkD0a_preBytes hk hw h hm hv)).2
  have hvals : (NearSpecV3.valsOf m.pre).length < Algebra.P := by
    simp only [forestBytes, List.flatMap_cons, List.length_append] at hcount
    rw [native_valsOf_eq]
    unfold Algebra.P
    omega
  refine ⟨oldPost, as, ⟨rfl, TrieShape.of_wf _ hwell, hpair, ?_, ?_, hvals⟩, hlen, hwf, hbytes⟩
  · intro account
    exact (ZkFormal.NearV3.find_upsert_ne (SizedAccountRun.wf hr hwell) (by decide)
      (by simp [keyBwState, accountKeyPath, nibbles]) hup).symm
  · show nativeAccountViews m.pre oldPost ((sourceInputLists (m.ctx k) p.lists w.entries).flatten.map Input.receipt) = some as
    rw [happ]
    exact hviews writes oldPost so.state hr hup

end ZkFormal.NearV3.Assembly.RcptSkeleton

namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Algebra

/-- **`AcctV3Ok` for the native account views** whenever at least one account is read
(`as ≠ []`): rows `16·|as| ≤ 16·4481 ≤ 2^17`, 72 byte-valued pre bytes with a
non-`u128::MAX` amount (`AcctWf.notMax`), 16 post values, canonical slot and version. -/
theorem acctV3Ok_of_views (as : List AcctV) (hne : as ≠ []) (hlen : as.length ≤ 4481)
    (hwf : AcctWf as) (hbytes : ∀ a ∈ as, ∀ b ∈ a.pre ++ a.post, b < 256) : AcctV3Ok as := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases as with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  · have : (2 : Nat) ^ AcctV3.maxLog = 131072 := rfl
    omega
  · intro a ha
    have hl := hwf.len a ha
    have hb : ∀ b ∈ a.pre, b < 256 := fun b hb => hbytes a ha b (List.mem_append_left _ hb)
    refine ⟨hl.1, hb, hwf.notMax a ha (fun i _ => ?_)⟩
    rw [List.getD_eq_getElem?_getD]
    cases h : a.pre[i]? with
    | none => simp
    | some x => simpa using hb x (List.mem_of_getElem? h)
  · intro a ha
    have hl := hwf.len a ha
    exact ⟨hl.2.1, fun b hb => by
      have := hbytes a ha b (List.mem_append_right _ hb); unfold ZkFormal.Algebra.P; omega⟩
  · intro a ha
    have hl := hwf.len a ha
    exact ⟨hl.2.2.1, hl.2.2.2⟩

end ZkFormal.NearV3.Render
