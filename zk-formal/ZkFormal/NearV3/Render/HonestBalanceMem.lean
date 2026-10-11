import ZkFormal.NearV3.Render.HonestBalanceSrec
import ZkFormal.NearV3.Rcpt.Candidates.NativeReceiptMemAggregate
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountMemContext
import ZkFormal.NearV3.Rcpt.Candidates.ReceiptJobOrder

/-!
# Honest MEM balance (`rcptV3` ↔ `acctV3`)

The honest receipt trace with `accountId` pinned to the native account slots
(`accountSlot x.t keys ·.receiptIndex`) has receipt `MEM` traffic equal to the native ledger
lanes (`native_receipt_mem_aggregate`, transported from the routing-q-patched trace: the patch
touches only `xb12..18`, none of the memory fields), and the account table of
`nativeAccountViews x.t replay rs` closes them (`native_account_memory_balance`).
-/

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof
open ZkFormal.NearV3.Render ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

theorem patch_cv (tr : Trace Fp) (r c : Nat) (hc : ¬(xb 12 ≤ c ∧ c ≤ xb 18)) :
    cv (RoutingQCandidate.patchTrace tr 0) 0 r c = cv tr 0 r c := by
  unfold cv; rw [RoutingQCandidate.patch_other tr 0 r c hc]

theorem patch_colAt (tr : Trace Fp) (s len c : Nat) (hc : ¬(xb 12 ≤ c ∧ c ≤ xb 18)) :
    colAt (RoutingQCandidate.patchTrace tr 0) 0 s len c = colAt tr 0 s len c := by
  unfold colAt; apply List.map_congr_left; intro i _; exact patch_cv tr _ c hc

/-- The memory lanes of a receipt write. -/
def memSendLanes (r : Nat) (x : RcptE) : List Msg :=
  (List.range 16).map fun i => [x.kslot, r + 1, i, x.aft.getD i 0, x.lk.getD i 0, x.st.getD i 0]

/-- The memory lanes of a receipt read. -/
def memRecvLanes (x : RcptE) : List Msg :=
  (List.range 16).map fun i => [x.kslot, x.tprev, i, x.bef.getD i 0, x.lk.getD i 0, x.st.getD i 0]

theorem rSends_mem (pub : List Fp) (xs : List RcptE) (j r o : Nat) (x : RcptE) :
    rSends pub xs j r o x B_MEM = memSendLanes r x := by
  simp only [rSends, memSendLanes, show B_MEM ≠ B_BYTES by decide, show B_MEM ≠ B_KEYNIB by decide,
    ite_false, ite_true]

theorem rRecvs_mem (r : Nat) (x : RcptE) : rRecvs r x B_MEM = memRecvLanes x := by
  simp only [rRecvs, memRecvLanes, show B_MEM ≠ B_DIGEST by decide, show B_MEM ≠ B_FINAL by decide,
    ite_false, ite_true]

theorem patch_mem_fields (tr : Trace Fp) (y : RS) :
    let a := rcptOf (RoutingQCandidate.patchTrace tr 0) 0 y
    let b := rcptOf tr 0 y
    a.kslot = b.kslot ∧ a.tprev = b.tprev ∧ a.bef = b.bef ∧ a.lk = b.lk ∧ a.st = b.st ∧ a.aft = b.aft := by
  refine ⟨patch_cv _ _ _ (by decide), patch_cv _ _ _ (by decide), patch_colAt _ _ _ _ (by decide),
    patch_colAt _ _ _ _ (by decide), patch_colAt _ _ _ _ (by decide), ?_⟩
  simp only [rcptOf]
  apply List.map_congr_left
  intro k _
  exact ZkFormal.NearV3.Render.SizeRender.bitsVal_congr _ _ 8 (fun e he =>
    patch_cv tr _ _ (by unfold xb; omega))

theorem patch_mem_lanes (tr : Trace Fp) (y : RS) (r : Nat) :
    memSendLanes r (rcptOf (RoutingQCandidate.patchTrace tr 0) 0 y) = memSendLanes r (rcptOf tr 0 y) ∧
    memRecvLanes (rcptOf (RoutingQCandidate.patchTrace tr 0) 0 y) = memRecvLanes (rcptOf tr 0 y) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := patch_mem_fields tr y
  simp only [memSendLanes, memRecvLanes] at *
  rw [h1, h2, h3, h4, h5, h6]
  exact ⟨rfl, rfl⟩

/-- Global order of the receipt `MEM` traffic. -/
theorem rcpt_mem_traffic (pub : List Fp) (ls : RcptV3Vs) :
    rcptSends3 pub ls B_MEM = ((flatR ls).zipIdx).flatMap (fun p => memSendLanes p.2 p.1) ∧
    rcptRecvs3 ls B_MEM = (flatR ls).flatMap memRecvLanes := by
  constructor
  · have hh := Rcpt.Candidates.located_global_order ls 0 (fun r x => memSendLanes r x)
    simp only [Nat.zero_add] at hh
    rw [← hh]
    unfold rcptSends3
    simp only [show B_MEM ≠ B_BYTES by decide, show B_MEM ≠ B_RCL by decide, ite_false,
      List.nil_append, rSends_mem]
  · have hh := Rcpt.Candidates.located_global_order ls 0 (fun _ x => memRecvLanes x)
    simp only [Nat.zero_add] at hh
    unfold rcptRecvs3
    simp only [rRecvs_mem]
    rw [hh]
    clear hh
    generalize flatR ls = xs
    have : ∀ n, (xs.zipIdx n).flatMap (fun p => memRecvLanes p.1) = xs.flatMap memRecvLanes := by
      induction xs with
      | nil => intro n; rfl
      | cons a xs ih => intro n; simp [List.zipIdx_cons, ih]
    exact this 0

/-- `zipIdx` of a mapped list whose elements carry their own position. -/
theorem zipIdx_map_index {α β : Type} (l : List α) (f : α → β) (idx : α → Nat)
    (h : l.map idx = List.range l.length) :
    (l.map f).zipIdx = l.map (fun a => (f a, idx a)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < l.length := by simpa using h1
    have hg := congrArg (fun m => m[i]?) h
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_range hi,
      Option.map_some, Option.some.injEq] at hg
    simp [hg]

/-- The native account-memory data the honest MEM balance needs, beyond `RcptOk`. -/
structure MemOk (x : RcptInput) (replay : PTrie) (as : List AcctV) : Prop where
  /-- `accountId` is the native account slot of each receipt's receiver in the pre-state -/
  acc : x.accountId = fun p => accountSlot x.t
    ((x.lists.flatten.map Input.receipt).map (fun r => accountKeyPath r.receiverId)) p.receiptIndex
  shape : TrieShape x.t
  pair : Rcpt.Candidates.WriteTreePair x.t replay
  post : ∀ account, replay.find (accountKeyPath account) = x.out.trie.find (accountKeyPath account)
  views : nativeAccountViews x.t replay (x.lists.flatten.map Input.receipt) = some as
  vals : (NearSpecV3.valsOf x.t).length < Algebra.P

theorem located_mem_sends (pub : List Fp) (tr : Trace Fp) (lists : List (List Input)) :
    locatedMemSends pub tr lists = (receiptLocations 0 (entityPlans lists)).flatMap
      (fun l => memSendLanes l.2.receiptIndex (rcptOf tr 0 (inputShape l.1 l.2.input))) := by
  unfold locatedMemSends; simp only [rSends_mem]

theorem located_mem_recvs (tr : Trace Fp) (lists : List (List Input)) :
    locatedMemRecvs tr lists = (receiptLocations 0 (entityPlans lists)).flatMap
      (fun l => memRecvLanes (rcptOf tr 0 (inputShape l.1 l.2.input))) := by
  unfold locatedMemRecvs; simp only [rRecvs_mem]

/-- **MEM balances between the honest receipt and account tables.** -/
theorem honest_mem_balance (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x)
    {replay : PTrie} {as : List AcctV} (hm : MemOk x replay as) :
    ((rcptTraffic3 pub (nativeRcptLists pub x)).sends B_MEM ++ (acctV3Traffic as).sends B_MEM).Perm
      ((rcptTraffic3 pub (nativeRcptLists pub x)).recvs B_MEM ++ (acctV3Traffic as).recvs B_MEM) := by
  obtain ⟨mid, so, steps, hmid, hl, -, -, -⟩ := booleanReceiptTrace_native_candidate_tableLocal
    ok.prep ok.walk ok.witness x.own x.ctx x.lists ok.source ok.applied ok.wf ok.nonempty ok.named
    ok.flags ok.run ok.gas x.accountId x.accessId x.constants pub (nativeDigests x.ctx x.digests) x.fallback
    x.headerFallback ok.gasPub ok.price ok.finalPub ok.owner
  have hs : x.steps = steps := by
    unfold RcptInput.steps; rw [hmid]; simp only [hl, Option.getD_some]
  obtain ⟨limits, after, happ, hafter, ho, hv, hpre⟩ := newchunk_mem_context hm.shape ok.run hmid hl
  have hagg := native_receipt_mem_aggregate x.own x.ctx x.k x.lists 22 x.constants pub
    (nativeDigests x.ctx x.digests) x.accessId x.fallback
    (completeReceiptHeaders (depositHeaderAux x.headerFallback)) x.t replay as ⟨mid, [], [], 0, 0⟩ steps
    hm.views hm.vals ok.run ok.gas hl ho hv hpre
  simp only at hagg
  rw [← hm.acc, ← hs] at hagg
  have hagg' : locatedMemSends pub (RoutingQCandidate.patchTrace (rcptTraceNative pub x) 0) x.lists =
        nativeLedgerMemWrites x.t (x.lists.flatten.map Input.receipt) x.steps ∧
      locatedMemRecvs (RoutingQCandidate.patchTrace (rcptTraceNative pub x) 0) x.lists =
        nativeLedgerMemReads x.t (x.lists.flatten.map Input.receipt) x.steps := hagg
  rw [hs] at hagg'
  obtain ⟨hws, hwr⟩ := hagg'
  rw [located_mem_sends] at hws
  rw [located_mem_recvs] at hwr
  simp only [fun l : Nat × ReceiptPlan => (patch_mem_lanes (rcptTraceNative pub x)
    (inputShape l.1 l.2.input) l.2.receiptIndex).1,
    fun l : Nat × ReceiptPlan => (patch_mem_lanes (rcptTraceNative pub x)
    (inputShape l.1 l.2.input) 0).2] at hws hwr
  have hidx := native_locations_indices x.lists
  have hlen : (receiptLocations 0 (entityPlans x.lists)).length = x.lists.flatten.length := by
    simpa using congrArg List.length hidx
  have hflat := nativeRcptLists_flat pub x ok
  obtain ⟨hsend, hrecv⟩ := rcpt_mem_traffic pub (nativeRcptLists pub x)
  have hS : (rcptTraffic3 pub (nativeRcptLists pub x)).sends B_MEM =
      nativeLedgerMemWrites x.t (x.lists.flatten.map Input.receipt) steps := by
    show rcptSends3 pub (nativeRcptLists pub x) B_MEM = _
    rw [hsend, hflat, locatedViews, zipIdx_map_index _ _ (fun l => l.2.receiptIndex)
      (by rw [hidx, hlen]), List.flatMap_map]
    exact hws
  have hR : (rcptTraffic3 pub (nativeRcptLists pub x)).recvs B_MEM =
      nativeLedgerMemReads x.t (x.lists.flatten.map Input.receipt) steps := by
    show rcptRecvs3 (nativeRcptLists pub x) B_MEM = _
    rw [hrecv, hflat, locatedViews, List.flatMap_map]
    exact hwr
  rw [hS, hR]
  exact native_account_memory_balance (st := (⟨mid, [], [], 0, 0⟩, limits)) happ hl ho hv hm.pair hpre
    (fun a => (hm.post a).trans (by rw [hafter])) hm.views

end ZkFormal.NearV3.Assembly.RcptSkeleton
