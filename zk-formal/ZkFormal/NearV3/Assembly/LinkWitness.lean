import ZkFormal.NearV3.Assembly.LinkCanon
import ZkFormal.NearV3.Assembly.LinkDict
import ZkFormal.NearV3.Assembly.A7Pre
import ZkFormal.NearV3.Assembly.NativeShape
import ZkFormal.NearV3.Rcpt.Candidates.NativeWitnessCharge
import ZkFormal.NearV3.Rcpt.Candidates.NativeDictionarySize
import ZkFormal.NearV3.Rcpt.Candidates.NativeEntryShape
import ZkFormal.NearV3.Rcpt.Candidates.PreparedSourceCount
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountClaimFields
import ZkFormal.NearV3.Rcpt.Candidates.ReceiptShaPayloads
import ZkFormal.NearV3.Rcpt.Link.NativeEncoding

/-!
# ZkFormal.NearV3.Assembly.LinkWitness — `RestFieldsV3.witnessBytes` (the 8 MiB witness cap)

With the deployed public (`oh = 0`) the AIR does not check the encoded witness size itself; it
is a **capacity consequence** of what `HoldsP` already enforces (no AIR change):

* **stores** — every store blob of instance `τ ≤ K` is a record of `τ` (`nodeEnc` of a record
  tree is its serialization, `enc_fullTree`), so `Σ_τ Σ_{b ∈ store τ} (|b| + 4)` is at most
  `Σ_n (|ser n| + 4) + Σ_t (len_t + 4)` (`stores_le`); A7 (`a7_total_le`) bounds
  `Σ |ser| + Σ len ≤ B0`, every record is `≥ 11` bytes (`ser_ge`) and there are no more value
  records than nodes (`VParentBal`, `vals_le_nodes`): `11 · stores ≤ 19 · B0`;
* **dictionary** — `|sources| ≤ 1984` entries (`nativeDictionary_encoded_size`), paths
  `≤ Dp0 = 32` items (A10), the receipt bytes of the first occurrences `≤ 347 · n` with
  `n ≤ 4481` (gas, `hint_n_le`);
* **fixed** — the chunk inner with no proposals / requests / split (`HeaderSemanticsV3`),
  `≤ 33` transitions, the 220-byte frame (`witness_encoding_charge`).

Total `≤ 3,454,545 + 3,761,119 + 302 + 69·33 + 220 < 8,388,608`.  **`witnessBytes_xOf`**.
-/

namespace ZkFormal.NearV3.Assembly

open NearSpec NearSpecV3

namespace LinkWitness

/-! ## Generic sums -/

theorem filter_sum_le {α : Type} (g : α → Nat) (q : α → Bool) : ∀ (l : List α),
    ((l.filter q).map g).sum ≤ (l.map g).sum
  | [] => by simp
  | a :: l => by
    have := filter_sum_le g q l
    rw [List.filter_cons]
    split <;> simp only [List.map_cons, List.sum_cons] <;> omega

theorem eraseDups_sum_le {α : Type} [BEq α] [LawfulBEq α] (g : α → Nat) (l : List α) :
    (l.eraseDups.map g).sum ≤ (l.map g).sum := by
  match l with
  | [] => simp
  | a :: xs =>
    rw [List.eraseDups_cons]
    have h1 := eraseDups_sum_le g (xs.filter fun b => !b == a)
    have h2 := filter_sum_le g (fun b => !b == a) xs
    simp only [List.map_cons, List.sum_cons]
    omega
termination_by l.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le ..)

theorem filterMap_sum {α β : Type} (f : α → Option β) (g : β → Nat) : ∀ (l : List α),
    ((l.filterMap f).map g).sum = (l.map fun a => ((f a).map g).getD 0).sum
  | [] => rfl
  | a :: l => by
    have := filterMap_sum f g l
    rw [List.filterMap_cons]
    cases hf : f a <;> simp [hf, this]

theorem range_getD_map {α : Type} (d : α) (f : α → Nat) (l : List α) :
    ((List.range l.length).map fun n => f (l.getD n d)).sum = (l.map f).sum := by
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]

theorem zipIdx_map_range {α β : Type} (f : Nat → β) (l : List α) :
    (l.zipIdx.map fun (p : α × Nat) => f p.2) = (List.range l.length).map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem_zipIdx]

theorem sum_const_gen {α : Type} (l : List α) (c : Nat) : (l.map fun _ => c).sum = c * l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.mul_succ]; omega

theorem sum_le_of {α : Type} {f g : α → Nat} : ∀ (l : List α), (∀ a ∈ l, f a ≤ g a) →
    (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | a :: l, h => by
    have h1 := h a List.mem_cons_self
    have h2 := sum_le_of l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons, List.sum_cons]
    omega

theorem sum_add_gen {α : Type} (l : List α) (a b : α → Nat) :
    (l.map fun m => a m + b m).sum = (l.map a).sum + (l.map b).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_swap_gen {α β : Type} (F : α → β → Nat) (A : List α) (B : List β) :
    (A.map fun a => (B.map fun b => F a b).sum).sum = (B.map fun b => (A.map fun a => F a b).sum).sum := by
  induction A with
  | nil => simp only [List.map_nil, List.sum_nil]; rw [sum_const_gen]; simp
  | cons a A ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [← sum_add_gen]

/-! ## Records -/

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Link3

/-- Every well-formed node record serializes to at least `11` bytes. -/
theorem ser_ge {v : NodeV3} (hw : v.wf) : 11 ≤ (v.ser false).length := by
  cases v with
  | leaf k s m =>
    have hm := hw.2.2
    simp only [NodeV3.ser, List.length_append, List.length_cons, List.length_nil, u32Bytes_length, hm]
    omega
  | ext k kid m =>
    have hm := hw.2.2.2
    simp only [NodeV3.ser, List.length_append, List.length_cons, List.length_nil, u32Bytes_length, hm]
    omega
  | branch sv kids m =>
    have hm := hw.2.2.2
    simp only [NodeV3.ser, List.length_append, List.length_cons, List.length_nil, hm]
    cases sv <;> simp <;> omega

/-- No more value records than node records (`VPARENT` balance). -/
theorem vals_le_nodes {vs : List NodeS3} {es : List ValE} (hvb : VParentBal vs es) :
    es.length ≤ vs.length := by
  have hp : ((nodeSends3 vs B_VPARENT).map Msg.toFp).Perm ((valRecvs es B_VPARENT).map Msg.toFp) := by
    rw [List.perm_iff_count]
    intro m
    exact hvb m
  have hl := hp.length_eq
  simp only [List.length_map] at hl
  rw [vparentR] at hl
  simp only [List.length_map] at hl
  rw [← hl, vparentS]
  have : ∀ (l : List (NodeS3 × Nat)) (g : NodeS3 × Nat → List Msg), (∀ a, (g a).length ≤ 1) →
      (l.flatMap g).length ≤ l.length := by
    intro l g hg
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have := hg a
      omega
  have h := this (vs.zip (List.range vs.length)) (fun (s, _) => vparMsg s)
    (fun a => by
      rcases a with ⟨s, n⟩
      show (vparMsg s).length ≤ 1
      unfold vparMsg
      split <;> simp)
  simp only [List.length_zip, List.length_range, Nat.min_self] at h
  exact h

variable {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
  {tr : Trace Fp} {r : V3Records}

/-- The cost of a stored blob in the encoded witness: its bytes and its `u32` length prefix. -/
def cost (b : Bytes) : Nat := b.length + 4

/-- **The stores of all instances** are within the records' bytes plus four bytes each. -/
theorem stores_le (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (d : List DictionaryEntryV3) :
    ((List.range (p.hdr.K + 1)).map fun τ => (((xOf r d).store τ).map cost).sum).sum ≤
      (r.nodes.map fun s => (s.v.ser false).length + 4).sum + (r.values.map fun e => e.len + 4).sum := by
  have L := trieLink_of hp hsz hH T W
  have hw := W.nodes; have hhw := W.heads; have hvw := W.values
  have hb := L.parent; have hvb := L.vparent
  have H := L.sha
  let ns := recsOf (vpos (vid0 r.values)) r.nodes
  let V := valsOf3 r.nodes r.values
  have hlen : ns.length = r.nodes.length := recsOf_length _ _
  -- per-record weights
  let wN : Nat → Nat := fun n => ((r.nodes.getD n default).v.ser false).length + 4
  let tN : Nat → Nat := fun n => (ns.getD n default).tau
  have hinst : ∀ τ, τ ≤ p.hdr.K → (((xOf r d).store τ).map cost).sum ≤
      ((List.range ns.length).map fun n => if tN n = τ then wN n else 0).sum +
      (V.map fun v => if v.tau = τ then cost v.bytes else 0).sum := by
    intro τ hτ
    obtain ⟨hh, htau⟩ := L.chain.head_mem τ hτ
    have hbytes := rec_bytes hw hhw hvw hb H
    have hd := rootedDag3 hw hhw hvw hb hvb (vlen_le hvw) hbytes hh
    rw [htau] at hd
    have e1 := eraseDups_sum_le cost ((xOf r d).rawStore τ)
    have e2 : (((xOf r d).rawStore τ).map cost).sum =
        ((nodeEntries ns V τ).map cost).sum + ((valEntries V τ).map cost).sum := by
      show ((storeOf ns V τ).map cost).sum = _
      rw [storeOf, List.map_append, List.sum_append]
    have e3 : ((nodeEntries ns V τ).map cost).sum ≤
        ((List.range ns.length).map fun n => if tN n = τ then wN n else 0).sum := by
      unfold nodeEntries
      rw [filterMap_sum]
      apply A9Air.sum_le_sum_range
      intro n hn
      have hn' : n < ns.length := hn
      rw [List.getElem?_eq_getElem hn']
      simp only
      by_cases ht : ns[n].tau = τ
      · rw [if_pos ht]
        have hm : InInst ns τ n := ⟨ns[n], List.getElem?_eq_getElem hn', ht⟩
        obtain ⟨hn2, henc, -⟩ := enc_fullTree hd hw hbytes
          (fun p hp c l r pre po hk => by
            obtain ⟨hc, -, he⟩ := kid_sha hw hhw hvw hb H hp hk; exact ⟨hc, he⟩)
          (fun p hp i l pre po w hv => val_sha hw hhw hvw hvb H hp hv) n hm
        have htN : tN n = τ := by
          show (ns.getD n default).tau = τ
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn', Option.getD_some]; exact ht
        simp only [Option.map_some, Option.getD_some, htN, if_true, cost, wN]
        rw [henc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn2, Option.getD_some]
        simp [toB]
      · rw [if_neg ht]; simp
    have e4 : ((valEntries V τ).map cost).sum = (V.map fun v => if v.tau = τ then cost v.bytes else 0).sum := by
      unfold valEntries
      rw [List.map_map]
      clear e1 e2 e3
      induction V with
      | nil => rfl
      | cons v vs ih =>
        rw [List.filter_cons]
        by_cases hv : v.tau = τ
        · simp [hv, ih]
        · simp [hv, ih]
    show ((((xOf r d).rawStore τ).eraseDups).map cost).sum ≤ _
    omega
  -- swap the sums
  calc ((List.range (p.hdr.K + 1)).map fun τ => (((xOf r d).store τ).map cost).sum).sum
      ≤ ((List.range (p.hdr.K + 1)).map fun τ =>
          ((List.range ns.length).map fun n => if tN n = τ then wN n else 0).sum +
          (V.map fun v => if v.tau = τ then cost v.bytes else 0).sum).sum := by
        apply sum_le_of
        intro τ hτ
        exact hinst τ (by have := List.mem_range.mp hτ; omega)
    _ = ((List.range ns.length).map fun n =>
          ((List.range (p.hdr.K + 1)).map fun τ => if tN n = τ then wN n else 0).sum).sum +
        (V.map fun v => ((List.range (p.hdr.K + 1)).map fun τ =>
          if v.tau = τ then cost v.bytes else 0).sum).sum := by
        rw [sum_add_gen, sum_swap_gen (fun τ n => if tN n = τ then wN n else 0),
          sum_swap_gen (fun τ (v : ValRec3) => if v.tau = τ then cost v.bytes else 0)]
    _ ≤ ((List.range ns.length).map wN).sum + (V.map fun v => cost v.bytes).sum := by
        apply Nat.add_le_add
        · apply sum_le_of
          intro n _
          exact A7Pre.sum_ite_le _ _ _
        · apply sum_le_of
          intro v _
          exact A7Pre.sum_ite_le _ _ _
    _ ≤ _ := by
        apply Nat.add_le_add
        · rw [hlen]
          exact Nat.le_of_eq (range_getD_map default (fun s : NodeS3 => (s.v.ser false).length + 4) r.nodes)
        · simp only [V, valsOf3, List.map_map]
          apply Nat.le_of_eq
          congr 1
          apply List.map_congr_left
          intro e he
          simp only [Function.comp, cost, toB, List.length_map]
          have hs := hvw.shape e he
          cases hz : e.vz
          · rw [(hs.2 hz).1]
          · rw [(hs.1 hz).1, (hs.1 hz).2]; rfl

/-! ## Receipt count, chunk inner -/

theorem prepBody_n {pc : PrepC} {hint : Hint} {p : Prep} (h : prepBody pc hint = .ok p) :
    hint.n = 0 ∨ (hint.n - 1) * Params.G < pc.ctxB2.gasLimit := by
  unfold prepBody at h
  obtain ⟨_, _, h⟩ := Sched.bind_ok h
  obtain ⟨_, _, h⟩ := Sched.bind_ok h
  obtain ⟨_, _, h⟩ := Sched.bind_ok h
  obtain ⟨_, _, h⟩ := Sched.bind_ok h
  obtain ⟨_, hc, _⟩ := Sched.bind_ok h
  have := Sched.check_ok hc
  simpa only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] using this

/-- **At most 4481 receipts** (A1 and the compute-limit check of `prepBody`). -/
theorem hint_n_le (hp : NearSpecV3.prepD0 cb h = .ok p) {k : WalkD0} (hw : walkD0 cb = .ok k)
    (C : ClaimFieldsV3 k) {m : MainExecutionV3} (hmb : k.blks[k.b2i]? = some m.block)
    (hmp : k.blks[k.b2i + 1]? = some m.previous) : h.n ≤ 4481 := by
  obtain ⟨pc, hc, hb⟩ := Sched.bind_ok hp
  have hctx := (LinkPrepCtx.prepClaim_context_of (stateWitnessOfV3 k ⟨[], [], [], [], []⟩) hc hw hmb hmp).ctx
  have hg : pc.ctxB2.gasLimit = k.slotB2.gasLimit := by rw [hctx]; rfl
  have hn := prepBody_n hb
  have hG := C.gasLimit
  unfold maxGasLimitD0 at hG
  have hGv : Params.G = 223182562500 := by decide
  rw [hg, hGv] at hn
  omega

theorem inner_len {ci : ChunkInner} (hw : V3.innerWf ci = true) (hp : ci.proposals = [])
    (hb : ci.bwRequests = []) (hs : ci.proposedSplit = none) :
    (V3.encodeChunkInner ci).length ≤ 302 := by
  simp only [V3.innerWf, Bool.and_eq_true, V3.h32, beq_iff_eq] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, h1⟩, h2⟩, h3⟩, h4⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, h5⟩, h6⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hw
  simp only [V3.encodeChunkInner, V3.encodeCongestion, V3.encodeBwRequests, hp, hb, hs,
    List.length_append, h1, h2, h3, h4, h5, h6, encList, List.map_nil, concatAll, u8, u16, u32, u64, u128,
    leN, List.length_cons, List.length_nil]
  split <;> simp [encOpt] <;> omega

/-! ## The dictionary -/

theorem flatR_sum (f : RcptE → Nat) (ls : RcptV3Vs) :
    (ls.map fun L => (L.rs.map f).sum).sum = ((flatR ls).map f).sum := by
  induction ls with
  | nil => rfl
  | cons L ls ih =>
    have e : flatR (L :: ls) = L.rs ++ flatR ls := by simp [flatR]
    rw [e, List.map_append, List.sum_append, ← ih, List.map_cons, List.sum_cons]

/-- Receipt byte lengths of the view. -/
theorem enc_le (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ∀ x ∈ flatR r.lists, x.enc.length ≤ 347 := by
  intro x hx
  obtain ⟨toks, -, -, hwf, -⟩ := W.lists.toks
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  exact (Rcpt.Candidates.receipt_sha_lengths (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) _ (hwf i hi)).1

/-- The source-size charge of the first occurrences. -/
theorem firsts_charge (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ((Rcpt.Candidates.firstNativeEntries p.lists p.hdr.own r.lists r.srcp).map
        Rcpt.Candidates.entrySizeCharge).sum ≤
      1068 * (Rcpt.Candidates.firstSourceIndices p.lists).length + 347 * (flatR r.lists).length := by
  let lenc : Nat → Nat := fun i => ((r.lists.getD i default).rs.map fun x => x.enc.length).sum
  have hone : ∀ i, Rcpt.Candidates.entrySizeCharge
      (Rcpt.Candidates.nativeEntryAt p.lists p.hdr.own r.lists r.srcp i).entry ≤ 1068 + lenc i := by
    intro i
    simp only [Rcpt.Candidates.entrySizeCharge, Rcpt.Candidates.nativeEntryAt,
      Rcpt.Candidates.DedupProof.nativeSourceEntry, SourceEntryV3.entry, encList, List.length_append,
      u64, u32, leN, List.length_cons, List.length_nil, List.length_map, concatAll_size,
      List.map_map]
    have hpath : (r.srcp.getD i default).path.length ≤ 32 := by
      rw [List.getD_eq_getElem?_getD]
      cases hb : r.srcp[i]? with
      | none => show ([] : List SrcpItem).length ≤ 32; simp
      | some B => exact W.srcpDepth B (List.mem_of_getElem? hb)
    have hrc : (((r.lists.getD i default).rs.map fun x => x.toRcptV.toReceipt.encode.length)).sum ≤ lenc i := by
      apply Nat.le_of_eq
      congr 1
      apply List.map_congr_left
      intro x hx
      have hxf : x ∈ flatR r.lists := by
        rw [List.getD_eq_getElem?_getD] at hx
        cases hl : r.lists[i]? with
        | none =>
          rw [hl] at hx
          exact absurd hx (by show x ∉ ([] : List RcptE); simp)
        | some L =>
          rw [hl, Option.getD_some] at hx
          exact List.mem_flatMap.mpr ⟨L, List.mem_of_getElem? hl, hx⟩
      rw [← RcptLink.view_receipt_encoding W.lists hxf, Near.Link.toBytes_length]
    simp only [Function.comp_def] at hrc ⊢
    omega
  have hfi : (Rcpt.Candidates.firstSourceIndices p.lists).Nodup :=
    (List.nodup_range).filter _
  calc ((Rcpt.Candidates.firstNativeEntries p.lists p.hdr.own r.lists r.srcp).map
          Rcpt.Candidates.entrySizeCharge).sum
      = ((Rcpt.Candidates.firstSourceIndices p.lists).map fun i => Rcpt.Candidates.entrySizeCharge
          (Rcpt.Candidates.nativeEntryAt p.lists p.hdr.own r.lists r.srcp i).entry).sum := by
        simp only [Rcpt.Candidates.firstNativeEntries, Rcpt.Candidates.firstNativeSources, List.map_map]
        rfl
    _ ≤ ((Rcpt.Candidates.firstSourceIndices p.lists).map fun i => 1068 + lenc i).sum :=
        sum_le_of _ (fun i _ => hone i)
    _ = 1068 * (Rcpt.Candidates.firstSourceIndices p.lists).length +
          ((Rcpt.Candidates.firstSourceIndices p.lists).map lenc).sum := by
        rw [sum_add_gen, sum_const_gen]
    _ ≤ 1068 * (Rcpt.Candidates.firstSourceIndices p.lists).length +
          ((List.range r.lists.length).map lenc).sum := by
        apply Nat.add_le_add_left
        apply A7Pre.nodup_sum_le' lenc hfi
        intro i _ hi
        show (((r.lists.getD i default).rs).map fun x => x.enc.length).sum = 0
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : r.lists.length ≤ i), Option.getD_none]
        rfl
    _ = 1068 * (Rcpt.Candidates.firstSourceIndices p.lists).length +
          ((flatR r.lists).map fun x => x.enc.length).sum := by
        rw [range_getD_map default (fun L : ListV3 => (L.rs.map fun x => x.enc.length).sum), flatR_sum]
    _ ≤ _ := by
        apply Nat.add_le_add_left
        have := sum_le_of (f := fun x : RcptE => x.enc.length) (g := fun _ => 347) (flatR r.lists) (enc_le W)
        rwa [sum_const_gen] at this

/-- **The encoded dictionary** is at most `3,761,119` bytes. -/
theorem dict_le (hp : NearSpecV3.prepD0 cb h = .ok p) {k : WalkD0} (hw : walkD0 cb = .ok k)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (hn : (flatR r.lists).length ≤ 4481) :
    (encList V3.encodeEntry ((dictOf p r).map DictionaryEntryV3.entry)).length ≤ 3761119 := by
  have hsrc := Rcpt.Candidates.prepD0_source_count hp
  have hk : ∀ e ∈ Rcpt.Candidates.firstNativeEntries p.lists p.hdr.own r.lists r.srcp, e.key.length = 32 := by
    intro e he
    simp only [Rcpt.Candidates.firstNativeEntries, Rcpt.Candidates.firstNativeSources, List.map_map,
      List.mem_map] at he
    obtain ⟨i, hi, rfl⟩ := he
    have hil := Rcpt.Candidates.firstSourceIndices_lt p.lists hi
    show (p.lists.getD i ⟨[], 0, []⟩).key.length = 32
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil, Option.getD_some]
    exact Rcpt.Candidates.prepD0_source_key_shape hp hw _ (List.getElem_mem hil)
  have hpth : ∀ e ∈ Rcpt.Candidates.firstNativeEntries p.lists p.hdr.own r.lists r.srcp,
      ∀ s ∈ e.proof.path, s.1.length = 32 := by
    intro e he s hs
    simp only [Rcpt.Candidates.firstNativeEntries, Rcpt.Candidates.firstNativeSources, List.map_map,
      List.mem_map] at he
    obtain ⟨i, -, rfl⟩ := he
    change s ∈ (r.srcp.getD i default).path.map (fun it => (Link3.toB it.sib, if it.dir then 1 else 0)) at hs
    obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hs
    rw [List.getD_eq_getElem?_getD] at hit
    cases hb : r.srcp[i]? with
    | none =>
      rw [hb] at hit
      exact absurd hit (by show it ∉ ([] : List SrcpItem); simp)
    | some B =>
      rw [hb, Option.getD_some] at hit
      have hB := W.srcp.block B (List.mem_of_getElem? hb)
      simp only [Link3.toB, List.length_map]
      split at hB
      · rw [hB.2.1] at hit; simp at hit
      · exact (hB.len.2.2 it hit).1
  have he := Rcpt.Candidates.nativeDictionary_encoded_size p.lists hsrc p.hdr.own r.lists r.srcp hk hpth
  have hc := firsts_charge (oh := oh) W
  have hfl : (Rcpt.Candidates.firstSourceIndices p.lists).length ≤ p.lists.length := by
    simpa only [Rcpt.Candidates.firstSourceIndices, List.length_range] using
      List.length_filter_le (fun j => !Public.sourceDup p.lists j) (List.range p.lists.length)
  unfold dictOf
  rw [he]
  omega

/-! ## The witness -/

theorem tcost (t : Transition) :
    Rcpt.Candidates.transitionPayload t + 4 * Rcpt.Candidates.transitionRecordCount t =
      (t.values.map cost).sum := by
  unfold Rcpt.Candidates.transitionPayload Rcpt.Candidates.transitionRecordCount cost
  induction t.values with
  | nil => rfl
  | cons v vs ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

theorem tscost : ∀ ts : List Transition,
    (ts.map Rcpt.Candidates.transitionPayload).sum + 4 * (ts.map Rcpt.Candidates.transitionRecordCount).sum =
      (ts.map fun t => (t.values.map cost).sum).sum
  | [] => rfl
  | t :: ts => by
    have := tscost ts
    have := tcost t
    simp only [List.map_cons, List.sum_cons]
    omega

/-- The node and value records are within `B0` (A7). -/
theorem records_le_B0 (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    (r.nodes.map fun s => (s.v.ser false).length).sum + (r.values.map ValE.len).sum ≤ 2000000 := by
  have ha := A7Bound.a7_total_le hH T W
  have hN : (r.nodes.map fun s => (s.v.ser false).length).sum ≤ nodeA7Sum r.nodes r.rplN := by
    rw [← range_getD_map default (fun s : NodeS3 => (s.v.ser false).length) r.nodes]
    unfold nodeA7Sum
    apply A9Air.sum_le_sum_range
    intro n _
    split <;> omega
  have hV : (r.values.map ValE.len).sum ≤ valA7Sum r.values r.rplV := by
    rw [← range_getD_map default ValE.len r.values]
    unfold valA7Sum
    apply A9Air.sum_le_sum_range
    intro n _
    split <;> omega
  unfold UnfoldA7.B0 at ha
  omega

/-- **`RestFieldsV3.witnessBytes`** for the reconstruction. -/
theorem witnessBytes_xOf (hp : NearSpecV3.prepD0 cb h = .ok p) {k : WalkD0} (hw : walkD0 cb = .ok k)
    (C : ClaimFieldsV3 k)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r) :
    (V3.encodeSW (stateWitnessOfV3 k (xOf r (dictOf p r)))).length ≤ 8388608 := by
  have hcount := receiptCount_of_records hp W.lists (xOf r (dictOf p r)) rfl
  have hn : h.n = (flatR r.lists).length := by
    rw [hcount]
    simp only [ExtV3.applied, xOf, flatR, List.length_flatMap, List.length_map]
  obtain ⟨block, previous, hmb, hmp⟩ := walkD0_blocks hw
  obtain ⟨m, last, hm, -, hhdr⟩ :=
    RcptLink.executions_holdsP hp hsz hH T W hw hn (x := xOf r (dictOf p r)) rfl rfl rfl rfl hmb hmp
  have hn4 : (flatR r.lists).length ≤ 4481 := hn ▸ hint_n_le hp hw C hm.block hm.previous
  have hKk : p.hdr.K = k.implicitBlks.length := (prepD0_root_endpoints hp hw).2.2
  have hK : p.hdr.K ≤ 32 := by
    have hlt : k.implicitBlks.length < p.sched.length := by
      have hlen : k.implicitBlks.length < (schedulerContexts k m).length := by
        simp [schedulerContexts]
      obtain ⟨sp, hsp, -⟩ := prepD0_context_index_of hp hw hm.block hm.previous _ _
        (List.getElem?_eq_getElem hlen)
      exact (List.getElem?_eq_some_iff.mp hsp).1
    have := Sched.prepD0_len hp
    omega
  -- the witness fields
  have L := trieLink_of hp hsz hH T W
  have hpost : ∀ τ, τ ≤ p.hdr.K → ((xOf r (dictOf p r)).post τ).length = 32 := by
    intro τ hτ
    rw [LinkImplicit.post_xHeads (x := (xOf r (dictOf p r))) rfl (L.chain.ups_mem τ hτ)]
    obtain ⟨hmem, -⟩ := L.chain.ups_mem τ hτ
    obtain ⟨s, -, hs⟩ := List.mem_map.mp hmem
    rw [← hs]
    simp [toB, UpsRows.upsE, UpsRows.regN_len]
  have hil : (stateWitnessOfV3 k (xOf r (dictOf p r))).implicit =
      (List.range p.hdr.K).map fun i => (xOf r (dictOf p r)).transition (i + 1) := by
    rw [hKk]
    exact zipIdx_map_range (fun i => (xOf r (dictOf p r)).transition (i + 1)) k.implicitBlks
  have ht : ∀ t ∈ Rcpt.Candidates.transitions (stateWitnessOfV3 k (xOf r (dictOf p r))),
      t.blockHash.length = 32 ∧ t.postStateRoot.length = 32 := by
    intro t ht
    simp only [Rcpt.Candidates.transitions, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨by simp [stateWitnessOfV3, ExtV3.transition], hpost 0 (Nat.zero_le _)⟩
    · rw [hil] at ht
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      exact ⟨by simp [ExtV3.transition], hpost (i + 1) (by have := List.mem_range.mp hi; omega)⟩
  have he := Rcpt.Candidates.SizeCount.walk_claim_epoch_length hw
  have hcharge := Rcpt.Candidates.witness_encoding_charge (stateWitnessOfV3 k (xOf r (dictOf p r))) he
    (ArenaCore.sha256_length _) ht
  -- stores
  have hpay : Rcpt.Candidates.witnessPayload (stateWitnessOfV3 k (xOf r (dictOf p r))) +
      4 * Rcpt.Candidates.witnessRecordCount (stateWitnessOfV3 k (xOf r (dictOf p r))) =
      ((List.range (p.hdr.K + 1)).map fun τ => (((xOf r (dictOf p r)).store τ).map cost).sum).sum := by
    unfold Rcpt.Candidates.witnessPayload Rcpt.Candidates.witnessRecordCount
    rw [tscost]
    simp only [Rcpt.Candidates.transitions, hil, List.map_cons, List.sum_cons, List.map_map,
      List.range_succ_eq_map, Function.comp_def]
    rfl
  have hst := stores_le hp hsz hH T W (dictOf p r)
  have hB := records_le_B0 hH T W
  have hser : 11 * r.nodes.length ≤ (r.nodes.map fun s => (s.v.ser false).length).sum := by
    have := sum_le_of (f := fun _ => 11) (g := fun s : NodeS3 => (s.v.ser false).length) r.nodes
      (fun s hs => ser_ge (W.nodes.wf s hs))
    rwa [sum_const_gen] at this
  have hvn := vals_le_nodes L.vparent
  have hs1 : (r.nodes.map fun s => (s.v.ser false).length + 4).sum =
      (r.nodes.map fun s => (s.v.ser false).length).sum + 4 * r.nodes.length := by
    rw [sum_add_gen, sum_const_gen]
  have hs2 : (r.values.map fun e => e.len + 4).sum = (r.values.map ValE.len).sum + 4 * r.values.length := by
    rw [sum_add_gen, sum_const_gen]
  -- dictionary, inner, implicit count
  have hd := dict_le (oh := oh) hp hw W hn4
  have hshape := decodeChunkInner_shape_bytes (walkD0_header_decode hw)
  have hinner : (stateWitnessOfV3 k (xOf r (dictOf p r))).innerBytes.length ≤ 302 := by
    show k.c.chunkInner.length ≤ 302
    rw [hshape.2]
    apply inner_len hshape.1
    · simpa using hhdr.proposals
    · simpa using hhdr.bandwidthRequests
    · simpa using hhdr.split
  have himpl : (stateWitnessOfV3 k (xOf r (dictOf p r))).implicit.length = p.hdr.K := by
    rw [stateWitnessOfV3_implicit_length, hKk]
  have hent : (stateWitnessOfV3 k (xOf r (dictOf p r))).entries = (dictOf p r).map DictionaryEntryV3.entry := rfl
  have hd' : (encList V3.encodeEntry (stateWitnessOfV3 k (xOf r (dictOf p r))).entries).length ≤ 3761119 := hd
  rw [hcharge, himpl]
  omega

end LinkWitness

end ZkFormal.NearV3.Assembly
