import ZkFormal.NearV3.Assembly.LinkTrieOk
import ZkFormal.NearV3.Rcpt.Link.RcptHoldsB
import ZkFormal.NearV3.Rcpt.Link.ValBytes

/-!
# ZkFormal.NearV3.Assembly.LinkPostRec — record side of `hpost` (`hrw`) via the `MEM` chain

v1's `Near/Link/Post` (`final_amt`, `valsAt_eq`) over the receipt core's `RecHyp` / `Mem3`:

* `acct_of_slot` — every receipt slot is an acct record's slot (the chain's first read is the
  acct's opening write, `mem_read`);
* `final_amt` — after all receipts the amount of an acct slot is the acct's post amount
  (`mem_final`);
* `valsAt_eq` — a written acct slot's final value is `post ‖ pre[16..]`;
* **`hrw_of`** — the `hrw` premise of `LinkTrieOk.post_of`: a receipt slot `k` is written by a node
  record (`wrote`, `VSLOT`: `acct_written'`) and its final value is `toB (pnOf k)`.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Near.Link

namespace LinkPostRec

open ZkFormal.NearV3 ZkFormal.NearV3.Link3 ZkFormal.NearV3.RcptLink NearSpec ZkFormal.NearV3.Assembly.LinkImplicit

section Hyp
variable {pub : List Fp} {ls : RcptV3Vs} {as : List AcctV} (H : RecHyp pub ls as)
  (base : Nat → NearSpec.Bytes) (T : (Nat → NearSpec.Bytes) → PTrie)
include H

/-- Every receipt slot is the slot of an acct record. -/
theorem acct_of_slot : ∀ r, r < (flatR ls).length → ∃ a ∈ as, a.k = (R (rv ls) r).kslot := by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro hr
    have hr' : r < (rv ls).length := by rwa [rv_length]
    have hm := mem_read H.mem hr' (i := 0) (by decide)
    rcases lastW_cases (ksl (rv ls)) (R (rv ls) r).kslot r with e | ⟨r0, -, -, e⟩
    · obtain ⟨a, ha, hk, -⟩ := hm.1 e
      exact ⟨a, ha, hk⟩
    · obtain ⟨h0, hk, -⟩ := hm.2 r0 e
      obtain ⟨a, ha, hka⟩ := ih r0 h0 (by omega)
      exact ⟨a, ha, hka.trans hk⟩

theorem final_amt {a : AcctV} (ha : a ∈ as) :
    (recModel ls as base T).amtAt a.k (flatR ls).length = leN' a.post := by
  have hl := (acct_len H ha).1
  rw [amt_inv H base T ha _ (Nat.le_refl _)]
  rw [← rv_length]
  rcases lastW_cases (ksl (rv ls)) a.k (rv ls).length with e | ⟨r0, -, -, e⟩
  · rw [e]; simp only [wval, if_true]
    congr 1
    apply ext16 (by simp [hl.1]) hl.2.1
    intro i hi
    have he := (mem_final H.mem ha hi).1 e
    simp only [arMsg, awMsg, acctLane, List.cons_append, List.nil_append, List.cons.injEq] at he
    rw [he.2.2.2.1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
      if_pos hi]
  · rw [e]; simp only [wval, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    obtain ⟨hr0, -, -⟩ := (mem_final H.mem ha (i := 0) (by decide)).2 r0 e
    have hr0' : r0 < (flatR ls).length := by rwa [rv_length] at hr0
    obtain ⟨toks, -, -, hwf, -⟩ := H.wf.toks
    obtain ⟨-, -, -, -, -, -, -, -, l9, -⟩ := (hwf r0 hr0').lens
    have hg : (rv ls).getD r0 default = (flatR ls)[r0].toRcptV := by
      simp [rv, List.getD_eq_getElem?_getD, hr0']
    rw [hg]
    congr 1
    apply ext16 l9 hl.2.1
    intro i hi
    obtain ⟨_, -, he⟩ := (mem_final H.mem ha hi).2 r0 e
    simp only [arMsg, wrMsg, acctLane, List.cons_append, List.nil_append, List.cons.injEq] at he
    have hR : R (rv ls) r0 = (flatR ls)[r0].toRcptV := by
      rw [R_rv]; simp [List.getD_eq_getElem?_getD, hr0']
    rw [hR] at he
    exact he.2.2.2.1.symm

theorem valsAt_eq {a : AcctV} (ha : a ∈ as) (hw : (recModel ls as base T).written a.k = true) :
    (recModel ls as base T).valsAt (flatR ls).length a.k = toBytes (a.post ++ a.pre.drop 16) := by
  have hl := (acct_len H ha).1
  simp only [RunModel.valsAt, hw, ↓reduceIte]
  rw [recModel_acc0 H.mem.knd ha, final_amt H base T ha]
  simp only [accOf, Account.encode, u128, u64]
  rw [leN_leN' hl.2.1, leN_leN' (l := (a.pre.drop 16).take 16) (by simp [hl.1]),
    leN_leN' (l := a.pre.drop 64) (by simp [hl.1])]
  have hsplit : a.pre.drop 16 = (a.pre.drop 16).take 16 ++ ((a.pre.drop 32).take 32 ++ a.pre.drop 64) := by
    have e1 : a.pre.drop 32 = (a.pre.drop 16).drop 16 := by simp [List.drop_drop]
    have e2 : a.pre.drop 64 = ((a.pre.drop 16).drop 16).drop 32 := by simp [List.drop_drop]
    rw [e1, e2, List.take_append_drop, List.take_append_drop]
  conv => rhs; rw [hsplit]
  simp only [toBytes_append, List.append_assoc]

theorem pnOf_eq {a : AcctV} (ha : a ∈ as) : LinkVPost.pnOf as a.k = a.post ++ a.pre.drop 16 := by
  have hnd := H.mem.knd
  unfold LinkVPost.pnOf
  have hf : as.find? (fun b => b.k == a.k) = some a := by
    obtain ⟨b, hb⟩ : ∃ b, as.find? (fun b => b.k == a.k) = some b :=
      Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨a, ha, by simp⟩)
    have hbm := List.mem_of_find?_eq_some hb
    have hbk : b.k = a.k := by simpa using List.find?_some hb
    rw [hb, acct_eq_of_k hnd hbm ha hbk]
  rw [hf]; rfl

end Hyp

section
variable {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
  {tr : Trace Fp} {r : V3Records}

/-- **`hrw`** of `LinkTrieOk.post_of`. -/
theorem hrw_of
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (H : RecHyp (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r.lists r.accts)
    (st : NearSpec.Bytes) :
    ∀ k, (LinkTrieOk.Mdl r st).written k = true → wrote r.nodes k = true ∧
      (LinkTrieOk.Mdl r st).valsAt (LinkTrieOk.Mdl r st).rs.length k = toB (LinkVPost.pnOf r.accts k) := by
  intro k hw
  have hw' := hw
  simp only [RunModel.written, List.any_eq_true, List.mem_range, beq_iff_eq] at hw'
  obtain ⟨i, hi, hik⟩ := hw'
  rw [LinkTrieOk.mdl_len] at hi
  obtain ⟨a, ha, hak⟩ := acct_of_slot H i hi
  have hk : k = a.k := by rw [← hik, hak]; rfl
  subst hk
  refine ⟨?_, ?_⟩
  · obtain ⟨q, hq, l, pre, po, hv⟩ := acct_written' hH T W ha
    unfold wrote
    apply List.any_eq_true.mpr
    exact ⟨r.nodes[q], List.getElem_mem hq, by rw [hv]; simp⟩
  · rw [LinkTrieOk.mdl_len, valsAt_eq H _ _ ha hw, pnOf_eq H ha]
    rfl

/-! ## Slots written by no receipt keep their pre value (`hun`) -/

/-- A written node slot is an acct record's slot (`VSLOT`). -/
theorem acct_of_wrote
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {q : Nat} (hq : q < r.nodes.length) {i l : Nat} {pre po : List Nat}
    (hv : r.nodes[q].v.value = some (i, l, pre, po, true)) (hi : i < P) :
    ∃ a ∈ r.accts, a.k = i := by
  have hm : [i] ∈ ZkFormal.NearV3.nodeRecvs3 r.nodes B_VSLOT := by
    unfold ZkFormal.NearV3.nodeRecvs3
    simp only [show B_VSLOT ≠ B_DIGEST by decide, show B_VSLOT ≠ B_PARENT by decide,
      show B_VSLOT ≠ B_EDGE by decide, show B_VSLOT ≠ ZkFormal.NearV3.B_BMAP by decide,
      show B_VSLOT ≠ ZkFormal.NearV3.B_DUP by decide, show B_VSLOT ≠ ZkFormal.NearV3.B_ENT by decide,
      show B_VSLOT ≠ ZkFormal.NearV3.B_UPB by decide, ite_false, ite_true, List.mem_flatMap]
    refine ⟨(r.nodes[q], q), ?_, by simp [hv]⟩
    have hz : q < (r.nodes.zip (List.range r.nodes.length)).length := by simpa using hq
    have := List.getElem_mem hz
    simpa using this
  have hc : 0 < ((ZkFormal.NearV3.nodeRecvs3 r.nodes B_VSLOT).map Msg.toFp).count (Msg.toFp [i]) :=
    List.count_pos_iff.mpr (List.mem_map_of_mem hm)
  rw [← vslot_bal hH T] at hc
  obtain ⟨m, hm', he⟩ := List.mem_map.mp (List.count_pos_iff.mp hc)
  simp only [ZkFormal.NearV3.acctV3Sends, show B_VSLOT ≠ B_VBYTES by decide,
    show B_VSLOT ≠ B_BYTES by decide, show B_VSLOT ≠ B_MEM by decide, ite_false, ite_true,
    List.mem_map] at hm'
  obtain ⟨a, ha, rfl⟩ := hm'
  have hk := (LinkVPost.acct_wf W ha).2.2.1
  simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
  exact ⟨a, ha, Link.ofNat_inj hk hi he⟩

theorem wrote_slot {vs : List NodeS3} {i : Nat} (h : wrote vs i = true) :
    ∃ q, ∃ hq : q < vs.length, ∃ l pre po, vs[q].v.value = some (i, l, pre, po, true) := by
  unfold wrote at h
  obtain ⟨s, hs, hsv⟩ := List.any_eq_true.mp h
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hs
  cases hx : vs[q].v.value with
  | none => rw [hx] at hsv; simp at hsv
  | some x =>
    obtain ⟨j, l, pre, po, w⟩ := x
    rw [hx] at hsv
    simp only [Bool.and_eq_true, beq_iff_eq] at hsv
    obtain ⟨rfl, rfl⟩ := hsv
    exact ⟨q, hq, l, pre, po, hx⟩

/-- **`hun`** (any instance): a value record whose slot is written by a node record but by no
receipt has post encoding `pnOf = pre`, equal to its bytes. -/
theorem post_eq_pre (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (H : RecHyp (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r.lists r.accts)
    {e : ValE} (he : e ∈ r.values) (hwr : wrote r.nodes e.vid = true)
    (hno : ∀ i, i < (flatR r.lists).length → (R (rv r.lists) i).kslot ≠ e.vid) :
    toB (LinkVPost.pnOf r.accts e.vid) = toB e.bytes := by
  have L := trieLink_of hp hsz hH T W
  -- the writing node slot
  obtain ⟨q, hq, l, pre, po, hval⟩ := wrote_slot hwr
  have hvidP : e.vid < P := (W.values.canon e he).1
  obtain ⟨a, ha, hak⟩ := acct_of_wrote hH T W hq hval hvidP
  -- no receipt touched the slot: the final read is the opening write
  have hl0 : lastW (ksl (rv r.lists)) a.k (rv r.lists).length = 0 := by
    rcases lastW_cases (ksl (rv r.lists)) a.k (rv r.lists).length with e0 | ⟨r0, hr0, hk0, -⟩
    · exact e0
    · exact absurd (hk0.trans hak) (hno r0 (by rwa [rv_length] at hr0))
  have hpost : a.post = a.pre.take 16 := by
    have hl := (acct_len H ha).1
    apply List.ext_getElem (by simp [hl.1, hl.2.1])
    intro i h1 h2
    have he' := (mem_final H.mem ha (i := i) (by rw [hl.2.1] at h1; exact h1)).1 hl0
    simp only [arMsg, awMsg, acctLane, List.cons_append, List.nil_append, List.cons.injEq] at he'
    have := he'.2.2.2.1
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem (by simp at h2; omega)] at this
    simpa using this
  have hpn : LinkVPost.pnOf r.accts e.vid = a.pre := by
    rw [← hak, pnOf_eq H ha, hpost, List.take_append_drop]
  rw [hpn]
  -- lengths: the slot's post value has `|pnOf| = 72 = l`, and the record has `len = l`
  have hl := (acct_len H ha).1
  have hvb := vparentBal_of hH T
  have HP := LinkVPost.vpostOk_holds hp hsz hH T W
  obtain ⟨hlen, -, -⟩ := vpost_len W.nodes W.values hvb L.sha HP hq hval
    (LinkVPost.hvpostLen_of hH T W q hq _ _ _ _ hval)
  rw [← hak, LinkVPost.pnOf_eq hH T W ha] at hlen
  simp only [toB, List.length_map, List.length_append, List.length_drop, hl.1, hl.2.1] at hlen
  obtain ⟨t, ht, -, hvt, hlt, -⟩ := val_pos W.nodes W.values hvb (vlen_le W.values) hq hval
  obtain ⟨t', ht', rfl⟩ := List.getElem_of_mem he
  have htt : t' = t := by
    rw [← vid_small W.values ht', ← vid_small W.values ht, hvt]
  subst htt
  have hbl : r.values[t'].bytes.length = 72 := by
    have hsh := W.values.shape _ (List.getElem_mem ht')
    cases hz : r.values[t'].vz
    · rw [(hsh.2 hz).1, hlt]; omega
    · have := (hsh.1 hz).1; omega
  -- bytes: `VBYTES` (`acct_pre_byte`)
  congr 1
  apply List.ext_getElem (by rw [hl.1, hbl])
  intro j h1 h2
  obtain ⟨u, hu, huv, hb⟩ := acct_pre_byte hH T W ha (j := j) (by rw [hl.1] at h1; exact h1)
  have hut : u = t' := by
    rw [← vid_small W.values hu, ← vid_small W.values ht', huv, hak]
  subst hut
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2] at hb
  simpa using hb

/-- **`hun`** of `LinkTrieOk.post_of`. -/
theorem hun_of (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (H : RecHyp (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r.lists r.accts)
    (st : NearSpec.Bytes) :
    ∀ e ∈ r.values, valTau r.nodes e.vid = 0 → wrote r.nodes e.vid = true →
      (LinkTrieOk.Mdl r st).written e.vid = false →
        toB (LinkVPost.pnOf r.accts e.vid) = toB e.bytes := by
  intro e he _ hwr hw
  apply post_eq_pre hp hsz hH T W H he hwr
  intro i hi hk
  have : (LinkTrieOk.Mdl r st).written e.vid = true := by
    simp only [RunModel.written, List.any_eq_true, List.mem_range, beq_iff_eq]
    exact ⟨i, by rw [LinkTrieOk.mdl_len]; exact hi, hk⟩
  rw [hw] at this; cases this

/-- **`PostPreOff0`**, given that every receipt slot is a value of instance `0`. -/
theorem postPreOff0_of (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (H : RecHyp (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r.lists r.accts)
    (hslot0 : ∀ i, i < (flatR r.lists).length → valTau r.nodes (R (rv r.lists) i).kslot = 0) :
    LinkImplicit.PostPreOff0 r := by
  intro e he h0 hwr
  apply post_eq_pre hp hsz hH T W H he hwr
  intro i hi hk
  exact h0 (by rw [← hk]; exact hslot0 i hi)

/-- A lookup from a node of an invariant node set (closed under children) ends at a value of a
node of that set. -/
theorem reach_inv {ns : List NodeRec3} (Q : Nat → Prop)
    (hQ : ∀ n nr, ns[n]? = some nr → Q n → ∀ c, Kid3.node c ∈ nr.node.kids → Q c) {j : Nat} :
    ∀ (f n : Nat) (key : List Nat), Q n → vreach3 ns f n key = some j →
      ∃ m : Nat, ∃ nr : NodeRec3, ns[m]? = some nr ∧ Q m ∧ j ∈ nr.node.vids := by
  intro f
  induction f with
  | zero => intro n key _ h; simp [vreach3] at h
  | succ f ih =>
    intro n key hn0 h
    simp only [vreach3] at h
    cases hn : ns[n]? with
    | none => rw [hn] at h; simp at h
    | some nr =>
      rw [hn] at h; simp only at h
      have hk := hQ n nr hn hn0
      generalize hr : nr.node = r at h hk
      cases r with
      | leaf k s m =>
        cases s with
        | ref => simp [recReach] at h
        | val j' =>
          simp only [recReach] at h; split at h <;> simp at h; subst h
          exact ⟨n, nr, hn, hn0, by rw [hr]; simp [Rec3.vids]⟩
      | ext k kid m =>
        cases kid with
        | node c =>
          simp only [recReach] at h; split at h
          · exact ih c _ (hk c (by simp [Rec3.kids])) h
          · simp at h
        | none => simp [recReach] at h
        | hash _ => simp [recReach] at h
      | branch sv kids m =>
        cases key with
        | nil =>
          cases sv with
          | none => simp [recReach] at h
          | some s =>
            cases s with
            | ref => simp [recReach] at h
            | val j' =>
              simp [recReach] at h; subst h
              exact ⟨n, nr, hn, hn0, by rw [hr]; simp [Rec3.vids]⟩
        | cons j0 rest =>
          simp only [recReach] at h
          split at h
          · rename_i c hc
            exact ih c rest (hk c (by simp only [Rec3.kids]; exact List.mem_of_getElem? hc)) h
          · simp at h

/-- **A receipt slot is a value of instance `0`.** -/
theorem slot_tau0 (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ∀ i, i < (flatR r.lists).length → valTau r.nodes (R (rv r.lists) i).kslot = 0 := by
  intro i hi
  have L := trieLink_of hp hsz hH T W
  have hd := LinkTrieFam.dag_v W L (Nat.zero_le _) (v := LinkTrieFam.preV r) (fun _ => rfl)
  obtain ⟨hr, hlt, hid⟩ := LinkRcptWalk.rcpt_reach hp hsz hH T W hi
  obtain ⟨m, nr, hm, hQ, hj⟩ := reach_inv (ns := UpsRows.Rpost r.nodes r.values)
    (fun n => InInst (UpsRows.Rpost r.nodes r.values) 0 n)
    (fun n nr hn hq c hc => by
      obtain ⟨nr', hn', ht⟩ := hq
      rw [hn] at hn'; cases hn'
      exact (hd.child n nr hn ht c hc).2) _ _ _ hd.root_inst hr
  obtain ⟨nr', hn', ht⟩ := hQ
  rw [hm] at hn'; cases hn'
  obtain ⟨vr, hvr, hvt⟩ := hd.vals m nr hm ht _ hj
  simp only [LinkTrieFam.valsBy, List.getElem?_map, List.getElem?_eq_getElem hlt, Option.map_some,
    Option.some.injEq] at hvr
  subst hvr
  have hR : (R (rv r.lists) i).kslot = (flatR r.lists)[i].kslot := by
    rw [R_rv]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, RcptE.toRcptV]
  rw [hR, ← hid]
  exact hvt

/-- `RecHyp` from `HoldsP` (`RcptLink.recHyp_of` under the trie link's `ShaHyp`). -/
theorem recHyp_holds (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    RecHyp (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r.lists r.accts :=
  recHyp_of hp hsz hH T W (shaHyp_holds hp hsz hH T W)

/-- **`PostPreOff0`** from `HoldsP`. -/
theorem postPreOff0_holds (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    LinkImplicit.PostPreOff0 r :=
  postPreOff0_of hp hsz hH T W (recHyp_holds hp hsz hH T W) (slot_tau0 hp hsz hH T W)

/-- **An acct record's pre bytes are its value record's bytes** (72 of them: the written slot's
post window has the acct's 72-byte post stream, `vpost_len`, and the record's length is the
slot's, `val_pos`; bytes by `VBYTES`, `acct_pre_byte`). -/
theorem acct_pre_eq (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (H : RecHyp (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r.lists r.accts)
    {a : AcctV} (ha : a ∈ r.accts) :
    ∃ t, ∃ ht : t < r.values.length, r.values[t].vid = a.k ∧ toB a.pre = toB r.values[t].bytes := by
  have L := trieLink_of hp hsz hH T W
  obtain ⟨q, hq, l, pre, po, hval⟩ := acct_written' hH T W ha
  have hl := (acct_len H ha).1
  have hvb := vparentBal_of hH T
  have HP := LinkVPost.vpostOk_holds hp hsz hH T W
  obtain ⟨hlen, -, -⟩ := vpost_len W.nodes W.values hvb L.sha HP hq hval
    (LinkVPost.hvpostLen_of hH T W q hq _ _ _ _ hval)
  rw [LinkVPost.pnOf_eq hH T W ha] at hlen
  simp only [toB, List.length_map, List.length_append, List.length_drop, hl.1, hl.2.1] at hlen
  obtain ⟨t, ht, -, hvt, hlt, -⟩ := val_pos W.nodes W.values hvb (vlen_le W.values) hq hval
  refine ⟨t, ht, hvt, ?_⟩
  have hbl : r.values[t].bytes.length = 72 := by
    have hsh := W.values.shape _ (List.getElem_mem ht)
    cases hz : r.values[t].vz
    · rw [(hsh.2 hz).1, hlt]; omega
    · have := (hsh.1 hz).1; omega
  congr 1
  apply List.ext_getElem (by rw [hl.1, hbl])
  intro j h1 h2
  obtain ⟨u, hu, huv, hb⟩ := acct_pre_byte hH T W ha (j := j) (by rw [hl.1] at h1; exact h1)
  have hut : u = t := by
    rw [← vid_small W.values hu, ← vid_small W.values ht, huv, hvt]
  subst hut
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2] at hb
  simpa using hb

/-- **`hinit`** of `LinkTrieOk` (the receipt slots' initial values are the pre values). -/
theorem hinit_holds (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (st : NearSpec.Bytes) :
    ∀ k, (LinkTrieOk.Mdl r st).valsAt 0 k = LinkTrieFam.preV r k := by
  have H := recHyp_holds hp hsz hH T W
  apply LinkTrieOk.hinit_of
  intro k hw
  have hw' := hw
  simp only [RunModel.written, List.any_eq_true, List.mem_range, beq_iff_eq] at hw'
  obtain ⟨i, hi, hik⟩ := hw'
  rw [LinkTrieOk.mdl_len] at hi
  obtain ⟨a, ha, hak⟩ := acct_of_slot H i hi
  have hk : k = a.k := by rw [← hik, hak]; rfl
  subst hk
  obtain ⟨t, ht, hvt, hbt⟩ := acct_pre_eq hp hsz hH T W H ha
  rw [← hvt, LinkTrieFam.preV_at W ht, ← hbt, hvt]
  have hl := (acct_len H ha).1
  simp only [RunModel.valsAt, hw, ↓reduceIte, RunModel.amtAt]
  rw [recModel_acc0 H.mem.knd ha]
  simp only [accOf, Account.encode, u128, u64]
  rw [leN_leN' (l := a.pre.take 16) (by simp [hl.1]),
    leN_leN' (l := (a.pre.drop 16).take 16) (by simp [hl.1]),
    leN_leN' (l := a.pre.drop 64) (by simp [hl.1])]
  have hsplit : a.pre = a.pre.take 16 ++ ((a.pre.drop 16).take 16 ++ ((a.pre.drop 32).take 32 ++ a.pre.drop 64)) := by
    have e1 : a.pre.drop 32 = (a.pre.drop 16).drop 16 := by simp [List.drop_drop]
    have e2 : a.pre.drop 64 = ((a.pre.drop 16).drop 16).drop 32 := by simp [List.drop_drop]
    rw [e1, e2, List.take_append_drop, List.take_append_drop, List.take_append_drop]
  conv => rhs; rw [hsplit]
  simp only [toBytes_append, toB, toBytes, List.map_append, List.append_assoc]

/-- **`hpost`** for the receipt core's final trie, from `HoldsP`. -/
theorem post_holds (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {x : ExtV3} (hxh : x.heads = xHeads (r.ups.map UpsRows.upsE))
    (h0 : 0 < p.sched.length) {o : NearSpecV3.Scheduler.Output}
    (ho : NearSpecV3.Scheduler.runCore p.sched[0] (Sched.prevOf tr T_CODEC 0) = some o) :
    ((LinkTrieOk.Mdl r (schedOut o).state).T
      ((LinkTrieOk.Mdl r (schedOut o).state).valsAt (LinkTrieOk.Mdl r (schedOut o).state).rs.length)).hashOf =
        x.post 0 := by
  have H := recHyp_holds hp hsz hH T W
  exact LinkTrieOk.post_of hp hsz hH T W hxh h0 ho (hinit_holds hp hsz hH T W _)
    (hrw_of hH T W H _) (hun_of hp hsz hH T W H _)

end

end LinkPostRec

end ZkFormal.NearV3.Assembly
