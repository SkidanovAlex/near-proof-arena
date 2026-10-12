import ZkFormal.Near.Link.OutMain
import ZkFormal.Near.Link.ShaCore
import ZkFormal.NearV3.Assembly.LinkShaKinds

/-!
# ZkFormal.NearV3.Rcpt.Link.OutCore3 — the outcome root from an abstract Merkle view (v3)

v1's `Link.out_ok`, abstracted from v1's `LinkHyp`: `OutCore S shaS shaR pub mv Rs n L` collects

* the SHA facts with the `BYTES` receives covered by the sender list `S`, and the `DIGEST`
  receives of the mrk view provided;
* the exact `MPOS` balance: the leaf sends `Rs` (each `[0, q, LEAF(q), 68]`, `q < n`) and the mrk
  sends against the mrk receives;
* the mrk view's well-formedness at `n` leaves (`mv.n = n ≤ 2^22`);
* for every leaf `q < n`, a 68-byte message isolated in `S` under `LEAF(q)` hashing to `L[q]`;
* the isolation of every hashed node's message under `MRK(i)`.

**`root_of_core`**: the root digest received by the mrk view is `merkleRoot L`.
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Link NearSpec

set_option linter.unusedSimpArgs false

/-- The `sha_core` isolation hypothesis for message id `Id` with message `enc`. -/
def Iso (S : List Msg) (Id : Nat) (enc : List Nat) : Prop :=
  ∀ m ∈ S, ∀ a, m.head? = some a → Fp.ofNat a = Fp.ofNat Id →
    ∃ k, k < enc.length ∧ m = [Id, k, enc.getD k 0]

structure OutCore (S : List Msg) (shaS shaR : Nat → List Fp → Nat) (pub : List Fp) (mv : MrkV)
    (Rs : List Msg) (n : Nat) (L : List Bytes) : Prop where
  hsha : ShaFacts shaS shaR
  hbytes : ∀ m, shaR B_BYTES m = cnt S m
  dig : ∀ m ∈ mrkRecvs pub mv B_DIGEST, 0 < shaS B_DIGEST m.toFp
  bal : ∀ m : List Fp, cnt Rs m + cnt (mrkSends pub mv B_MPOS) m = cnt (mrkRecvs pub mv B_MPOS) m
  rs : ∀ m ∈ Rs, ∃ q, q < n ∧ m = [0, q, msgId K_LEAF q, 68]
  wf : MrkWf pub mv
  nv : mv.n = n
  nle : n ≤ 2 ^ 22
  leaf : ∀ q, q < n → ∃ enc : List Nat, enc.length = 68 ∧ (∀ x ∈ enc, x < P) ∧
    Iso S (msgId K_LEAF q) enc ∧ sha256 (toBytes enc) = L.getD q []
  mrk : ∀ i enc, (mrkMsgs mv)[i]? = some enc → Iso S (msgId K_MRK i) enc
  len : L.length = n

theorem cnt_app (a b : List Msg) (m : List Fp) : cnt (a ++ b) m = cnt a m + cnt b m := by
  unfold cnt; simp [List.map_append, List.count_append]

section Core
variable {S : List Msg} {shaS shaR : Nat → List Fp → Nat} {pub : List Fp} {mv : MrkV}
  {Rs : List Msg} {n : Nat} {L : List Bytes} (C : OutCore S shaS shaR pub mv Rs n L)
include C

theorem core_npos : 1 ≤ n := C.nv ▸ C.wf.npos

theorem core_nodes_le : mv.nodes.length ≤ 2 ^ 23 := by
  rw [C.wf.shape.1]
  have := ZkFormal.NearV3.Assembly.mrkLevels_length2 (mv.n + 1) 1 mv.n
  have := C.nle
  have := C.nv
  unfold mrkShape; omega

/-- Position facts of mrk node `q`. -/
theorem core_node_pos {q : Nat} (hq : q < mv.nodes.length) :
    ∃ d, (mrkPos mv q).1 = 1 + d ∧ (mrkPos mv q).2 < sz n (d + 1) ∧
      kindOf mv.nodes[q] = decide (2 * (mrkPos mv q).2 + 1 < sz n d) ∧
      ∀ d', d' < d → sz n (d' + 1) ≠ 1 := by
  obtain ⟨hlen, hkind⟩ := C.wf.shape
  have hS : q < (mrkShape mv.n).length := by rw [← hlen]; exact hq
  have hmem : (mrkShape mv.n)[q] ∈ mrkShape mv.n := List.getElem_mem hS
  have hget : (mrkShape mv.n).getD q (0, 0, false) = (mrkShape mv.n)[q] := getD_eq_getElem _ _ hS
  have hk := hkind q hq
  rw [hget] at hk
  generalize (mrkShape mv.n)[q] = e at hmem hget hk
  obtain ⟨d, h1, h2, h3, h4⟩ := levels_mem _ _ _ _ _ _ (show (e.1, e.2.1, e.2.2) ∈
    mrkLevels (mv.n + 1) 1 mv.n from hmem)
  rw [C.nv] at h2 h3 h4
  have hp : mrkPos mv q = (e.1, e.2.1) := by unfold mrkPos; rw [hget]
  refine ⟨d, by rw [hp]; exact h1, by rw [hp]; exact h2, ?_, h4⟩
  rw [hp]; dsimp only
  rw [← h3, ← hk]
  unfold kindOf; rfl

theorem core_send_canon {q : Nat} (hq : q < mv.nodes.length) : Canon (mrkSend mv mv.nodes[q] q) := by
  have hml := core_nodes_le C
  have hn1 := core_npos C
  have hnle := C.nle
  obtain ⟨d, h1, h2, -, h4⟩ := core_node_pos C hq
  have hd := depth_le n hn1 d h4
  have hs := sz_le n (d + 1)
  have hb := hashedBefore_le mv.nodes q
  have hcan := C.wf.canon.2.2.2 _ (List.getElem_mem hq)
  intro x hx
  unfold mrkSend at hx
  split at hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [h1]; unfold P; omega
    · unfold P; omega
    · unfold msgId K_MRK P; omega
    · unfold P; omega
  · next cId cLen he =>
    rw [he] at hcan
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [h1]; unfold P; omega
    · unfold P; omega
    · exact hcan _ (by simp [MrkNode.raw])
    · exact hcan _ (by simp [MrkNode.raw])

theorem core_sends_canon : ∀ m ∈ Rs ++ mrkSends pub mv B_MPOS, Canon m := by
  have hnle := C.nle
  intro m hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨q, hq, rfl⟩ := C.rs m hm
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> (unfold msgId K_LEAF P at *; omega)
  · rw [mrkSends_mpos] at hm
    obtain ⟨⟨nd, q⟩, hp, rfl⟩ := List.mem_map.mp hm
    obtain ⟨hq, rfl⟩ := mem_zip_range.mp hp
    exact core_send_canon C hq

theorem core_kids_canon {q : Nat} (hq : q < mv.nodes.length) :
    ∀ m ∈ mrkKids mv mv.nodes[q] q, Canon m := by
  have hsc := core_send_canon C hq
  have hcan := C.wf.canon.2.2.2 _ (List.getElem_mem hq)
  have hpos : (mrkPos mv q).1 < P ∧ (mrkPos mv q).2 < P := by
    unfold mrkSend at hsc
    split at hsc <;> exact ⟨hsc _ (by simp), hsc _ (by simp)⟩
  have hn1 := core_npos C
  have hnle := C.nle
  obtain ⟨d, h1, h2, -, h4⟩ := core_node_pos C hq
  have hs := sz_le n (d + 1)
  intro m hm x hx
  unfold mrkKids at hm
  split at hm
  · next lI lL l rI rL r he =>
    rw [show mv.nodes[q] = _ from he] at hcan
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
      rcases hx with rfl | rfl | rfl | rfl <;>
      first | (unfold P at *; omega) | exact hcan _ (by simp [MrkNode.raw])
  · next cId cLen he =>
    rw [show mv.nodes[q] = _ from he] at hcan
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      first | (unfold P at *; omega) | exact hcan _ (by simp [MrkNode.raw])

/-- A received `MPOS` message (canonical) is sent. -/
theorem core_recv_sent {m : Msg} (hm : m ∈ mrkRecvs pub mv B_MPOS) (hc : Canon m) :
    m ∈ Rs ++ mrkSends pub mv B_MPOS := by
  have h1 := cnt_pos_of_mem hm
  rw [← C.bal, ← cnt_app] at h1
  obtain ⟨y, hy, he⟩ := cnt_pos.mp h1
  rwa [← toFp_inj (core_sends_canon C y hy) hc he]

/-- What an `MPOS` send at `(j, i)` guarantees. -/
def MGood3 (S : List Msg) (n : Nat) (L : List Bytes) (m : Msg) : Prop :=
  ∃ j i Id enc, m = [j, i, Id, enc.length] ∧ Id < P ∧ (∀ x ∈ enc, x < P) ∧ enc.length < P ∧
    Iso S Id enc ∧ i < sz n j ∧ sha256 (toBytes enc) = (lvl L j).getD i []

/-- A consumed digest window of a good child is its hash. -/
theorem core_win {d k Id len : Nat} {w : List Nat} (hg : MGood3 S n L [d, k, Id, len])
    (hw : ∀ x ∈ w, x < P) (hd : 0 < shaS B_DIGEST (digMsg Id len w).toFp) :
    toBytes w = (lvl L d).getD k [] := by
  obtain ⟨_, _, _, enc, he, e1, e2, e3, e4, -, e5⟩ := hg
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨rfl, rfl, rfl, rfl⟩ := he
  have := (sha_core C.hsha S C.hbytes e1 e2 e3 hw e4 hd).2
  rw [this, toBytes_map_toNat', e5]

theorem core_sends_good : ∀ j, ∀ m ∈ Rs ++ mrkSends pub mv B_MPOS, m.head? = some j → MGood3 S n L m := by
  have hnle := C.nle
  have hn1 := core_npos C
  intro j
  induction j with
  | zero =>
    intro m hm hj
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨q, hq, rfl⟩ := C.rs m hm
      obtain ⟨enc, hl, hc, hi, hs⟩ := C.leaf q hq
      refine ⟨0, q, _, enc, by rw [hl], by unfold msgId K_LEAF P; omega, hc,
        by rw [hl]; unfold P; omega, hi, by simpa [sz] using hq, ?_⟩
      rw [hs]; rfl
    · rw [mrkSends_mpos] at hm
      obtain ⟨⟨nd, q⟩, hp, rfl⟩ := List.mem_map.mp hm
      obtain ⟨hq, rfl⟩ := mem_zip_range.mp hp
      obtain ⟨d, h1, -⟩ := core_node_pos C hq
      unfold mrkSend at hj; split at hj <;> simp [h1] at hj
  | succ j ih =>
    intro m hm hj
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨q, -, rfl⟩ := C.rs m hm
      simp at hj
    rw [mrkSends_mpos] at hm
    obtain ⟨⟨nd0, q⟩, hp, rfl⟩ := List.mem_map.mp hm
    obtain ⟨hq, rfl⟩ := mem_zip_range.mp hp
    obtain ⟨d, h1, h2, h3, h4⟩ := core_node_pos C hq
    have hdj : d = j := by unfold mrkSend at hj; split at hj <;> simp [h1] at hj <;> omega
    subst hdj
    have hsc := core_send_canon C hq
    have hlj : (lvl L d).length = sz n d := by rw [lvl_length, C.len]
    -- the child at (d, k) is good
    have kid_good : ∀ k Id len, [(mrkPos mv q).1 - 1, k, Id, len] ∈ mrkKids mv mv.nodes[q] q →
        MGood3 S n L [d, k, Id, len] := by
      intro k Id len hk
      have hR : [(mrkPos mv q).1 - 1, k, Id, len] ∈ mrkRecvs pub mv B_MPOS := by
        rw [mrkRecvs_mpos]
        exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨(mv.nodes[q], q), mem_zip_range.mpr ⟨hq, rfl⟩, hk⟩)
      have hW := core_recv_sent C hR (core_kids_canon C hq _ hk)
      rw [h1, show 1 + d - 1 = d from by omega] at hW
      exact ih _ hW rfl
    have hmd : ∀ m', m' ∈ (match mv.nodes[q] with
        | .hashed lI lL l rI rL r => [digMsg lI lL l, digMsg rI rL r]
        | _ => []) → 0 < shaS B_DIGEST m'.toFp := by
      intro m' hm'
      apply C.dig
      unfold mrkRecvs; dsimp only; rw [if_pos rfl]
      exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨(mv.nodes[q], q), mem_zip_range.mpr ⟨hq, rfl⟩, hm'⟩)
    have hgetL := merkleLevel_get (lvl L d) (mrkPos mv q).2
      (by rw [hlj]; simpa [sz] using h2)
    rw [hlj] at hgetL
    have hcanq := C.wf.canon.2.2.2 _ (List.getElem_mem hq)
    generalize hnd : mv.nodes[q] = nd at h3 hmd kid_good hsc hcanq ⊢
    cases nd with
    | hashed lI lL l rI rL r =>
      have hw := C.wf.windows _ (List.getElem_mem hq)
      rw [hnd] at hw
      have hk1 := kid_good (2 * (mrkPos mv q).2) lI lL (by simp [mrkKids])
      have hk2 := kid_good (2 * (mrkPos mv q).2 + 1) rI rL (by simp [mrkKids])
      have t1 := core_win C hk1 (w := l) (fun x hx => hcanq x (by simp [MrkNode.raw, hx])) (hmd _ (by simp))
      have t2 := core_win C hk2 (w := r) (fun x hx => hcanq x (by simp [MrkNode.raw, hx])) (hmd _ (by simp))
      have hmsg := mrkMsgs_at mv q hq hnd
      have hlt : 2 * (mrkPos mv q).2 + 1 < sz n d := by
        simp only [kindOf] at h3; exact of_decide_eq_true h3.symm
      have hb := hashedBefore_le mv.nodes q
      have hml := core_nodes_le C
      refine ⟨d + 1, (mrkPos mv q).2, _, l ++ r, ?_, by unfold msgId K_MRK P; omega,
        fun x hx => hcanq x (by rcases List.mem_append.mp hx with hx | hx <;> simp [MrkNode.raw, hx]),
        by simp [hw.1, hw.2]; unfold P; omega, C.mrk _ _ hmsg, h2, ?_⟩
      · simp only [mrkSend, h1, Nat.add_comm, List.length_append, hw.1, hw.2]
      · rw [toBytes_append, t1, t2]
        simp only [lvl]
        rw [hgetL, if_pos hlt]
    | promoted cId cLen =>
      have hk := kid_good (2 * (mrkPos mv q).2) cId cLen (by simp [mrkKids])
      obtain ⟨_, _, _, enc, he, e1, e2, e3, e4, -, e5⟩ := hk
      simp only [List.cons.injEq, and_true] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      have hnlt : ¬ (2 * (mrkPos mv q).2 + 1 < sz n d) := by
        simp only [kindOf] at h3; exact of_decide_eq_false h3.symm
      refine ⟨d + 1, (mrkPos mv q).2, _, enc, ?_, e1, e2, e3, e4, h2, ?_⟩
      · simp only [mrkSend, h1, Nat.add_comm]
      · rw [e5]; simp only [lvl]; rw [hgetL, if_neg hnlt]

/-- **The root digest the mrk view receives is `merkleRoot L`.** -/
theorem root_of_core :
    toBytes ((List.range 32).map fun j => pubNat pub (PV_OUT + j)) = merkleRoot L := by
  have hn1 := core_npos C
  have hL1 : 1 ≤ L.length := by rw [C.len]; exact hn1
  -- the top level
  obtain ⟨Jt, hJ1, hJn, hJ, hmin⟩ := exists_first (sz n) 1 1 n hn1 (sz_n_n _ hn1)
  obtain ⟨b, hb⟩ := levels_complete (n + 1) 1 n (Jt - 1) (by omega)
    (fun d' hd' => hmin (d' + 1) (by omega) (by omega)) 0
    (by rw [show Jt - 1 + 1 = Jt from by omega, hJ]; decide)
  rw [show 1 + (Jt - 1) = Jt from by omega, ← C.nv] at hb
  obtain ⟨hlen, -⟩ := C.wf.shape
  obtain ⟨q, hqS, hqe⟩ := List.mem_iff_getElem.mp (show (Jt, 0, b) ∈ mrkShape mv.n from hb)
  have hq : q < mv.nodes.length := by rw [hlen]; exact hqS
  have hpos : mrkPos mv q = (Jt, 0) := by
    unfold mrkPos; rw [getD_eq_getElem _ _ hqS, hqe]
  -- its send is received: the root reference
  have hmW : mrkSend mv mv.nodes[q] q ∈ Rs ++ mrkSends pub mv B_MPOS := by
    apply List.mem_append_right
    rw [mrkSends_mpos]
    exact List.mem_map.mpr ⟨(mv.nodes[q], q), mem_zip_range.mpr ⟨hq, rfl⟩, rfl⟩
  have hmR : mrkSend mv mv.nodes[q] q ∈ mrkRecvs pub mv B_MPOS := by
    have h1 := cnt_pos_of_mem hmW
    rw [cnt_app, C.bal] at h1
    obtain ⟨y, hy, he⟩ := cnt_pos.mp h1
    have hyc : Canon y := by
      rw [mrkRecvs_mpos] at hy
      rcases List.mem_cons.mp hy with rfl | hk
      · obtain ⟨c1, c2, c3, -⟩ := C.wf.canon
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact c1
        · unfold P; omega
        · exact c2
        · exact c3
      · obtain ⟨⟨nd, q'⟩, hp, hk⟩ := List.mem_flatMap.mp hk
        obtain ⟨hq', rfl⟩ := mem_zip_range.mp hp
        exact core_kids_canon C hq' _ hk
    rwa [toFp_inj hyc (core_send_canon C hq) he] at hy
  rw [mrkRecvs_mpos] at hmR
  have hroot : mrkSend mv mv.nodes[q] q = [mv.J, 0, mv.rootId, mv.rootLen] := by
    rcases List.mem_cons.mp hmR with he | hk
    · exact he
    · exfalso
      obtain ⟨⟨nd, q'⟩, hp, hk⟩ := List.mem_flatMap.mp hk
      obtain ⟨hq', rfl⟩ := mem_zip_range.mp hp
      obtain ⟨d', e1, -, -, e4⟩ := core_node_pos C hq'
      have hhead : (mrkSend mv mv.nodes[q] q).head? = some Jt := by
        unfold mrkSend; split <;> simp [hpos]
      have hkh : ∀ k ∈ mrkKids mv mv.nodes[q'] q', k.head? = some ((mrkPos mv q').1 - 1) := by
        intro k hk'
        unfold mrkKids at hk'; split at hk' <;> simp at hk' <;>
          first | (rcases hk' with rfl | rfl <;> rfl) | (subst hk'; rfl)
      have : (mrkPos mv q').1 - 1 = Jt := by
        have := hkh _ hk; rw [hhead] at this; simpa using this.symm
      rw [e1] at this
      exact e4 (Jt - 1) (by omega) (by rw [show Jt - 1 + 1 = Jt from by omega]; exact hJ)
  have hJJ : mv.J = Jt := by
    have e := congrArg List.head? hroot
    have hh : (mrkSend mv mv.nodes[q] q).head? = some Jt := by unfold mrkSend; split <;> simp [hpos]
    rw [hh] at e; simp at e; exact e.symm
  -- the root digest
  have hg := core_sends_good C Jt _ hmW (by unfold mrkSend; split <;> simp [hpos])
  rw [hroot, hJJ] at hg
  have hd : 0 < shaS B_DIGEST (digMsg mv.rootId mv.rootLen
      ((List.range 32).map fun j => pubNat pub (PV_OUT + j))).toFp := by
    apply C.dig
    unfold mrkRecvs; dsimp only; rw [if_pos rfl]; exact List.mem_cons_self
  have hw := core_win C hg (fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx; exact Fp.toNat_lt _) hd
  rw [hw, merkleRoot_eq _ hL1 Jt (by rw [C.len]; exact hJ)]

end Core

end ZkFormal.NearV3.RcptLink
