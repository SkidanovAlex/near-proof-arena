import ZkFormal.NearV3.D1.Link.RfBody

/-!
# `ZkFormal.NearV3.D1.Link.TxOps` — the `txV3` ops are the public ops, once each (L1)

Lane `v3-d1-phase2`, item L1 (the run, next step 5 of checkpoint 10).  `txV3` has no op counter:
an op's index `op` is a free column, tied to the public `TXP`/`SIG` records.  The `SIG` bus has
the public `SIG` segment (one record `(o, valid_o)` per op `o < T0`) as its only sender and
`txV3` (one receive `(op, valid)` per op record) as its only receiver, so:

* `filter_tagged_length`: the public messages of one tagged segment, by bus;
* **`pubCount_sig`**: `pubCount SIG true m` = the multiplicity of `m` among `(o, valid_o)`;
* **`tx_ops_perm`**: the op indices of the `txV3` view are a permutation of `0 … T0 − 1`.
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.D1
open ZkFormal.NearV3.D1.Public

theorem filter_tagged_length (s : PubSeg) (rows : ZkFormal.NearV3.Public.Payload) (b : Nat) (sd : Bool)
    (m : List Fp) :
    ((tagged s rows).filter fun x => decide (x = (b, sd, m))).length =
      if s.bus = b ∧ s.send = sd then
        ((List.range rows.length).map fun j => ZkFormal.NearV3.Public.recordValues s j (rows.getD j [])).count m
      else 0 := by
  unfold tagged
  rw [List.filter_map, List.length_map, ← List.countP_eq_length_filter]
  split
  · next hb =>
    obtain ⟨rfl, rfl⟩ := hb
    rw [List.count_eq_countP, List.countP_map, List.countP_map]
    apply List.countP_congr
    intro x _
    simp
  · next hb =>
    rw [List.countP_map]
    apply List.countP_eq_zero.mpr
    intro x _ hx
    simp only [Function.comp_def, decide_eq_true_eq, Prod.mk.injEq] at hx
    exact hb ⟨hx.1, hx.2.1⟩

/-- The public `SIG` records. -/
def sigRecs (p : PrepD1) : List (List Fp) :=
  (List.range p.ops.length).map fun o =>
    [((o : Nat) : Fp), ZkFormal.NearV3.Public.byteF (UInt8.ofNat (p.ops.getD o default).valid)]

set_option maxHeartbeats 2000000 in
/-- **The public `SIG` messages** are `sigRecs p`, with multiplicity. -/
theorem pubCount_sig (p : PrepD1) (ov : Nat) (hr : ZkFormal.NearV3.Public.RootsSized p.base)
    (hs : ∀ s ∈ p.base.lists, s.root.length = 32) (hleaves : ∀ l ∈ p.leaves, l.length = 32)
    (hlen : (preparedBytesD1 p ov).length < 256 ^ 4) (m : List Fp) :
    pubCount nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) B_SIG true m = (sigRecs p).count m := by
  rw [pubCountD1_split p ov hr hs hlen, pubCount_nobus segsV3_no_sig true, Nat.zero_add,
    newMsgs_eq p ov hr hlen hleaves]
  simp only [List.filter_append, List.length_append, filter_tagged_length]
  simp only [bodyPrefixPlan, txpPlan, sigPlan, keyPlan, leafPlan, ridPlan, ZkFormal.NearV3.Public.plainPlan,
    show (0 : Nat) ≠ B_SIG by decide, show B_TXP ≠ B_SIG by decide, show B_PKEY ≠ B_SIG by decide,
    show B_PLEAF ≠ B_SIG by decide, show B_PRID ≠ B_SIG by decide, false_and, ite_false, true_and, ite_true,
    Nat.zero_add, Nat.add_zero]
  unfold sigRecs
  congr 1
  rw [show (sigPayload p.ops).length = p.ops.length by simp [sigPayload]]
  apply List.map_congr_left
  intro o ho
  have ho' : o < p.ops.length := List.mem_range.mp ho
  simp [ZkFormal.NearV3.Public.recordValues, sigPayload, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_eq_getElem ho']

/-- A permutation of images under a map injective on a set, of lists inside the set, is a
permutation of the lists. -/
theorem perm_of_map_inj {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → β} {S : α → Prop}
    (hinj : ∀ a b, S a → S b → f a = f b → a = b) :
    ∀ {l1 l2 : List α}, (∀ a ∈ l1, S a) → (∀ a ∈ l2, S a) → (l1.map f).Perm (l2.map f) → l1.Perm l2 := by
  intro l1 l2 h1 h2 hp
  apply List.perm_iff_count.mpr
  intro a
  by_cases ha : S a
  · have hc := List.perm_iff_count.mp hp (f a)
    have key : ∀ l : List α, (∀ x ∈ l, S x) → (l.map f).count (f a) = l.count a := by
      intro l hl
      induction l with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.map_cons, List.count_cons]
        rw [ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))]
        congr 1
        by_cases hx : x = a
        · subst hx; simp
        · have : f x ≠ f a := fun e => hx (hinj x a (hl x (List.mem_cons_self ..)) ha e)
          simp [hx, this]
    rw [← key l1 h1, ← key l2 h2, hc]
  · rw [List.count_eq_zero.mpr (fun hm => ha (h1 a hm)), List.count_eq_zero.mpr (fun hm => ha (h2 a hm))]

section
variable {cb : NearSpec.Bytes} {h : HintD1} {p : PrepD1} {ov : Nat} {tr : Trace Fp} {es : List TxE}
  (hp : prepD1 cb h = .ok p) (hlen : (preparedBytesD1 p ov).length < P)
  (hH : HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) tr) (hW : TxWf es)
  (hT : TableTraffic TxV3.interactions tr T_TX (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) (txTraffic es))
include hp hlen hH hW hT

omit hW in
/-- **`SIG` balance**: `txV3`'s receives are the public `SIG` records. -/
theorem tx_sig_count (m : List Fp) :
    ((es.map fun e => Msg.toFp [e.op, e.valid])).count m = (sigRecs p).count m := by
  have hP : P < 256 ^ 4 := by unfold P; omega
  rw [← pubCount_sig p ov (prepD1_roots hp) (prepD1_source_roots hp) (prepD1_leaves hp) (by omega)]
  have hb := hH.balance B_SIG m
  rw [ZkFormal.NearV3.Assembly.busCount_users_d1 (U := [25]) (by decide) (by decide) (by decide +kernel),
    ZkFormal.NearV3.Assembly.busCount_users_d1 (U := [25]) (by decide) (by decide) (by decide +kernel)] at hb
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hb
  rw [show isAtD1 25 = TxV3.interactions from rfl, show (25 : Nat) = T_TX from rfl,
    (hT B_SIG m).1, (hT B_SIG m).2] at hb
  have hs0 : txSends es B_SIG = [] := by
    simp [txSends, show B_SIG ≠ B_MEM by decide, show B_SIG ≠ B_AKMEM by decide]
  have hpf : pubCount nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) B_SIG false m = 0 := by
    rcases Nat.eq_zero_or_pos (pubCount nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov))
      B_SIG false m) with h0 | h0
    · exact h0
    · exact absurd (pub_sig_mem p ov (prepD1_roots hp) (prepD1_source_roots hp) (prepD1_leaves hp)
        (by omega) h0).1 (by decide)
  simp only [txTraffic, hs0, List.map_nil, List.count_nil, Nat.zero_add, hpf, Nat.add_zero] at hb
  rw [hb]
  simp only [txRecvs, show B_SIG ≠ B_TXP by decide, ite_false, ite_true, List.map_map]
  rfl

/-- **The `txV3` ops are the public ops, once each.** -/
theorem tx_ops_perm : (es.map TxE.op).Perm (List.range p.ops.length) := by
  have hP : P < 256 ^ 4 := by unfold P; omega
  have hT0 : p.ops.length ≤ 2 * NearSpecV3.NT0 := by
    have := (prepD1_m0_t0 hp).2
    obtain ⟨w, -, rfl⟩ := prepD1_spec hp
    exact this
  have hoP : ∀ o, o < p.ops.length → o < P := by
    intro o ho; unfold NearSpecV3.NT0 at hT0; unfold P; omega
  -- the `SIG` messages of `txV3` are the public records, as a permutation
  have hperm : (es.map fun e => Msg.toFp [e.op, e.valid]).Perm (sigRecs p) :=
    List.perm_iff_count.mpr (tx_sig_count hp hlen hH hT)
  have hsig : (es.map fun e => Msg.toFp [e.op, e.valid]) = (es.map TxE.op).map fun o =>
      [((o : Nat) : Fp), ZkFormal.NearV3.Public.byteF (UInt8.ofNat (p.ops.getD o default).valid)] := by
    rw [List.map_map]
    apply List.map_congr_left
    intro e he
    simp only [Function.comp_def, Msg.toFp, List.map_cons, List.map_nil, natCast_eq]
    rw [(tx_op_lt hp hlen hH hW hT he).2]
  rw [hsig] at hperm
  unfold sigRecs at hperm
  -- the record map is injective on `[0, T0)` and on the view's ops
  have hinj : ∀ o1 o2, o1 < p.ops.length → o2 < p.ops.length →
      ([((o1 : Nat) : Fp), ZkFormal.NearV3.Public.byteF (UInt8.ofNat (p.ops.getD o1 default).valid)] : List Fp) =
        [((o2 : Nat) : Fp), ZkFormal.NearV3.Public.byteF (UInt8.ofNat (p.ops.getD o2 default).valid)] → o1 = o2 := by
    intro o1 o2 h1 h2 he
    simp only [List.cons.injEq] at he
    have := congrArg Fp.toNat he.1
    rw [natCast_eq, natCast_eq, Fp.toNat_ofNat, Fp.toNat_ofNat, Nat.mod_eq_of_lt (hoP o1 h1),
      Nat.mod_eq_of_lt (hoP o2 h2)] at this
    exact this
  have hlt : ∀ o ∈ es.map TxE.op, o < p.ops.length := by
    intro o ho
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
    exact (tx_op_lt hp hlen hH hW hT he).1
  exact perm_of_map_inj hinj hlt (fun o ho => List.mem_range.mp ho) hperm

end

end ZkFormal.NearV3.D1.Link
