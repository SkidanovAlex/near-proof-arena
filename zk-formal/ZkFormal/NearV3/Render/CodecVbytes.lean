import ZkFormal.NearV3.Render.CodecVbytesRows
import ZkFormal.NearV3.Render.CodecCanon

/-!
# Codec `VBYTES` (bus 21) on the native blocks

* `decode_encode'`: `State.decode` is exact — a decoded state re-encodes to the decoded bytes.
* **`prior_stateBytes`**: a present canonical prior's bytes are the codec block's pre bytes
  `stateBytes ids a0 hpre`.
* **`codec_vbytes_native`**: on `A`'s trace, the frozen codec's `VBYTES` sends are, block by block,
  `posMsgs vid 0 (prior bytes)` for a present prior and nothing for an absent one.
-/
namespace ZkFormal.NearV3.Render.CdcGrant
open NearSpec NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Candidates ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.CodecDigest
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Render.Cdc

theorem takeN_some : ∀ (w : Nat) (bs h t : Bytes), takeN w bs = some (h, t) → h.length = w ∧ bs = h ++ t
  | 0, bs, h, t, e => by
    simp only [takeN, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e; simp
  | w + 1, [], h, t, e => by simp [takeN] at e
  | w + 1, b :: bs, h, t, e => by
    simp only [takeN] at e
    cases hq : takeN w bs with
    | none => simp [hq] at e
    | some q =>
      obtain ⟨h', t'⟩ := q
      simp only [hq, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      obtain ⟨h1, h2⟩ := takeN_some w bs h' t' hq
      exact ⟨by simp [h1], by simp [h2]⟩

theorem readLE_some {w : Nat} {bs t : Bytes} {x : Nat} (e : readLE w bs = some (x, t)) :
    bs = leN w x ++ t := by
  unfold readLE at e
  cases hq : takeN w bs with
  | none => simp [hq] at e
  | some q =>
    obtain ⟨h, t'⟩ := q
    simp only [hq, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨h1, h2⟩ := takeN_some w bs h t' hq
    rw [ZkFormal.NearV3.leN_leNat' h1, h2]

theorem readLink_some {bs t : Bytes} {l : Bandwidth.LinkAllowance} (e : Bandwidth.readLink bs = some (l, t)) :
    bs = l.encode ++ t := by
  unfold Bandwidth.readLink at e
  cases h1 : readU64 bs with
  | none => simp [h1] at e
  | some q1 =>
    obtain ⟨s, b1⟩ := q1
    simp only [h1] at e
    cases h2 : readU64 b1 with
    | none => simp [h2] at e
    | some q2 =>
      obtain ⟨r, b2⟩ := q2
      simp only [h2] at e
      cases h3 : readU64 b2 with
      | none => simp [h3] at e
      | some q3 =>
        obtain ⟨a, b3⟩ := q3
        simp only [h3, Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        rw [readLE_some h1, readLE_some h2, readLE_some h3]
        simp [Bandwidth.LinkAllowance.encode, u64]

theorem readMany_some : ∀ (n : Nat) (bs t : Bytes) (ls : List Bandwidth.LinkAllowance),
    readMany Bandwidth.readLink n bs = some (ls, t) →
      ls.length = n ∧ bs = concatAll (ls.map Bandwidth.LinkAllowance.encode) ++ t
  | 0, bs, t, ls, e => by
    simp only [readMany, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e; simp [concatAll]
  | n + 1, bs, t, ls, e => by
    simp only [readMany] at e
    cases h1 : Bandwidth.readLink bs with
    | none => simp [h1] at e
    | some q =>
      obtain ⟨l, r⟩ := q
      simp only [h1] at e
      cases h2 : readMany Bandwidth.readLink n r with
      | none => simp [h2] at e
      | some q2 =>
        obtain ⟨ls', t'⟩ := q2
        simp only [h2, Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        obtain ⟨hl, hr⟩ := readMany_some n r t' ls' h2
        refine ⟨by simp [hl], ?_⟩
        rw [readLink_some h1, hr]
        simp [concatAll, List.append_assoc]

/-- **`State.decode` is exact**: decoded bytes are the encoding of the decoded state. -/
theorem decode_encode' {v : Bytes} {st : Bandwidth.State} (h : Bandwidth.State.decode v = some st) :
    st.encode = v := by
  unfold Bandwidth.State.decode at h
  cases h1 : readU8 v with
  | none => simp [h1] at h
  | some q1 =>
    obtain ⟨tag, b1⟩ := q1
    simp only [h1] at h
    by_cases ht : tag = 0
    · simp only [ht, ne_eq, not_true_eq_false, ite_false] at h
      cases h2 : readU32 b1 with
      | none => simp [h2] at h
      | some q2 =>
        obtain ⟨n, b2⟩ := q2
        simp only [h2] at h
        cases h3 : readMany Bandwidth.readLink n b2 with
        | none => simp [h3] at h
        | some q3 =>
          obtain ⟨links, b3⟩ := q3
          simp only [h3] at h
          cases h4 : readHash b3 with
          | none => simp [h4] at h
          | some q4 =>
            obtain ⟨hh, b4⟩ := q4
            simp only [h4] at h
            by_cases he : b4 = []
            · simp only [he, ite_true, Option.some.injEq] at h
              subst h
              have e1 := readLE_some h1
              have e2 := readLE_some h2
              obtain ⟨hl, e3⟩ := readMany_some n b2 b3 links h3
              obtain ⟨-, e4⟩ := takeN_some 32 b3 hh b4 h4
              rw [e1, e2, e3, e4, he, ht]
              simp [Bandwidth.State.encode, hl, u32, leN, List.append_assoc]
            · simp [he] at h
    · simp [ht] at h


/-- A canonical prior's links, in order. -/
theorem links_canon (ids : List Nat) (prev : NearSpec.Bandwidth.State)
    (hL : prev.links.map (fun la => (la.sender, la.receiver)) = ids.flatMap fun s => ids.map fun r => (s, r)) :
    prev.links = (List.range (ids.length * ids.length)).map fun l =>
      (⟨ids.getD (l / ids.length) 0, ids.getD (l % ids.length) 0, (a0Canon ids.length prev)[l]!⟩ :
        NearSpec.Bandwidth.LinkAllowance) := by
  have hlen : prev.links.length = ids.length * ids.length := by
    have := congrArg List.length hL
    rw [CdcAllow.pairs_eq] at this
    simpa using this
  have ha : ∀ l (hl : l < prev.links.length), (a0Canon ids.length prev)[l]! = (prev.links[l]).allowance := by
    intro l hl
    simp only [a0Canon, hlen, ite_true]
    rw [getElem!_pos _ l (by simp; omega)]
    simp
  apply List.ext_getElem (by simp [hlen])
  intro l h1 h2
  have hl : l < ids.length * ids.length := by omega
  have hp := congrArg (fun xs => xs[l]?) hL
  simp only [CdcAllow.pairs_eq, List.getElem?_map, List.getElem?_eq_getElem h1,
    List.getElem?_range hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp
  simp only [List.getElem_map, List.getElem_range, ha l h1]
  cases hx : prev.links[l]
  rw [hx] at hp
  simp only at hp
  rw [hp.1, hp.2]

/-- **A present canonical prior's bytes are the codec block's pre bytes.** -/
theorem prior_stateBytes (b : NativeBlock) (hval : b.Valid) {v : Bytes} (hq : b.prior = some v)
    (hL : b.old.links.map (fun la => (la.sender, la.receiver)) =
      b.pub.ids.flatMap fun s => b.pub.ids.map fun r => (s, r))
    (hn : b.run.n = b.pub.ids.length) :
    v.map UInt8.toNat = stateBytes (blkOf b).ids (blkOf b).a0 (blkOf b).hpre := by
  have hd : Bandwidth.State.decode v = some b.old := by
    have := hval.2.2.2.1; rw [hq] at this; exact this
  rw [← decode_encode' hd, encode_bytes, links_canon _ _ hL]
  have hids : (blkOf b).ids = b.pub.ids := rfl
  have ha0 : (blkOf b).a0 = fun kk => (a0Canon b.pub.ids.length b.old)[kk]! := by
    simp only [blkOf, hn]; rfl
  have hh : (blkOf b).hpre = b.old.sanityHash.map UInt8.toNat := by
    simp only [blkOf, hpreOf, hq, Option.isSome_some, ite_true]; rfl
  rw [hids, ha0, hh]
  unfold stateBytes
  simp only [List.length_map, List.length_range, List.flatMap_map]


theorem decode_hash_len {v : Bytes} {st : Bandwidth.State} (h : Bandwidth.State.decode v = some st) :
    st.sanityHash.length = 32 := by
  unfold Bandwidth.State.decode at h
  cases h1 : readU8 v with
  | none => simp [h1] at h
  | some q1 =>
    obtain ⟨tag, b1⟩ := q1
    simp only [h1] at h
    by_cases ht : tag = 0
    · simp only [ht, ne_eq, not_true_eq_false, ite_false] at h
      cases h2 : readU32 b1 with
      | none => simp [h2] at h
      | some q2 =>
        obtain ⟨n, b2⟩ := q2
        simp only [h2] at h
        cases h3 : readMany Bandwidth.readLink n b2 with
        | none => simp [h3] at h
        | some q3 =>
          obtain ⟨links, b3⟩ := q3
          simp only [h3] at h
          cases h4 : readHash b3 with
          | none => simp [h4] at h
          | some q4 =>
            obtain ⟨hh, b4⟩ := q4
            simp only [h4] at h
            by_cases he : b4 = []
            · simp only [he, ite_true, Option.some.injEq] at h
              subst h
              exact (takeN_some 32 b3 hh b4 h4).1
            · simp [he] at h
    · simp [ht] at h

theorem hpre_len (b : NativeBlock) (hval : b.Valid) : (blkOf b).hpre.length = 32 := by
  simp only [blkOf, hpreOf]
  cases hq : b.prior with
  | none => simp
  | some v =>
    have hd : Bandwidth.State.decode v = some b.old := by
      have := hval.2.2.2.1; rw [hq] at this; exact this
    simp only [Option.isSome_some, ite_true, List.length_map]
    exact decode_hash_len hd

/-- The `VBYTES` sends of a native block: its prior's bytes at its value id (none if absent). -/
def priorMsgs (b : NativeBlock) : List (List Fp) :=
  match b.prior with
  | some v => posMsgs b.vid 0 (v.map UInt8.toNat)
  | none => []

/-- **The frozen codec's `VBYTES` sends on `A`'s trace.** -/
theorem codec_vbytes_native {cb wb : Bytes} (A : AcceptedV3 cb wb) {B : Nat} {bs : List NativeBlock}
    (hc : PriorCore A.p B bs) (hres : ∀ b ∈ bs, NatRes b)
    (hctx : bs.map (fun b => (b.witness.ctx, b.witness.pre)) =
      (A.m.ctx A.k, A.m.pre) :: A.steps.map (fun e => (implicitCtx A.k e, e.pre)))
    (t : Nat) (pub : List Fp) :
    rowsTrafficFp Codec.table.interactions (codecCell (bs.map blkOf)) 22 t pub ZkFormal.NearV3.B_VBYTES true =
      bs.flatMap priorMsgs := by
  rw [codec_bus _ (prior_cap hc) t pub _ _ vbT (rt_vbytes · · t pub), List.flatMap_map]
  apply flatMap_congr_rt
  intro b hb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨⟨hsch, hr⟩, _, _⟩ := hc.indexed i b hi
  have hil : i < bs.length := (List.getElem?_eq_some_iff.mp hi).1
  have hval := (hc.valid b hb).1
  have hok := blkOf_ok b (hc.valid b hb).2 i (by have := hc.length; omega) hr
    (prepD0_sched A.hp b.pub (List.mem_of_getElem? hsch)) (hres b hb)
  have hn : b.run.n = b.pub.ids.length := (ProcActualRunProjection.run_fields _ i b.run hr).2.1
  rw [blk_vbytes (blkOf b) hok (by simp only [blkOf, hn]; rfl) (hpre_len b hval)]
  unfold priorMsgs
  cases hq : b.prior with
  | none => simp [blkOf, hq]
  | some v =>
    have hpres : b.prior.isSome = true := by rw [hq]; rfl
    rw [← prior_stateBytes b hval hq (prior_canonical A hc hctx b hb hpres) hn]
    have h1 : (blkOf b).I.pres = true := hpres
    have h2 : (blkOf b).I.vid = b.vid := rfl
    rw [h1, h2]
    rfl

end ZkFormal.NearV3.Render.CdcGrant
