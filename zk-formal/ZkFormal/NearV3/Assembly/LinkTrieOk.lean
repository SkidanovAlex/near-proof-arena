import ZkFormal.NearV3.Assembly.LinkRcptWalk
import ZkFormal.NearV3.Rcpt.Link.RcptCore
import ZkFormal.NearV3.Rcpt.Link.SrecLink

/-!
# ZkFormal.NearV3.Assembly.LinkTrieOk — the receipt core's `TrieOk` on the main trie family

The receipt core's model on this lane's family (`Mdl r st := recModel r.lists r.accts (preV r)
(Tf r 0 st)`: slots are value ids, `base` the pre bytes).  Given the record-side agreement
`hinit : ∀ k, (Mdl r st).valsAt 0 k = preV r k` (a written slot's `Account.encode` of the acct
record is the pre value; unwritten slots are `preV` by definition):

* `lenOk_of` — a `LenPres` assignment is `LenOk` (lengths of the initial values = pre lengths);
* **`init_of`** — `T (valsAt 0) = Q` for the scheduler's upsert `Q` of `Fpre r 0` (`Tf_pre`);
* **`get_of`, `find_of`, `set_of`** — `TrieOk.get` / `.find` / `.set` for every `LenPres` `v`;
* **`ak_of`** — a system receipt to its own signer finds, at its access-key path, `some (v akk)`
  (`akf = VAL`) or `none` (`akf = ABS`) for every `LenPres` `v` (`ee` by `RcptLink.ee_of_self`).

`TrieOk.get`/`.find` of lane v3-rcpt-sound quantify over **all** `v`; on this family only
length-preserving `v` are meaningful (the family is an upsert of a trie that is well-formed only
for those), and `RunModel.step` uses them at `valsAt r` (`valsAt_lenPres`) only.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkTrieOk

open ZkFormal.NearV3 ZkFormal.NearV3.Link3 ZkFormal.NearV3.UpsRows LinkImplicit LinkSched0 LinkTrieFam
  LinkRcptWalk

/-- The receipt core's model on the main trie family. -/
noncomputable abbrev Mdl (r : V3Records) (st : NearSpec.Bytes) : RcptLink.RunModel :=
  RcptLink.recModel r.lists r.accts (preV r) (Tf r 0 st)

section
variable {r : V3Records} {st : NearSpec.Bytes}

theorem mdl_rc {i : Nat} (hi : i < (flatR r.lists).length) :
    (Mdl r st).rc i = (flatR r.lists)[i].toRcptV.toReceipt := by
  rw [RcptLink.recModel_rc hi, RcptLink.R_rv]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem mdl_slot {i : Nat} (hi : i < (flatR r.lists).length) :
    (Mdl r st).slot i = (flatR r.lists)[i].kslot := by
  show (RcptLink.R (RcptLink.rv r.lists) i).kslot = _
  rw [RcptLink.R_rv]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, RcptE.toRcptV]

theorem mdl_len : (Mdl r st).rs.length = (flatR r.lists).length := RcptLink.recModel_length

theorem lenOk_of (hinit : ∀ k, (Mdl r st).valsAt 0 k = preV r k) {v : Nat → NearSpec.Bytes}
    (hv : (Mdl r st).LenPres v) : LenOk r v := fun k => by rw [hv k, hinit k]

theorem lenPres_of (hinit : ∀ k, (Mdl r st).valsAt 0 k = preV r k) {v : Nat → NearSpec.Bytes}
    (hv : LenOk r v) : (Mdl r st).LenPres v := fun k => by rw [hv k, hinit k]

end

section
variable {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
  {tr : Trace Fp} {r : V3Records}

/-- **`MainTrieLink.init`**. -/
theorem init_of (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {st : NearSpec.Bytes} (hinit : ∀ k, (Mdl r st).valsAt 0 k = preV r k) {Q : NearSpec.PTrie}
    (hQ : (Fpre r 0).upsert NearSpecV3.keyBwState st = some Q) :
    (Mdl r st).T ((Mdl r st).valsAt 0) = Q := by
  have e : (Mdl r st).valsAt 0 = preV r := funext hinit
  rw [e]
  exact Tf_pre hp hsz hH T W st hQ

/-- **`TrieOk.find`** (and `get`) for length-preserving assignments. -/
theorem find_of (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (h0 : 0 < p.sched.length) {st : NearSpec.Bytes} (hinit : ∀ k, (Mdl r st).valsAt 0 k = preV r k)
    {i : Nat} (hi : i < (Mdl r st).rs.length) {v : Nat → NearSpec.Bytes} (hv : (Mdl r st).LenPres v) :
    ((Mdl r st).T v).find (NearSpec.accountKeyPath ((Mdl r st).rc i).receiverId) =
        some (some (v ((Mdl r st).slot i))) ∧
      ((Mdl r st).T v).get (NearSpec.accountKeyPath ((Mdl r st).rc i).receiverId) =
        some (v ((Mdl r st).slot i)) := by
  rw [mdl_len] at hi
  rw [mdl_rc hi, mdl_slot hi]
  exact rcpt_find hp hsz hH T W h0 st hi (lenOk_of hinit hv)

/-- **`TrieOk.set`** (length-preserving assignment, same-length value). -/
theorem set_of (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (h0 : 0 < p.sched.length) {st : NearSpec.Bytes} (hinit : ∀ k, (Mdl r st).valsAt 0 k = preV r k)
    {i : Nat} (hi : i < (Mdl r st).rs.length) {v : Nat → NearSpec.Bytes} (hv : (Mdl r st).LenPres v)
    {b : NearSpec.Bytes} (hb : b.length = (v ((Mdl r st).slot i)).length) :
    ((Mdl r st).T v).set (NearSpec.accountKeyPath ((Mdl r st).rc i).receiverId) b =
      some ((Mdl r st).T (RcptLink.RunModel.upd v ((Mdl r st).slot i) b)) := by
  rw [mdl_len] at hi
  rw [mdl_slot hi] at hb ⊢
  rw [mdl_rc hi]
  exact rcpt_set hp hsz hH T W h0 st hi (lenOk_of hinit hv) hb

/-- **`TrieOk.ak`, trie half**: a system receipt to its own signer finds, at its access-key path,
`some (v akk)` (walk kind `VAL`) or `none` (`ABS`). -/
theorem ak_of (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (h0 : 0 < p.sched.length) {st : NearSpec.Bytes} (hinit : ∀ k, (Mdl r st).valsAt 0 k = preV r k)
    {i : Nat} (hi' : i < (flatR r.lists).length) (hsys : (Mdl r st).isSys i = true)
    (hsr : ((Mdl r st).rc i).signerId = ((Mdl r st).rc i).receiverId)
    {v : Nat → NearSpec.Bytes} (hv : (Mdl r st).LenPres v) :
    (flatR r.lists)[i].ee = true ∧
    ((Mdl r st).T v).find (NearSpecV3.keyAccessKey ((Mdl r st).rc i).receiverId ((Mdl r st).rc i).signerPk) =
      some (if (flatR r.lists)[i].akf = FK_VAL then some (v (flatR r.lists)[i].akk) else none) := by
  obtain ⟨toks, -, -, hwf, -⟩ := W.lists.toks
  have hWf := hwf i hi'
  rw [mdl_rc hi'] at hsr ⊢
  have hsys' : (flatR r.lists)[i].sys = true := by
    have := hsys
    simp only [RcptLink.RunModel.isSys, mdl_rc hi', RcptV.toReceipt, beq_iff_eq] at this
    exact hWf.sysIff.mpr this
  have hsv : toBytes (flatR r.lists)[i].s = toBytes (flatR r.lists)[i].v := hsr
  have hee := RcptLink.ee_of_self hH T W hi' hsys' hsv
  refine ⟨hee, ?_⟩
  have := ak_find hp hsz hH T W h0 st hi' hee (lenOk_of hinit hv)
  simp only [RcptV.toReceipt] at this ⊢
  rw [← hsv]
  exact this

/-- `hinit` reduces to the written slots (unwritten slots hold `base = preV`). -/
theorem hinit_of {st : NearSpec.Bytes}
    (hw : ∀ k, (Mdl r st).written k = true → (Mdl r st).valsAt 0 k = preV r k) :
    ∀ k, (Mdl r st).valsAt 0 k = preV r k := by
  intro k
  by_cases e : (Mdl r st).written k = true
  · exact hw k e
  · simp only [RcptLink.RunModel.valsAt, e, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- **`hpost`** for the receipt core's final trie `T (valsAt n)`: the ups post root of instance
`0`, given the record-side agreement of the final values with the post value records —
a receipt slot is written in instance `0` with the acct's post encoding (`hrw`), and an
instance-`0` written slot of no receipt keeps its pre bytes (`hun`). -/
theorem post_of (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {x : ExtV3} (hxh : x.heads = xHeads (r.ups.map upsE))
    (h0 : 0 < p.sched.length) {o : NearSpecV3.Scheduler.Output}
    (ho : NearSpecV3.Scheduler.runCore p.sched[0] (Sched.prevOf tr T_CODEC 0) = some o)
    (hinit : ∀ k, (Mdl r (schedOut o).state).valsAt 0 k = preV r k)
    (hrw : ∀ k, (Mdl r (schedOut o).state).written k = true → wrote r.nodes k = true ∧
      (Mdl r (schedOut o).state).valsAt (Mdl r (schedOut o).state).rs.length k =
        toB (LinkVPost.pnOf r.accts k))
    (hun : ∀ e ∈ r.values, valTau r.nodes e.vid = 0 → wrote r.nodes e.vid = true →
      (Mdl r (schedOut o).state).written e.vid = false →
        toB (LinkVPost.pnOf r.accts e.vid) = toB e.bytes) :
    ((Mdl r (schedOut o).state).T
      ((Mdl r (schedOut o).state).valsAt (Mdl r (schedOut o).state).rs.length)).hashOf = x.post 0 := by
  apply Tf_post hp hsz hH T W hxh h0 ho
    (lenOk_of hinit (RcptLink.RunModel.valsAt_lenPres _ _))
  intro e he he0
  by_cases hw : (Mdl r (schedOut o).state).written e.vid = true
  · obtain ⟨hwr, hv⟩ := hrw e.vid hw
    rw [if_pos hwr, hv]
  · have hw' : (Mdl r (schedOut o).state).written e.vid = false := by simpa using hw
    have hb : (Mdl r (schedOut o).state).valsAt (Mdl r (schedOut o).state).rs.length e.vid =
        toB e.bytes := by
      simp only [RcptLink.RunModel.valsAt, hw', Bool.false_eq_true, ↓reduceIte]
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he
      exact preV_at W ht
    rw [hb]
    split
    · rename_i hwr; exact (hun e he he0 hwr hw').symm
    · rfl

end

end LinkTrieOk

end ZkFormal.NearV3.Assembly
