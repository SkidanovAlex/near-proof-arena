import ZkFormal.NearV3.Assembly.LinkSched0
import ZkFormal.NearV3.Assembly.LinkRefine
import ZkFormal.NearV3.Assembly.PrepFacts

/-!
# ZkFormal.NearV3.Assembly.LinkTrieFam — the main trie family of the receipt core

The receipt core (`RcptLink.MainTrieLink`, lane v3-rcpt-sound) runs on a trie family
`T v` — the main trie after the scheduler step with value record `k` (by value id) holding
`v k`.  Here: `Fv r τ v` is the record tree of instance `τ` with every value record `e` holding
`v e.vid` (`valsBy`), and `Tf r τ st v` is its `0x0f` upsert by `st`.

* `Fv_pre` — with the pre bytes, `Fv` is the pre record tree `Fpre r τ`;
* `Fv_wf` — `Fv r τ v` is well-formed for every **length-preserving** `v`
  (`(v k).length = (pre k).length`: `VSlot3.wf` bounds value lengths);
* `Fv_find` — a key that reaches value record `t` (`fullReach`) finds `v es[t].vid`;
* `Fv_set` — `set` at such a key is the family at the updated assignment (`post_eq_set`,
  `occ_le_one`);
* `Fv_find_key` — the `0x0f` lookup is defined for every `v` (`find_reach`/`reach_find`,
  `find_none_vals`), so `Tf` is a real upsert (`Tf_upsert`);
* `Tf_find`, `Tf_set` — the same through the upsert for keys `≠ 0x0f` (`find_upsert_other`,
  `set_upsert_comm`; the latter needs the old and new value of equal length).
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkTrieFam

open ZkFormal.NearV3 ZkFormal.NearV3.Link3 ZkFormal.NearV3.UpsRows LinkImplicit LinkSched0

/-! ## Ranked DAGs with other value records of the same lengths -/

section Dag
variable {ns : List NodeRec3}

theorem rec_wf_vals {V₁ V₂ : List ValRec3} (hlen : ∀ i, (valOf V₂ i).length = (valOf V₁ i).length) :
    ∀ r : Rec3, r.wf V₁ → r.wf V₂
  | .leaf k v m, h => by
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, h2, ?_, h4⟩
    cases v with
    | ref => exact h3
    | val i => show (valOf V₂ i).length < _; rw [hlen]; exact h3
  | .ext k kid m, h => h
  | .branch v kids m, h => by
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, fun s hs => ?_, h3, h4⟩
    have := h2 s hs
    cases s with
    | ref => exact this
    | val i => show (valOf V₂ i).length < _; rw [hlen]; exact this

theorem rootedDag_vals {V₁ V₂ : List ValRec3} {τ root : Nat} {rk : Nat → Nat}
    (hd : RootedDagR ns V₁ τ root rk)
    (htau : ∀ (i : Nat) (vr : ValRec3), V₁[i]? = some vr → ∃ vr' : ValRec3, V₂[i]? = some vr' ∧ vr'.tau = vr.tau)
    (hlen : ∀ i, (valOf V₂ i).length = (valOf V₁ i).length) : RootedDagR ns V₂ τ root rk where
  root_inst := hd.root_inst
  child := hd.child
  vals n nr hn ht i hi := by
    obtain ⟨vr, hvr, hvt⟩ := hd.vals n nr hn ht i hi
    obtain ⟨vr', hvr', hvt'⟩ := htau i vr hvr
    exact ⟨vr', hvr', hvt'.trans hvt⟩
  wf n nr hn ht := rec_wf_vals hlen _ (hd.wf n nr hn ht)

end Dag

/-! ## The family -/

/-- Value records with value record `e` holding `v e.vid`. -/
def valsBy (vs : List NodeS3) (es : List ValE) (v : Nat → NearSpec.Bytes) : List ValRec3 :=
  es.map fun e => ⟨valTau vs e.vid, v e.vid⟩

/-- The pre bytes of value id `k`. -/
def preV (r : V3Records) (k : Nat) : NearSpec.Bytes :=
  valOf (valsOf3 r.nodes r.values) (vpos (vid0 r.values) k)

/-- The record tree of instance `τ` with value assignment `v`. -/
noncomputable def Fv (r : V3Records) (τ : Nat) (v : Nat → NearSpec.Bytes) : NearSpec.PTrie :=
  fullTree (Rpost r.nodes r.values) (valsBy r.nodes r.values v) (headAt r.heads τ).rid

theorem valOf_valsBy {vs : List NodeS3} {es : List ValE} (v : Nat → NearSpec.Bytes) {t : Nat}
    (ht : t < es.length) : valOf (valsBy vs es v) t = v es[t].vid := by
  simp [valOf, valsBy, List.getElem?_eq_getElem ht]

theorem valOf_valsBy_out {vs : List NodeS3} {es : List ValE} (v : Nat → NearSpec.Bytes) {t : Nat}
    (ht : es.length ≤ t) : valOf (valsBy vs es v) t = [] := by
  simp [valOf, valsBy, List.getElem?_eq_none ht]

section Fam
variable {pub : List Fp} {tr : Trace Fp} {r : V3Records} {K : Nat} {r0 rK : List Nat}

theorem preV_at (W : V3RecordsWf pub r) {t : Nat} (ht : t < r.values.length) :
    preV r r.values[t].vid = toB r.values[t].bytes := by
  unfold preV
  rw [vpos_at W.values (vlen_le W.values) ht]
  simp [valOf, valsOf3, List.getElem?_eq_getElem ht]

theorem valsBy_pre (W : V3RecordsWf pub r) :
    valsBy r.nodes r.values (preV r) = valsOf3 r.nodes r.values := by
  apply List.ext_getElem
  · simp [valsBy, valsOf3]
  · intro t h1 h2
    have ht : t < r.values.length := by simpa [valsBy] using h1
    simp [valsBy, valsOf3, preV_at W ht]

/-- **With the pre bytes the family is the pre record tree.** -/
theorem Fv_pre (W : V3RecordsWf pub r) (τ : Nat) : Fv r τ (preV r) = Fpre r τ := by
  unfold Fv Fpre; rw [valsBy_pre W]

/-- Length-preserving assignments. -/
def LenOk (r : V3Records) (v : Nat → NearSpec.Bytes) : Prop := ∀ k, (v k).length = (preV r k).length

theorem valOf_len (W : V3RecordsWf pub r) {v : Nat → NearSpec.Bytes} (hv : LenOk r v) (i : Nat) :
    (valOf (valsBy r.nodes r.values v) i).length = (valOf (valsOf3 r.nodes r.values) i).length := by
  by_cases ht : i < r.values.length
  · rw [valOf_valsBy v ht, hv, ← valsBy_pre W, valOf_valsBy _ ht]
  · rw [valOf_valsBy_out v (by omega), ← valsBy_pre W, valOf_valsBy_out _ (by omega)]

theorem dag_v (W : V3RecordsWf pub r) (L : TrieLink pub tr r K r0 rK) {τ : Nat} (hτ : τ ≤ K)
    {v : Nat → NearSpec.Bytes} (hv : LenOk r v) :
    RootedDagR (Rpost r.nodes r.values) (valsBy r.nodes r.values v) τ (headAt r.heads τ).rid
      (rkOf r.nodes) := by
  obtain ⟨hh, htau⟩ := L.chain.head_mem τ hτ
  have hd := rootedDag3 W.nodes W.heads W.values L.parent L.vparent (vlen_le W.values)
    (recBytes_of W L) hh
  rw [htau] at hd
  refine rootedDag_vals hd (fun i vr hvr => ?_) (valOf_len W hv)
  simp only [valsOf3, List.getElem?_map] at hvr
  cases he : r.values[i]? with
  | none => rw [he] at hvr; cases hvr
  | some e =>
    rw [he] at hvr; cases hvr
    exact ⟨⟨valTau r.nodes e.vid, v e.vid⟩, by simp [valsBy, he], rfl⟩

/-- **The family is well-formed** for length-preserving assignments. -/
theorem Fv_wf (W : V3RecordsWf pub r) (L : TrieLink pub tr r K r0 rK) {τ : Nat} (hτ : τ ≤ K)
    {v : Nat → NearSpec.Bytes} (hv : LenOk r v) : (Fv r τ v).wf = true := by
  have hd := dag_v W L hτ hv
  exact fullTree_wfR hd _ hd.root_inst

/-- **A key reaching value record `t` finds `v es[t].vid`.** -/
theorem Fv_find {τ : Nat} {key : List Nat} {t : Nat}
    (hr : fullReach (Rpost r.nodes r.values) (headAt r.heads τ).rid key = some t)
    (ht : t < r.values.length) (v : Nat → NearSpec.Bytes) :
    (Fv r τ v).find key = some (some (v r.values[t].vid)) := by
  unfold Fv fullTree
  rw [reach_find _ _ _ _ hr, valOf_valsBy v ht]

/-- Replacing one value record of `valsBy` is updating the assignment at its id. -/
theorem setVal_valsBy (W : V3RecordsWf pub r) (v : Nat → NearSpec.Bytes) {t : Nat}
    (ht : t < r.values.length) (b : NearSpec.Bytes) :
    setVal (valsBy r.nodes r.values v) t b =
      valsBy r.nodes r.values (fun k => if k = r.values[t].vid then b else v k) := by
  apply List.ext_getElem
  · simp [setVal_length, valsBy]
  · intro j h1 h2
    have hj : j < r.values.length := by simpa [valsBy] using h2
    have hg := setVal_get? (valsBy r.nodes r.values v) t b j
    rw [List.getElem?_eq_getElem h1] at hg
    have hjt : r.values[j].vid = r.values[t].vid ↔ j = t := by
      constructor
      · intro e
        have a := vpos_at W.values (vlen_le W.values) hj
        have c := vpos_at W.values (vlen_le W.values) ht
        rw [e] at a; omega
      · rintro rfl; rfl
    by_cases e : j = t
    · subst e
      simp [valsBy] at hg ⊢
      simp_all
    · have e' : ¬ r.values[j].vid = r.values[t].vid := fun x => e (hjt.mp x)
      simp [valsBy, e'] at hg ⊢
      simp_all

/-- **`set` at a key reaching value record `t`** is the family at the updated assignment. -/
theorem Fv_set (W : V3RecordsWf pub r) (L : TrieLink pub tr r K r0 rK) {τ : Nat} {key : List Nat}
    {t : Nat} (hr : fullReach (Rpost r.nodes r.values) (headAt r.heads τ).rid key = some t)
    (ht : t < r.values.length) (v : Nat → NearSpec.Bytes) (b : NearSpec.Bytes) :
    (Fv r τ v).set key b = some (Fv r τ (fun k => if k = r.values[t].vid then b else v k)) := by
  unfold Fv
  rw [post_eq_set (valsBy r.nodes r.values v) b (by simpa [valsBy] using ht) hr
    (occ_le_one W.nodes W.heads W.values L.parent L.vparent t _), setVal_valsBy W v ht b]

end Fam

section Key
variable {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
  {tr : Trace Fp} {r : V3Records}

/-- The `0x0f` lookup is defined for every assignment. -/
theorem Fv_find_key (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {τ : Nat} (hτ : τ < p.sched.length) (hK : τ ≤ p.hdr.K) (v : Nat → NearSpec.Bytes) :
    (Fv r τ v).find NearSpecV3.keyBwState ≠ none := by
  have hf := pre_find_key hp hsz hH T W hτ hK
  rw [← LinkVBytes.keyBwState_eq] at hf
  unfold Fpre fullTree at hf
  unfold Fv fullTree
  cases hpv : Sched.prevOf tr T_CODEC τ with
  | none =>
    rw [hpv] at hf
    rw [find_none_vals _ _ _ _ _ hf]; simp
  | some b =>
    rw [hpv] at hf
    obtain ⟨j, hj, -⟩ := find_reach _ _ _ _ hf
    rw [reach_find _ _ _ _ hj]; simp

/-- The main trie family: the `0x0f` upsert of `Fv` by `st`. -/
noncomputable def Tf (r : V3Records) (τ : Nat) (st : NearSpec.Bytes) (v : Nat → NearSpec.Bytes) :
    NearSpec.PTrie :=
  ((Fv r τ v).upsert NearSpecV3.keyBwState st).getD (.hash [])

theorem Tf_upsert (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {τ : Nat} (hτ : τ < p.sched.length) (hK : τ ≤ p.hdr.K) (st : NearSpec.Bytes)
    {v : Nat → NearSpec.Bytes} (hv : LenOk r v) :
    (Fv r τ v).upsert NearSpecV3.keyBwState st = some (Tf r τ st v) := by
  have L := trieLink_of hp hsz hH T W
  obtain ⟨Q, hQ⟩ := LinkPartial.PTrie.upsert_of_find (Fv r τ v) NearSpecV3.keyBwState st
    (Fv_wf W L hK hv) (by decide) (Fv_find_key hp hsz hH T W hτ hK v)
  unfold Tf; rw [hQ]; rfl

/-- **`init`**: with the pre bytes the family is the scheduler's output on the pre record tree. -/
theorem Tf_pre (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {τ : Nat} (st : NearSpec.Bytes) {Q : NearSpec.PTrie}
    (hQ : (Fpre r τ).upsert NearSpecV3.keyBwState st = some Q) : Tf r τ st (preV r) = Q := by
  unfold Tf; rw [Fv_pre W, hQ]; rfl

/-- **`get`/`find` through the upsert** at a key `≠ 0x0f` reaching value record `t`. -/
theorem Tf_find (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {τ : Nat} (hτ : τ < p.sched.length) (hK : τ ≤ p.hdr.K) (st : NearSpec.Bytes)
    {key : List Nat} (hne : key ≠ NearSpecV3.keyBwState) {t : Nat}
    (hr : fullReach (Rpost r.nodes r.values) (headAt r.heads τ).rid key = some t)
    (ht : t < r.values.length) {v : Nat → NearSpec.Bytes} (hv : LenOk r v) :
    (Tf r τ st v).find key = some (some (v r.values[t].vid)) ∧
      (Tf r τ st v).get key = some (v r.values[t].vid) := by
  have L := trieLink_of hp hsz hH T W
  have hf : (Tf r τ st v).find key = some (some (v r.values[t].vid)) := by
    rw [NearSpec.PTrie.find_upsert_other _ _ _ _ _ (Fv_wf W L hK hv) (by decide) hne
      (Tf_upsert hp hsz hH T W hτ hK st hv)]
    exact Fv_find hr ht v
  exact ⟨hf, LinkRefine.get_of_find hf⟩

/-- **`set` through the upsert** (old and new value of equal length). -/
theorem Tf_set (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {τ : Nat} (hτ : τ < p.sched.length) (hK : τ ≤ p.hdr.K) (st : NearSpec.Bytes)
    {key : List Nat} (hne : key ≠ NearSpecV3.keyBwState) {t : Nat}
    (hr : fullReach (Rpost r.nodes r.values) (headAt r.heads τ).rid key = some t)
    (ht : t < r.values.length) {v : Nat → NearSpec.Bytes} (hv : LenOk r v) {b : NearSpec.Bytes}
    (hb : (v r.values[t].vid).length = b.length) :
    (Tf r τ st v).set key b = some (Tf r τ st (fun k => if k = r.values[t].vid then b else v k)) := by
  have L := trieLink_of hp hsz hH T W
  have hv' : LenOk r (fun k => if k = r.values[t].vid then b else v k) := by
    intro k
    by_cases e : k = r.values[t].vid
    · subst e; show (if r.values[t].vid = r.values[t].vid then b else v r.values[t].vid).length = _
      rw [if_pos rfl, ← hb]; exact hv _
    · show (if k = r.values[t].vid then b else v k).length = _
      rw [if_neg e]; exact hv k
  obtain ⟨t12, h1, h2⟩ := ZkFormal.NearV3.PTrie.set_upsert_comm (Fv r τ v) key NearSpecV3.keyBwState b st _ _
    (Fv_wf W L hK hv) hne
    (fun old ho => by rw [Fv_find hr ht v] at ho; cases ho; exact hb)
    (Fv_set W L hr ht v b) (Tf_upsert hp hsz hH T W hτ hK st hv)
  rw [Tf_upsert hp hsz hH T W hτ hK st hv'] at h1
  cases h1
  exact h2

/-- **`hpost`**: at an assignment agreeing with the post value records on instance `0`, the family
(upserted by the scheduler's output state) has the ups post root of instance `0`, i.e. `x.post 0`. -/
theorem Tf_post (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {x : ExtV3} (hxh : x.heads = xHeads (r.ups.map upsE))
    (h0 : 0 < p.sched.length) {o : NearSpecV3.Scheduler.Output}
    (ho : NearSpecV3.Scheduler.runCore p.sched[0] (Sched.prevOf tr T_CODEC 0) = some o)
    {v : Nat → NearSpec.Bytes} (hv : LenOk r v)
    (hagree : ∀ e ∈ r.values, valTau r.nodes e.vid = 0 →
      v e.vid = if wrote r.nodes e.vid then toB (LinkVPost.pnOf r.accts e.vid) else toB e.bytes) :
    (Tf r 0 (schedOut o).state v).hashOf = x.post 0 := by
  have L := trieLink_of hp hsz hH T W
  have hK : 0 ≤ p.hdr.K := Nat.zero_le _
  -- `Fv r 0 v` is the post record tree of instance `0`
  have hd := dag_v W L hK hv
  have hFv : Fv r 0 v = fullTree (Rpost r.nodes r.values)
      (Vpost r.nodes r.values (fun i => toB (LinkVPost.pnOf r.accts i))) (headAt r.heads 0).rid := by
    apply fullTree_vals hd ?_ hd.root_inst
    intro n nr hnr ht i hi
    obtain ⟨vr, hvr, hvt⟩ := hd.vals n nr hnr ht i hi
    simp only [valsBy, List.getElem?_map] at hvr
    cases he : r.values[i]? with
    | none => rw [he] at hvr; cases hvr
    | some e =>
      rw [he] at hvr; cases hvr
      have hi' : i < r.values.length := (List.getElem?_eq_some_iff.mp he).1
      have he' : r.values[i] = e := (List.getElem?_eq_some_iff.mp he).2
      rw [valOf_valsBy v hi', he', hagree e (List.mem_of_getElem? he) hvt]
      simp [valOf, Vpost, valsPost, he]
  -- the ups entry of instance `0`
  obtain ⟨f, m, fc, -, -, -, -, -, -, -, -, -, H⟩ := LinkSchedCore.schedCore_v3 hp hsz hH T W h0
  obtain ⟨hrun, -⟩ := H
  have e := Option.some.inj (ho.symm.trans hrun)
  obtain ⟨sv, rfl, -, U⟩ := LinkSched.upsLink_holds hp hsz hH T W
  obtain ⟨⟨Q, hQ, -, hQpost, -, -⟩, -⟩ := U 0 hK
  have hQ' : (fullTree (Rpost r.nodes r.values)
      (Vpost r.nodes r.values (fun i => toB (LinkVPost.pnOf r.accts i))) (headAt r.heads 0).rid).upsert
        NearSpecV3.keyBwState (schedOut o).state = some Q := by rw [e]; exact hQ
  have hT := Tf_upsert hp hsz hH T W h0 hK (schedOut o).state hv
  rw [hFv, hQ'] at hT
  cases hT
  rw [post_xHeads hxh (L.chain.ups_mem 0 hK), hQpost]

end Key

end LinkTrieFam

end ZkFormal.NearV3.Assembly
