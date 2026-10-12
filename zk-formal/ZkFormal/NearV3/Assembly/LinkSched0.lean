import ZkFormal.NearV3.Assembly.LinkImplicit

/-!
# ZkFormal.NearV3.Assembly.LinkSched0 — the scheduler step on the pre record tree

`sched_step` runs the scheduler on the record tree with the acct **post** values (`Vpost`).  For
the main instance the native order is scheduler first (on the **pre** values), so the receipt
core needs `schedStep prims ctx (Fpre r 0) = .ok (mid, so)`.  The scheduler reads `0x0f` and
upserts it; the `0x0f` lookup does not depend on the acct writes:

* `find_none_vals` — an absent lookup (`some none`) of a record tree does not depend on its
  value records;
* `pre_find_key` — `(Fpre r τ).find 0x0f = some (prevOf τ)`: a found value is the value record the
  lookup reaches (`find_reach`, `reach_find`); a written record has a 72-byte post value (or none),
  the codec's value has `37 + 24·NN` bytes, so the reached record is not written;
* **`sched_pre`** — the scheduler step of instance `τ` on `Fpre r τ` (for every `τ ≤ K`).
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkSched0

open ZkFormal.NearV3 ZkFormal.NearV3.Link3 ZkFormal.NearV3.UpsRows ZkFormal.NearV3.Sched LinkImplicit

/-! ## Absent lookups do not depend on the values -/

section Shape
variable {ns : List NodeRec3}

theorem kids_find_none_inv (g : Nat → NearSpec.PTrie) (rest : List Nat) :
    ∀ (kids : List Kid3) (j : Nat), NearSpec.Kids.find (kidsOf3 g kids) j rest = some none →
      (∃ c, kids[j]? = some (Kid3.node c) ∧ (g c).find rest = some none) ∨
        kids[j]? = some Kid3.none ∨ kids.length ≤ j
  | [], _, _ => .inr (.inr (by simp))
  | kd :: r, 0, h => by
    cases kd with
    | none => exact .inr (.inl rfl)
    | hash _ => simp [kidsOf3, NearSpec.Kids.find, NearSpec.PTrie.find] at h
    | node c => exact .inl ⟨c, by simp, by simpa [kidsOf3, NearSpec.Kids.find] using h⟩
  | kd :: r, j + 1, h => by
    have key : NearSpec.Kids.find (kidsOf3 g r) j rest = some none := by
      cases kd <;> simpa [kidsOf3, NearSpec.Kids.find] using h
    rcases kids_find_none_inv g rest r j key with ⟨c, hc, hf⟩ | hn | hl
    · exact .inl ⟨c, by simpa using hc, hf⟩
    · exact .inr (.inl (by simpa using hn))
    · exact .inr (.inr (by simp; omega))

theorem kids_find_none_mk (g : Nat → NearSpec.PTrie) (rest : List Nat) :
    ∀ (kids : List Kid3) (j : Nat),
      ((∃ c, kids[j]? = some (Kid3.node c) ∧ (g c).find rest = some none) ∨
        kids[j]? = some Kid3.none ∨ kids.length ≤ j) →
      NearSpec.Kids.find (kidsOf3 g kids) j rest = some none
  | [], _, _ => by simp [kidsOf3, NearSpec.Kids.find]
  | kd :: r, 0, h => by
    rcases h with ⟨c, hc, hf⟩ | hn | hl
    · simp at hc; subst hc; simpa [kidsOf3, NearSpec.Kids.find] using hf
    · simp at hn; subst hn; simp [kidsOf3, NearSpec.Kids.find]
    · simp at hl
  | kd :: r, j + 1, h => by
    have key := kids_find_none_mk g rest r j (by
      rcases h with ⟨c, hc, hf⟩ | hn | hl
      · exact .inl ⟨c, by simpa using hc, hf⟩
      · exact .inr (.inl (by simpa using hn))
      · exact .inr (.inr (by simp at hl; omega)))
    cases kd <;> simpa [kidsOf3, NearSpec.Kids.find] using key

/-- **An absent lookup does not depend on the value records.** -/
theorem find_none_vals (V₁ V₂ : List ValRec3) : ∀ f n key,
    (treeOf3 ns V₁ f n).find key = some none → (treeOf3 ns V₂ f n).find key = some none := by
  intro f
  induction f with
  | zero => intro n key h; simp [treeOf3, NearSpec.PTrie.find] at h
  | succ f ih =>
    intro n key h
    simp only [treeOf3] at h ⊢
    cases hn : ns[n]? with
    | none => rw [hn] at h; simp [NearSpec.PTrie.find] at h
    | some nr =>
      rw [hn] at h; simp only at h ⊢
      generalize nr.node = r at h ⊢
      cases r with
      | leaf k s m =>
        cases s with
        | ref =>
          simp only [nodeTree3, slot3, NearSpec.PTrie.find, NearSpec.Slot.get] at h ⊢
          split at h
          · simp at h
          · rename_i hk; simp [hk]
        | val j =>
          simp only [nodeTree3, slot3, NearSpec.PTrie.find, NearSpec.Slot.get] at h ⊢
          split at h
          · simp at h
          · rename_i hk; simp [hk]
      | ext k kid m =>
        cases kid with
        | node c =>
          simp only [nodeTree3, kidTree3, NearSpec.PTrie.find] at h ⊢
          split at h
          · rename_i hp; simp only [hp, ↓reduceIte]; exact ih c _ h
          · rename_i hp; simp [hp]
        | none =>
          simp only [nodeTree3, kidTree3, NearSpec.PTrie.find] at h ⊢
          split at h
          · simp at h
          · rename_i hp; simp [hp]
        | hash _ =>
          simp only [nodeTree3, kidTree3, NearSpec.PTrie.find] at h ⊢
          split at h
          · simp at h
          · rename_i hp; simp [hp]
      | branch sv kids m =>
        cases key with
        | nil =>
          cases sv with
          | none => simp [nodeTree3, NearSpec.PTrie.find]
          | some s =>
            cases s with
            | ref => simp [nodeTree3, slot3, NearSpec.PTrie.find, NearSpec.Slot.get] at h
            | val j => simp [nodeTree3, slot3, NearSpec.PTrie.find, NearSpec.Slot.get] at h
        | cons j rest =>
          simp only [nodeTree3, NearSpec.PTrie.find] at h ⊢
          apply kids_find_none_mk
          rcases kids_find_none_inv _ rest kids j h with ⟨c, hc, hf⟩ | hn | hl
          · exact .inl ⟨c, hc, ih c rest hf⟩
          · exact .inr (.inl hn)
          · exact .inr (.inr hl)

end Shape

/-! ## The `0x0f` lookup on the pre record tree -/

theorem prevOf_len {tr : Trace Fp} {tc τ : Nat} {b : NearSpec.Bytes} (h : prevOf tr tc τ = some b) :
    ∃ N, b.length = 37 + 24 * N := by
  unfold prevOf pvOf at h
  split at h
  · split at h
    · simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨_, by simp; rfl⟩
    · simp at h
  · simp at h

/-- A written value record's post bytes have 72 bytes. -/
theorem pn_len {pub : List Fp} {r : V3Records} (W : V3RecordsWf pub r) {i : Nat}
    (ha : ∃ a ∈ r.accts, a.k = i) : (toB (LinkVPost.pnOf r.accts i)).length = 72 := by
  obtain ⟨a, ha, hk⟩ := ha
  unfold LinkVPost.pnOf
  cases hf : r.accts.find? (fun a => a.k == i) with
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf a ha
    simp [hk] at this
  | some a' =>
    have ha' := List.mem_of_find?_eq_some hf
    obtain ⟨h1, h2, -, -⟩ := LinkVPost.acct_wf W ha'
    simp [toB_len, h1, h2]

section Run
variable {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
  {tr : Trace Fp} {r : V3Records}

/-- **The `0x0f` lookup on the pre record tree** is the codec's previous value. -/
theorem pre_find_key (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {τ : Nat} (hτ : τ < p.sched.length) (hK : τ ≤ p.hdr.K) :
    (Fpre r τ).find UpsSpec.key = some (prevOf tr T_CODEC τ) := by
  have hpost := LinkVBytes.codec_find hp hsz hH T W hτ hK
  unfold fullTree at hpost
  show (treeOf3 (Rpost r.nodes r.values) (valsOf3 r.nodes r.values) (Rpost r.nodes r.values).length
    (headAt r.heads τ).rid).find UpsSpec.key = _
  cases hpv : prevOf tr T_CODEC τ with
  | none =>
    rw [hpv] at hpost
    exact find_none_vals _ _ _ _ _ hpost
  | some b =>
    rw [hpv] at hpost
    obtain ⟨j, hj, hvj⟩ := find_reach _ _ _ _ hpost
    rw [reach_find (valsOf3 r.nodes r.values) _ _ _ hj, ← hvj]
    congr 2
    unfold valOf Vpost valsPost valsOf3
    cases he : r.values[j]? with
    | none => simp [he]
    | some e =>
      simp only [List.getElem?_map, he, Option.map_some, Option.getD_some]
      cases hw : wrote r.nodes e.vid with
      | false => simp
      | true =>
        exfalso
        have hm := List.mem_of_getElem? he
        have hacc := LinkVBytes.wrote_acct hH T W (W.values.canon _ hm).1 hw
        have h72 := pn_len W hacc
        obtain ⟨N, hN⟩ := prevOf_len hpv
        have hb : valOf (Vpost r.nodes r.values (fun i => toB (LinkVPost.pnOf r.accts i))) j = b := hvj
        unfold valOf Vpost valsPost at hb
        simp only [List.getElem?_map, he, Option.map_some, Option.getD_some, hw, ite_true] at hb
        rw [hb] at h72
        omega

/-- **The scheduler step of instance `τ` on the pre record tree** (for the main instance: the
`sched` field of the receipt core's `MainTrieLink` at `pre := Fpre r 0`). -/
theorem sched_pre (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {τ : Nat} (hτ : τ < p.sched.length) (hK : τ ≤ p.hdr.K) {ctx : NearSpecV3.ApplyCtx}
    (hctx : NearSpecV3.schedPub ctx = some p.sched[τ]) :
    ∃ o Q, NearSpecV3.Scheduler.runCore p.sched[τ] (prevOf tr T_CODEC τ) = some o ∧
      (Fpre r τ).upsert NearSpecV3.keyBwState (schedOut o).state = some Q ∧
      NearSpecV3.schedStep NearSpecV3.prims ctx (Fpre r τ) = .ok (Q, schedOut o) := by
  obtain ⟨f, m, fc, -, -, -, -, -, -, -, -, -, H⟩ := LinkSchedCore.schedCore_v3 hp hsz hH T W hτ
  obtain ⟨hrun, -⟩ := H
  have L := trieLink_of hp hsz hH T W
  have hfind := pre_find_key hp hsz hH T W hτ hK
  rw [← LinkVBytes.keyBwState_eq] at hfind
  obtain ⟨hh, -⟩ := L.chain.head_mem τ hK
  have hd := rootedDag3 W.nodes W.heads W.values L.parent L.vparent (vlen_le W.values)
    (recBytes_of W L) hh
  have hwf : (Fpre r τ).wf = true := fullTree_wfR hd _ hd.root_inst
  obtain ⟨Q, hQ⟩ := LinkPartial.PTrie.upsert_of_find (Fpre r τ) NearSpecV3.keyBwState _ hwf (by decide)
    (by rw [hfind]; simp)
  refine ⟨_, Q, hrun, hQ, schedStep_sound ?_ hctx hrun hQ⟩
  unfold NearSpecV3.readKey
  rw [hfind]

end Run

end LinkSched0

end ZkFormal.NearV3.Assembly
