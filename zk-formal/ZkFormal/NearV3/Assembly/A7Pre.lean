import ZkFormal.NearV3.Assembly.A7Post
import ZkFormal.NearV3.Link.Post3Occ
import ZkFormal.NearV3.Assembly.A9Air

/-!
# ZkFormal.NearV3.Assembly.A7Pre — (B) of `A7RecordBound`: the pre record trees

Generic (records `ns`, values `V`, a ranked rooted DAG `hd : RootedDagR ns V τ root rk`):

* `U_full`: `U (fullTree n) = |nodeEnc (fullTree n)| + ow n + Σ_{node kids c} U (fullTree c)`
  (`ow n` = the own value bytes of record `n`);
* `pc3_fuel`: the path counts `pc3 ns m f n` do not depend on the fuel `f > mu n`;
* **`U_pc`**: `U (fullTree n) = Σ_m pc3 ns m |ns| n · w m` for a weight `w` equal to
  `|nodeEnc (fullTree m)| + ow m` on the instance;
* `pc_inst`: paths stay in the instance.
-/

namespace ZkFormal.NearV3.Assembly

namespace A7Pre

open NearSpec NearSpecV3 ZkFormal.NearV3 TrieA7Post

/-- Own value bytes of a record. -/
def ow (V : List ValRec3) (nr : NodeRec3) : Nat := (nr.node.vids.map fun i => (valOf V i).length).sum

theorem U_hash (h : Bytes) : unfoldedBytesT (.hash h) = 0 := by
  simp [unfoldedBytesT, NearSpecV3.occs, NearSpecV3.valsOf]

theorem UK_kidsOf3 (g : Nat → PTrie) : ∀ kids,
    UK (kidsOf3 g kids) = kOcc (fun c => unfoldedBytesT (g c)) kids
  | [] => by simp [kidsOf3, kOcc, UK, NearSpecV3.kOccs]
  | .none :: r => by simp only [kidsOf3, kOcc, UK_none]; exact UK_kidsOf3 g r
  | .hash h :: r => by simp only [kidsOf3, kOcc, UK_some, U_hash, Nat.zero_add]; exact UK_kidsOf3 g r
  | .node c :: r => by simp only [kidsOf3, kOcc, UK_some]; rw [UK_kidsOf3 g r]

theorem kOcc_congr {g g' : Nat → Nat} : ∀ kids, (∀ c, Kid3.node c ∈ kids → g c = g' c) →
    kOcc g kids = kOcc g' kids
  | [], _ => rfl
  | .none :: r, h => by simp only [kOcc]; exact kOcc_congr r (fun c hc => h c (List.mem_cons_of_mem _ hc))
  | .hash _ :: r, h => by simp only [kOcc]; exact kOcc_congr r (fun c hc => h c (List.mem_cons_of_mem _ hc))
  | .node c :: r, h => by
    simp only [kOcc]
    rw [h c (List.mem_cons_self ..), kOcc_congr r (fun c hc => h c (List.mem_cons_of_mem _ hc))]

theorem sum_add' (l : List Nat) (a b : Nat → Nat) :
    (l.map fun m => a m + b m).sum = (l.map a).sum + (l.map b).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_zero' (l : List Nat) : (l.map fun _ => (0 : Nat)).sum = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]

theorem sum_kOcc (G : Nat → Nat → Nat) (w : Nat → Nat) (M : List Nat) : ∀ kids,
    (M.map fun m => kOcc (G m) kids * w m).sum = kOcc (fun c => (M.map fun m => G m c * w m).sum) kids
  | [] => by simp only [kOcc, Nat.zero_mul]; exact sum_zero' M
  | .none :: r => by simp only [kOcc]; exact sum_kOcc G w M r
  | .hash _ :: r => by simp only [kOcc]; exact sum_kOcc G w M r
  | .node c :: r => by
    simp only [kOcc, Nat.add_mul]
    rw [sum_add', sum_kOcc G w M r]

theorem kOcc_pos {g : Nat → Nat} : ∀ kids, 0 < kOcc g kids → ∃ c, Kid3.node c ∈ kids ∧ 0 < g c
  | [], h => by simp [kOcc] at h
  | .none :: r, h => by
    simp only [kOcc] at h
    obtain ⟨c, hc, hp⟩ := kOcc_pos r h; exact ⟨c, List.mem_cons_of_mem _ hc, hp⟩
  | .hash _ :: r, h => by
    simp only [kOcc] at h
    obtain ⟨c, hc, hp⟩ := kOcc_pos r h; exact ⟨c, List.mem_cons_of_mem _ hc, hp⟩
  | .node c :: r, h => by
    simp only [kOcc] at h
    by_cases hc : 0 < g c
    · exact ⟨c, List.mem_cons_self .., hc⟩
    · obtain ⟨c', hc', hp⟩ := kOcc_pos (g := g) r (by omega); exact ⟨c', List.mem_cons_of_mem _ hc', hp⟩

theorem sum_ite_eq (w : Nat → Nat) : ∀ (L n : Nat), n < L →
    ((List.range L).map fun m => (if n = m then 1 else 0) * w m).sum = w n
  | 0, _, h => by omega
  | L + 1, n, h => by
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    by_cases e : n = L
    · subst e
      have : ((List.range n).map fun m => (if n = m then 1 else 0) * w m).sum = 0 := by
        have hz : ∀ y ∈ List.range n, (if n = y then 1 else 0) * w y = 0 := by
          intro y hy; simp [show n ≠ y by have := List.mem_range.mp hy; omega]
        rw [List.map_congr_left hz]; exact sum_zero' _
      rw [this]; simp
    · rw [sum_ite_eq w L n (by omega)]; simp [e]

section
variable {ns : List NodeRec3} {V : List ValRec3} {τ root : Nat} {rk : Nat → Nat}

theorem U_full (hd : RootedDagR ns V τ root rk) {n : Nat} {nr : NodeRec3} (hnr : ns[n]? = some nr)
    (ht : nr.tau = τ) :
    unfoldedBytesT (fullTree ns V n) = (NearSpecV3.nodeEnc (fullTree ns V n)).length + ow V nr +
      kOcc (fun c => unfoldedBytesT (fullTree ns V c)) nr.node.kids := by
  rw [Link3.fullTree_unfold_any hd V hnr ht]
  generalize fullTree ns V = g
  unfold ow
  cases nr.node with
  | leaf k v mem =>
    simp only [nodeTree3, U_leaf, Rec3.kids, kOcc, Nat.add_zero]
    cases v with
    | ref len h => simp [slot3, NearSpecV3.slotVal, Rec3.vids]
    | val i => simp [slot3, NearSpecV3.slotVal, Rec3.vids]
  | ext k kid mem =>
    simp only [nodeTree3, U_ext, Rec3.kids, Rec3.vids, List.map_nil, List.sum_nil, Nat.add_zero]
    cases kid with
    | none => simp [kidTree3, kOcc, U_hash]
    | hash h => simp [kidTree3, kOcc, U_hash]
    | node c => simp [kidTree3, kOcc]
  | branch v kids mem =>
    simp only [nodeTree3, U_branch, Rec3.kids, UK_kidsOf3]
    congr 2
    cases v with
    | none => simp [NearSpecV3.optSlotVal, Rec3.vids]
    | some s =>
      cases s with
      | ref len h => simp [slot3, NearSpecV3.optSlotVal, NearSpecV3.slotVal, Rec3.vids]
      | val i => simp [slot3, NearSpecV3.optSlotVal, NearSpecV3.slotVal, Rec3.vids]

theorem pc3_fuel (hd : RootedDagR ns V τ root rk) (m : Nat) :
    ∀ n, InInst ns τ n → ∀ f f', mu ns τ rk n < f → mu ns τ rk n < f' → pc3 ns m f n = pc3 ns m f' n := by
  apply dag_inductionR hd
  intro n nr hnr ht ih f f' h1 h2
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  obtain ⟨g', rfl⟩ : ∃ g', f' = g' + 1 := ⟨f' - 1, by omega⟩
  rw [pc3_succ, pc3_succ, hnr]
  simp only
  congr 1
  apply kOcc_congr
  intro c hc
  obtain ⟨hlt, hcI⟩ := hd.child n nr hnr ht c hc
  have := mu_child (ns := ns) hlt hcI
  exact ih c hc g g' (by omega) (by omega)

theorem pc_inst (hd : RootedDagR ns V τ root rk) (m : Nat) :
    ∀ f n, InInst ns τ n → 0 < pc3 ns m f n → InInst ns τ m := by
  intro f
  induction f with
  | zero => intro n _ h; simp [pc3] at h
  | succ f ih =>
    intro n hn h
    obtain ⟨nr, hnr, ht⟩ := hn
    rw [pc3_succ, hnr] at h
    simp only at h
    by_cases e : n = m
    · subst e; exact ⟨nr, hnr, ht⟩
    · rw [if_neg e, Nat.zero_add] at h
      obtain ⟨c, hc, hp⟩ := kOcc_pos _ h
      exact ih c (hd.child n nr hnr ht c hc).2 hp

/-- **`U` of a record tree as a path-weighted sum.** -/
theorem U_pc (hd : RootedDagR ns V τ root rk) (w : Nat → Nat)
    (hw : ∀ m nr, ns[m]? = some nr → nr.tau = τ →
      w m = (NearSpecV3.nodeEnc (fullTree ns V m)).length + ow V nr) :
    ∀ n, InInst ns τ n →
      unfoldedBytesT (fullTree ns V n) = ((List.range ns.length).map fun m => pc3 ns m ns.length n * w m).sum := by
  apply dag_inductionR hd
  intro n nr hnr ht ih
  have hn : InInst ns τ n := ⟨nr, hnr, ht⟩
  have hmu := mu_lt_length (rk := rk) hn
  obtain ⟨g, hg⟩ : ∃ g, ns.length = g + 1 := ⟨ns.length - 1, by omega⟩
  have hpc : ∀ m, pc3 ns m ns.length n = (if n = m then 1 else 0) + kOcc (pc3 ns m g) nr.node.kids := by
    intro m; rw [hg, pc3_succ, hnr]
  rw [U_full hd hnr ht]
  simp only [hpc, Nat.add_mul]
  rw [sum_add']
  rw [sum_ite_eq w _ n (by have := hn; obtain ⟨_, h1, _⟩ := this; exact (List.getElem?_eq_some_iff.mp h1).1),
    sum_kOcc, hw n nr hnr ht]
  congr 1
  apply kOcc_congr
  intro c hc
  obtain ⟨hlt, hcI⟩ := hd.child n nr hnr ht c hc
  have := mu_child (ns := ns) hlt hcI
  rw [ih c hc]
  apply congrArg List.sum
  apply List.map_congr_left
  intro m _
  rw [pc3_fuel hd m c hcI g ns.length (by omega) (by omega)]

end

/-! ## Generic counting -/

theorem nodup_flatMap' {α : Type} (g : Nat → List α) : ∀ (l : List Nat), l.Nodup → (∀ a ∈ l, (g a).Nodup) →
    (∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ x ∈ g a, x ∉ g b) → (l.flatMap g).Nodup
  | [], _, _, _ => by simp
  | a :: l, hl, hg, hd => by
    rw [List.flatMap_cons]
    refine List.nodup_append.mpr ⟨hg a (List.mem_cons_self ..),
      nodup_flatMap' g l (List.nodup_cons.mp hl).2 (fun b hb => hg b (List.mem_cons_of_mem _ hb))
        (fun b hb c hc hbc => hd b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc) hbc), ?_⟩
    intro x hx y hy hxy
    subst hxy
    obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp hy
    have hab : a ≠ b := fun e => (List.nodup_cons.mp hl).1 (e ▸ hb)
    exact hd a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb) hab x hx hxb

theorem nodup_sum_le' (g : Nat → Nat) {S : List Nat} (hS : S.Nodup) (H : Nat) (hz : ∀ x ∈ S, H ≤ x → g x = 0) :
    (S.map g).sum ≤ ((List.range H).map g).sum := by
  have e : (S.map g).sum = ((S.filter (· < H)).map g).sum := by
    induction S with
    | nil => rfl
    | cons x S ih =>
      have ih' := ih (List.nodup_cons.mp hS).2 (fun y hy => hz y (List.mem_cons_of_mem _ hy))
      by_cases hx : x < H
      · simp [List.filter_cons, hx, ih']
      · simp [List.filter_cons, hx, ih', hz x (List.mem_cons_self ..) (by omega)]
  rw [e]
  exact A9Air.nodup_sum_le (hS.filter _) (fun x hx => by simpa using (List.mem_filter.mp hx).2) g

theorem vids_nodup (r : Rec3) : r.vids.Nodup := by
  cases r with
  | leaf k v m => cases v <;> simp [Rec3.vids]
  | ext => simp [Rec3.vids]
  | branch v kids m =>
    cases v with
    | none => simp [Rec3.vids]
    | some s => cases s <;> simp [Rec3.vids]

theorem sum_swap (F : Nat → Nat → Nat) (A B : List Nat) :
    (A.map fun a => (B.map fun b => F a b).sum).sum = (B.map fun b => (A.map fun a => F a b).sum).sum := by
  induction A with
  | nil => simp [sum_zero']
  | cons a A ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [← sum_add']

theorem sum_ite_le (w : Nat) (t : Nat) : ∀ L, ((List.range L).map fun τ => if t = τ then w else 0).sum ≤ w
  | 0 => by simp
  | L + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append]
    have := sum_ite_le w t L
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    by_cases e : t = L
    · subst e
      have : ((List.range t).map fun τ => if t = τ then w else 0).sum = 0 := by
        have hz : ∀ y ∈ List.range t, (if t = y then w else 0) = 0 := by
          intro y hy; simp [show t ≠ y by have := List.mem_range.mp hy; omega]
        rw [List.map_congr_left hz]; exact sum_zero' _
      rw [this]; simp
    · simp [e]; omega

/-! ## (B) on the records -/

section Rec
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Link3

variable {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
  {tr : Trace Fp} {r : V3Records}

abbrev nsR (r : V3Records) : List NodeRec3 := recsOf (vpos (vid0 r.values)) r.nodes
abbrev VR (r : V3Records) : List ValRec3 := valsOf3 r.nodes r.values

/-- The pre record weight of record `m`: serialized bytes plus own value bytes. -/
def wPre (r : V3Records) (m : Nat) : Nat :=
  ((r.nodes.getD m default).v.ser false).length +
    ow (VR r) ((nsR r).getD m default)

/-- **(B)** The pre record trees of all instances are within the record bytes. -/
theorem pre_le (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ((List.range (p.hdr.K + 1)).map fun τ => unfoldedBytesT (LinkImplicit.Fpre r τ)).sum ≤
      A7Assemble.recNode r + A7Assemble.recVal r := by
  have L := trieLink_of hp hsz hH T W
  have hw := W.nodes; have hhw := W.heads; have hvw := W.values
  have hb := L.parent; have hvb := L.vparent
  have H := L.sha
  have hlen : (nsR r).length = r.nodes.length := recsOf_length _ _
  -- path counts are at most one
  have hpc : ∀ m f n, pc3 (nsR r) m f n ≤ 1 := by
    apply pc_le_one (rk := rkOf r.nodes)
    · intro r' nr c hr hc
      obtain ⟨hr', rfl⟩ := recsOf_some hr
      obtain ⟨l, rr, pre, po, hk⟩ := (kids_toRec3 _ _ c).mp hc
      obtain ⟨hcl, -, hdc, -⟩ := kid_depth hw hhw hb hr' hk
      simp only [rkOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr', List.getElem?_eq_getElem hcl,
        Option.getD_some, hdc]
      omega
    · intro m r1 r2 nr nr' hr hr' hc hc'
      obtain ⟨h1, rfl⟩ := recsOf_some hr
      obtain ⟨h2, rfl⟩ := recsOf_some hr'
      apply Classical.byContradiction; intro hne
      have := (kid_slots hw hb (vpos (vid0 r.values)) (n := m)).2 r1 r2 h1 h2 hne
      simp only at hc hc'; omega
    · intro m r1 nr hr
      obtain ⟨h1, rfl⟩ := recsOf_some hr
      exact (kid_slots hw hb (vpos (vid0 r.values)) (n := m)).1 r1 h1
  -- one instance
  have hinst : ∀ τ, τ ≤ p.hdr.K → unfoldedBytesT (LinkImplicit.Fpre r τ) ≤
      ((List.range (nsR r).length).map fun m => if ((nsR r).getD m default).tau = τ then wPre r m else 0).sum := by
    intro τ hτ
    obtain ⟨hh, htau⟩ := L.chain.head_mem τ hτ
    have hbytes := rec_bytes hw hhw hvw hb H
    have hd := rootedDag3 hw hhw hvw hb hvb (vlen_le hvw) hbytes hh
    rw [htau] at hd
    have hU := U_pc hd (wPre r) (fun m nr hnr ht => by
      have hm : InInst (nsR r) τ m := ⟨nr, hnr, ht⟩
      obtain ⟨hn, henc, -⟩ := enc_fullTree hd hw hbytes
        (fun p hp c l r pre po hk => by
          obtain ⟨hc, -, he⟩ := kid_sha hw hhw hvw hb H hp hk; exact ⟨hc, he⟩)
        (fun p hp i l pre po w hv => val_sha hw hhw hvw hvb H hp hv) m hm
      unfold wPre
      rw [← enc_eq, henc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some,
        List.getD_eq_getElem?_getD, hnr, Option.getD_some]
      simp [toB]) _ hd.root_inst
    show unfoldedBytesT (fullTree (nsR r) (VR r) (headAt r.heads τ).rid) ≤ _
    rw [hU]
    apply A9Air.sum_le_sum_range
    intro m hm
    by_cases hp0 : pc3 (nsR r) m (nsR r).length (headAt r.heads τ).rid = 0
    · rw [hp0]; simp
    · have hI := pc_inst hd m (nsR r).length _ hd.root_inst (Nat.pos_of_ne_zero hp0)
      obtain ⟨nr, hnr, ht⟩ := hI
      have e : ((nsR r).getD m default).tau = τ := by
        rw [List.getD_eq_getElem?_getD, hnr]; exact ht
      rw [if_pos e]
      have := hpc m (nsR r).length (headAt r.heads τ).rid
      have : pc3 (nsR r) m (nsR r).length (headAt r.heads τ).rid = 1 := by omega
      rw [this, Nat.one_mul]
      exact Nat.le_refl _
  -- all instances
  have h1 : ((List.range (p.hdr.K + 1)).map fun τ => unfoldedBytesT (LinkImplicit.Fpre r τ)).sum ≤
      ((List.range (p.hdr.K + 1)).map fun τ =>
        ((List.range (nsR r).length).map fun m => if ((nsR r).getD m default).tau = τ then wPre r m else 0).sum).sum :=
    A9Air.sum_le_sum_range (fun τ hτ => hinst τ (by omega))
  rw [sum_swap] at h1
  have h2 : ((List.range (nsR r).length).map fun m =>
      ((List.range (p.hdr.K + 1)).map fun τ => if ((nsR r).getD m default).tau = τ then wPre r m else 0).sum).sum ≤
      ((List.range (nsR r).length).map (wPre r)).sum :=
    A9Air.sum_le_sum_range (fun m _ => sum_ite_le _ _ _)
  -- the weights
  have h3 : ((List.range (nsR r).length).map (wPre r)).sum =
      A7Assemble.recNode r + ((List.range (nsR r).length).map fun m =>
        ow (VR r) ((nsR r).getD m default)).sum := by
    unfold wPre A7Assemble.recNode
    rw [sum_add', hlen]
  -- own values: each value id in at most one record
  have h4 : ((List.range (nsR r).length).map fun m => ow (VR r) ((nsR r).getD m default)).sum ≤ A7Assemble.recVal r := by
    have e1 : ((List.range (nsR r).length).map fun m => ow (VR r) ((nsR r).getD m default)).sum =
        (((List.range (nsR r).length).flatMap fun m => ((nsR r).getD m default).node.vids).map
          fun i => (valOf (VR r) i).length).sum := by
      rw [A9Air.sum_flatMap']
      rfl
    rw [e1]
    have hnd : ((List.range (nsR r).length).flatMap fun m => ((nsR r).getD m default).node.vids).Nodup := by
      apply nodup_flatMap' _ _ List.nodup_range (fun m _ => vids_nodup _)
      intro a ha b hb hab j hja hjb
      have ha' : a < (nsR r).length := List.mem_range.mp ha
      have hb' : b < (nsR r).length := List.mem_range.mp hb
      have hra : (nsR r)[a]? = some ((nsR r).getD a default) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha']; rfl
      have hrb : (nsR r)[b]? = some ((nsR r).getD b default) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb']; rfl
      apply hab
      obtain ⟨h1, e1⟩ := recsOf_some hra
      obtain ⟨h2, e2⟩ := recsOf_some hrb
      rw [e1] at hja; rw [e2] at hjb
      obtain ⟨vid, l, pre, po, w, hv, rfl⟩ := vids_toRec3 _ _ hja
      obtain ⟨vid', l', pre', po', w', hv', he⟩ := vids_toRec3 _ _ hjb
      have hlen' := vlen_le hvw
      obtain ⟨t, ht, hti, -⟩ := val_link hw hvw hvb h1 hv
      obtain ⟨t', ht', hti', -⟩ := val_link hw hvw hvb h2 hv'
      have e1 := vpos_at hvw hlen' ht
      have e2 := vpos_at hvw hlen' ht'
      rw [hti] at e1; rw [hti'] at e2
      have htt : t = t' := by rw [← e1, ← e2, he]
      subst htt
      rw [hti] at hti'; subst hti'
      exact val_unique hw hvw hvb hlen' h1 h2 hv hv'
    refine Nat.le_trans (nodup_sum_le' _ hnd r.values.length (fun x _ hx => ?_)) ?_
    · simp only [VR, valOf, valsOf3, List.getElem?_map, List.getElem?_eq_none hx]; rfl
    · unfold A7Assemble.recVal
      apply Nat.le_of_eq
      apply congrArg List.sum
      apply List.map_congr_left
      intro t ht
      have ht' := List.mem_range.mp ht
      simp only [valOf, valsOf3, List.getElem?_map, List.getElem?_eq_getElem ht', Option.map_some,
        Option.getD_some, toB, List.length_map, List.getD_eq_getElem?_getD]
      have hsh := W.values.shape _ (List.getElem_mem ht')
      cases hz : r.values[t].vz
      · exact (hsh.2 hz).1
      · rw [(hsh.1 hz).1, (hsh.1 hz).2]; rfl
  omega

end Rec

end A7Pre

end ZkFormal.NearV3.Assembly

/-! # `A7RecordBound` from (E) -/

namespace ZkFormal.NearV3.Assembly

namespace A7Pre

open NearSpec NearSpecV3 Render.UpsGen ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.NearV3

/-- **(E), segment level** (open): for every `upsV3` segment `s` (instance `τ = (upsE s).tau`) and the
run of `traceUpsert` on the post record tree `Tpost r τ` at `[0,15]` with the scheduler value
`sv τ`: the segment's value/node-part rows pay for the new value and the output parts, and its
`RPL` / `RPLV` names weigh at most the replaced sources / the overwritten value. -/
def UpsSegMatch (tr : Trace Fp) (r : V3Records) : Prop :=
  ∀ s ∈ r.ups, ∀ run, traceUpsert (A7Native.Tpost r (UpsRows.upsE s).tau) UpsSpec.key
      (Link3.toB (Sched.svOf tr T_CODEC (UpsRows.upsE s).tau)) = some run →
    outputByteCharge run + (Link3.toB (Sched.svOf tr T_CODEC (UpsRows.upsE s).tau)).length ≤ s.a7S ∧
    (((s.a7Rpl).map ZkFormal.Near.Msg.toFp).map (A7Assemble.wN r)).sum ≤ TrieA7Repl.replacedCharge run ∧
    (((s.a7Rplv).map ZkFormal.Near.Msg.toFp).map (A7Assemble.wV r)).sum ≤ TrieA7Repl.oldValCharge run

section
variable {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
  {tr : Trace Fp} {r : V3Records}

/-- **`A7RecordBound` from (E)**: (B) `pre_le`, (C)+(D) `A7Post.qrec_run`, `A7Assemble.recordBound_of`. -/
theorem recordBound_of_match (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (hE : UpsSegMatch tr r) : A7Native.A7RecordBound tr r p.hdr.K := by
  have L := trieLink_of hp hsz hH T W
  refine A7Assemble.recordBound_of hH T W L.chain.ups_count (pre_le hp hsz hH T W) ?_
  intro s hs
  have hτ : (UpsRows.upsE s).tau ≤ p.hdr.K :=
    (L.chain.ups_all _ (List.mem_map_of_mem hs)).1
  obtain ⟨run, hr, -, hle⟩ := A7Post.qrec_run hp hsz hH T W hτ
  obtain ⟨e1, e2, e3⟩ := hE s hs run hr
  exact ⟨run, hle, e1, e2, e3⟩


/-- **`RestFieldsV3.unfoldedBytes` from (E)** (with the `shape` and `source.applied` fields). -/
theorem unfoldedBytes_of_match (hp : NearSpecV3.prepD0 cb h = .ok p) {k : NearSpecV3.WalkD0}
    (hw : NearSpecV3.walkD0 cb = .ok k)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (d : List DictionaryEntryV3) (hs : V3.D0Shape (stateWitnessOfV3 k (xOf r d)))
    (happ : appliedReceipts k (stateWitnessOfV3 k (xOf r d)) = (xOf r d).applied)
    (hE : UpsSegMatch tr r) :
    unfoldBytes cb (witnessOfV3 k (xOf r d)) ≤ UnfoldA7.B0 :=
  A7Native.unfoldedBytes_of_record hp hw hsz hH W T d hs happ (recordBound_of_match hp hsz hH T W hE)

end

end A7Pre

end ZkFormal.NearV3.Assembly
