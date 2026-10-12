import ZkFormal.NearV3.Assembly.A7Assemble
import ZkFormal.NearV3.Rcpt.Candidates.NativeReplayByteSize
import ZkFormal.NearV3.Render.Ups.TreePlan

/-!
# ZkFormal.NearV3.Assembly.A7Post — (C) and (D) of `A7RecordBound`

* `LeTree a b`: same shape, `b`'s revealed values no longer than `a`'s.  `LeTree a b` keeps node
  encoding lengths (`le_node_length`, via `WriteTreePair`), well-formedness (`le_wf`) and does not
  increase unfolded bytes (`le_U`).
* `le_treeOf3`: two value lists with pointwise no longer values give `LeTree` record trees.
* **(C)** `tpost_le`: `LeTree (Fpre r τ) (Tpost r τ)` — written values are no longer than the pre
  values (`LinkVPost.hvpostLen_of`, `val_link`, `vid_small`); hence `U (Tpost r τ) ≤ U (Fpre r τ)` and
  `Tpost r τ` is well formed.
* **(D)** `qrec_run`: for `τ ≤ K` there is a run `traceUpsert (Tpost r τ) key (sv τ) = some run`
  with output `Qrec tr r τ` and
  `U (Qrec tr r τ) + replacedCharge run + oldValCharge run ≤ U (Fpre r τ) + outputByteCharge run + |sv τ|`
  (`TrieA7Repl.traceUpsert_replaced`).
-/

namespace ZkFormal.NearV3.Assembly

namespace A7Post

open NearSpec NearSpecV3 Render.UpsGen TrieA7Post
open ZkFormal.NearV3.Rcpt.Candidates

inductive LeSlot : Slot → Slot → Prop
  | ref (n : Nat) (h : Bytes) : LeSlot (.ref n h) (.ref n h)
  | val {a b : Bytes} (h : b.length ≤ a.length) : LeSlot (.val a) (.val b)

mutual
inductive LeTree : PTrie → PTrie → Prop
  | hash (h : Bytes) : LeTree (.hash h) (.hash h)
  | leaf {a b : Slot} (k : List Nat) (m : Nat) (h : LeSlot a b) : LeTree (.leaf k a m) (.leaf k b m)
  | ext {a b : PTrie} (k : List Nat) (m : Nat) (h : LeTree a b) : LeTree (.ext k a m) (.ext k b m)
  | branch {a b : Option Slot} {cs ds : Kids} (m : Nat) (h : Option.Rel LeSlot a b)
      (hs : LeKids cs ds) : LeTree (.branch a cs m) (.branch b ds m)
inductive LeKids : Kids → Kids → Prop
  | nil : LeKids .nil .nil
  | none {cs ds : Kids} (h : LeKids cs ds) : LeKids (.none cs) (.none ds)
  | some {a b : PTrie} {cs ds : Kids} (h : LeTree a b) (hs : LeKids cs ds) : LeKids (.some a cs) (.some b ds)
end

theorem LeSlot.write {a b : Slot} (h : LeSlot a b) : WriteSlotPair a b := by
  cases h with
  | ref n h => exact .ref n h
  | val _ => exact .val _ _

mutual
theorem LeTree.write : ∀ {a b : PTrie}, LeTree a b → WriteTreePair a b
  | _, _, .hash h => .hash h
  | _, _, .leaf k m h => .leaf k m h.write
  | _, _, .ext k m h => .ext k m h.write
  | _, _, .branch m h hs => .branch m (by cases h with
      | none => exact .none
      | some h => exact .some h.write) hs.write
theorem LeKids.write : ∀ {a b : Kids}, LeKids a b → WriteKidsPair a b
  | _, _, .nil => .nil
  | _, _, .none h => .none h.write
  | _, _, .some h hs => .some h.write hs.write
end

theorem le_node_length {a b : PTrie} (h : LeTree a b) :
    (NearSpecV3.nodeEnc a).length = (NearSpecV3.nodeEnc b).length := by
  rw [← enc_eq, ← enc_eq]
  exact NodePostUpdate.write_node_length h.write

theorem slotOk_le {a b : Slot} (h : LeSlot a b) (ha : slotOk a = true) : slotOk b = true := by
  cases h with
  | ref => exact ha
  | val hl => simp only [slotOk, decide_eq_true_eq] at ha ⊢; omega

theorem slotVal_le {a b : Slot} (h : LeSlot a b) :
    ((NearSpecV3.slotVal b).map List.length).sum ≤ ((NearSpecV3.slotVal a).map List.length).sum := by
  cases h with
  | ref => exact Nat.le_refl _
  | val hl => simp [NearSpecV3.slotVal]; omega

mutual
theorem le_wf : ∀ {a b : PTrie}, LeTree a b → a.wf = true → b.wf = true
  | _, _, .hash _, h => h
  | _, _, .leaf k m hs, h => by
    simp only [PTrie.wf, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨h.1.1.1, slotOk_le hs h.1.1.2⟩, h.1.2⟩, h.2⟩
  | _, _, .ext k m hc, h => by
    simp only [PTrie.wf, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨h.1.1.1, le_wf hc h.1.1.2⟩, h.1.2⟩, h.2⟩
  | _, _, .branch m ho hs, h => by
    simp only [PTrie.wf, Bool.and_eq_true] at h ⊢
    refine ⟨⟨?_, le_kwf hs h.1.2⟩, h.2⟩
    cases ho with
    | none => rfl
    | some hs' => exact slotOk_le hs' h.1.1
theorem le_kwf : ∀ {a b : Kids} {n : Nat}, LeKids a b → Kids.wf a n = true → Kids.wf b n = true
  | _, _, n, .nil, h => h
  | _, _, n, .none hs, h => by
    simp only [Kids.wf, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, le_kwf hs h.2⟩
  | _, _, n, .some hc hs, h => by
    simp only [Kids.wf, Bool.and_eq_true] at h ⊢
    exact ⟨⟨h.1.1, le_wf hc h.1.2⟩, le_kwf hs h.2⟩
end

theorem UK_nil : UK .nil = 0 := by simp [UK, NearSpecV3.kOccs]

mutual
theorem le_U : ∀ {a b : PTrie}, LeTree a b → unfoldedBytesT b ≤ unfoldedBytesT a
  | _, _, .hash _ => Nat.le_refl _
  | _, _, .leaf k m hs => by
    have e := le_node_length (.leaf k m hs)
    rw [U_leaf, U_leaf]
    have := slotVal_le hs
    omega
  | _, _, .ext k m hc => by
    have e := le_node_length (.ext k m hc)
    rw [U_ext, U_ext]
    have := le_U hc
    omega
  | _, _, @LeTree.branch a b cs ds m ho hs => by
    have e := le_node_length (.branch m ho hs)
    rw [U_branch, U_branch]
    have := le_UK hs
    have hv : ((NearSpecV3.optSlotVal b).map List.length).sum ≤ ((NearSpecV3.optSlotVal a).map List.length).sum := by
      cases ho with
      | none => exact Nat.le_refl _
      | some hs' => exact slotVal_le hs'
    omega
theorem le_UK : ∀ {a b : Kids}, LeKids a b → UK b ≤ UK a
  | _, _, .nil => Nat.le_refl _
  | _, _, .none hs => by rw [UK_none, UK_none]; exact le_UK hs
  | _, _, .some hc hs => by
    rw [UK_some, UK_some]
    have := le_U hc
    have := le_UK hs
    omega
end

/-! ## Record trees with shorter values -/

section
variable {ns : List ZkFormal.NearV3.NodeRec3} {V V' : List ZkFormal.NearV3.ValRec3}

theorem le_slot3 (hV : ∀ i, (ZkFormal.NearV3.valOf V' i).length ≤ (ZkFormal.NearV3.valOf V i).length)
    (s : ZkFormal.NearV3.VSlot3) : LeSlot (ZkFormal.NearV3.slot3 V s) (ZkFormal.NearV3.slot3 V' s) := by
  cases s with
  | ref len h => exact .ref len h
  | val i => exact .val (hV i)

theorem le_kidsOf3 {g g' : Nat → PTrie} (hg : ∀ c, LeTree (g c) (g' c)) :
    ∀ kids, LeKids (ZkFormal.NearV3.kidsOf3 g kids) (ZkFormal.NearV3.kidsOf3 g' kids)
  | [] => .nil
  | .none :: r => .none (le_kidsOf3 hg r)
  | .hash h :: r => .some (.hash h) (le_kidsOf3 hg r)
  | .node c :: r => .some (hg c) (le_kidsOf3 hg r)

theorem le_treeOf3 (hV : ∀ i, (ZkFormal.NearV3.valOf V' i).length ≤ (ZkFormal.NearV3.valOf V i).length) :
    ∀ f n, LeTree (ZkFormal.NearV3.treeOf3 ns V f n) (ZkFormal.NearV3.treeOf3 ns V' f n)
  | 0, _ => .hash []
  | f + 1, n => by
    simp only [ZkFormal.NearV3.treeOf3]
    cases ns[n]? with
    | none => exact .hash []
    | some nr =>
      have hg := le_treeOf3 hV f
      dsimp only
      cases h : nr.node with
      | leaf k v mem => simp only [ZkFormal.NearV3.nodeTree3]; exact .leaf k mem (le_slot3 hV v)
      | ext k kid mem =>
        simp only [ZkFormal.NearV3.nodeTree3]
        refine .ext k mem ?_
        cases kid with
        | none => exact .hash []
        | hash hh => exact .hash hh
        | node c => exact hg c
      | branch v kids mem =>
        simp only [ZkFormal.NearV3.nodeTree3]
        refine .branch mem ?_ (le_kidsOf3 hg kids)
        cases v with
        | none => exact .none
        | some s => exact .some (le_slot3 hV s)

end

/-! ## (C) and (D) on the records -/

section Rec
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Link3

variable {pub : List Fp} {tr : Trace Fp} {r : V3Records}

/-- Written values are no longer than the pre values. -/
theorem vpost_le (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r)
    (i : Nat) :
    (valOf (valsPost r.nodes r.values (fun i => toB (LinkVPost.pnOf r.accts i))) i).length ≤
      (valOf (valsOf3 r.nodes r.values) i).length := by
  unfold valOf
  simp only [valsPost, valsOf3, List.getElem?_map]
  cases he : r.values[i]? with
  | none => simp
  | some e =>
    simp only [Option.map_some, Option.getD_some]
    split
    · rename_i hwr
      obtain ⟨hi, he'⟩ := List.getElem?_eq_some_iff.mp he
      unfold wrote at hwr
      obtain ⟨s, hs, hsv⟩ := List.any_eq_true.mp hwr
      obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hs
      split at hsv
      · rename_i j l pre po w hval
        simp only [Bool.and_eq_true, beq_iff_eq] at hsv
        obtain ⟨rfl, rfl⟩ := hsv
        have h1 := LinkVPost.hvpostLen_of hH T W p hp _ l pre po hval
        obtain ⟨t', ht', hvt, hlt⟩ := val_link W.nodes W.values (vparentBal_of hH T) hp hval
        have e1 : t' = i := by
          rw [vid_small W.values ht', ← he', vid_small W.values hi] at hvt; exact hvt
        subst e1
        have hsh := (W.values.shape _ (List.getElem_mem ht'))
        simp only [toB, List.length_map] at h1 ⊢
        rw [he'] at hlt hsh
        cases hz : e.vz
        · have := (hsh.2 hz).1; omega
        · have := (hsh.1 hz); omega
      · simp at hsv
    · exact Nat.le_refl _

/-- **(C)** The post-value record tree is a shorter-valued copy of the pre record tree. -/
theorem tpost_le (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r)
    (τ : Nat) : LeTree (LinkImplicit.Fpre r τ) (A7Native.Tpost r τ) :=
  le_treeOf3 (vpost_le hH T W) _ _

end Rec

section Inst
variable {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
  {tr : ZkFormal.Air.Trace ZkFormal.Algebra.Fp} {r : V3Records}

/-- **(D)** The scheduler upsert of instance `τ`, with the replaced-bytes identity. -/
theorem qrec_run (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : ZkFormal.V2.HoldsP nearAirV3 (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {τ : Nat} (hτ : τ ≤ p.hdr.K) :
    ∃ run, traceUpsert (A7Native.Tpost r τ) ZkFormal.NearV3.UpsSpec.key
        (ZkFormal.NearV3.Link3.toB (Sched.svOf tr T_CODEC τ)) = some run ∧
      run.output = A7Native.Qrec tr r τ ∧
      unfoldedBytesT (A7Native.Qrec tr r τ) + TrieA7Repl.replacedCharge run + TrieA7Repl.oldValCharge run ≤
        unfoldedBytesT (LinkImplicit.Fpre r τ) + outputByteCharge run +
          (ZkFormal.NearV3.Link3.toB (Sched.svOf tr T_CODEC τ)).length := by
  have L := trieLink_of hp hsz hH T W
  have hQ := A7Native.qrec_upsert hp hsz hH T W hτ
  obtain ⟨run, hr, ho⟩ := traceUpsert_complete hQ
  have hle := tpost_le hH T W τ
  have hwf := le_wf hle (LinkMain.Fpre_wf W L hτ)
  have hrep := TrieA7Repl.traceUpsert_replaced _ _ _ run hr hwf (by decide)
  unfold TrieA7Repl.ReplOk at hrep
  rw [ho] at hrep
  have := le_U hle
  exact ⟨run, hr, ho, by omega⟩

/-- **(C)+(D), exact**: every run of the scheduler upsert of instance `τ` on `Tpost r τ` has output `Qrec tr r τ` and
`U (Tpost) + outputByteCharge + |sv τ| = U (Qrec) + replacedCharge + oldValCharge`. -/
theorem qrec_eq (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : ZkFormal.V2.HoldsP nearAirV3 (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {τ : Nat} (hτ : τ ≤ p.hdr.K) (run : TreeRun)
    (hr : traceUpsert (A7Native.Tpost r τ) ZkFormal.NearV3.UpsSpec.key
        (ZkFormal.NearV3.Link3.toB (Sched.svOf tr T_CODEC τ)) = some run) :
    unfoldedBytesT (A7Native.Tpost r τ) + outputByteCharge run +
        (ZkFormal.NearV3.Link3.toB (Sched.svOf tr T_CODEC τ)).length =
      unfoldedBytesT (A7Native.Qrec tr r τ) + TrieA7Repl.replacedCharge run + TrieA7Repl.oldValCharge run := by
  have L := trieLink_of hp hsz hH T W
  have hQ := A7Native.qrec_upsert hp hsz hH T W hτ
  have ho := traceUpsert_output (A7Native.Tpost r τ) ZkFormal.NearV3.UpsSpec.key
    (ZkFormal.NearV3.Link3.toB (Sched.svOf tr T_CODEC τ))
  rw [hr, hQ] at ho
  simp only [Option.map_some, Option.some.injEq] at ho
  have hle := tpost_le hH T W τ
  have hwf := le_wf hle (LinkMain.Fpre_wf W L hτ)
  have hrep := TrieA7Repl.traceUpsert_replaced _ _ _ run hr hwf (by decide)
  unfold TrieA7Repl.ReplOk at hrep
  rw [ho] at hrep
  exact hrep

end Inst

end A7Post

end ZkFormal.NearV3.Assembly
