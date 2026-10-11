import ZkFormal.NearV3.Render.PaddedTrie
import ZkFormal.NearV3.Link.Uniq3Digs

/-!
# ZkFormal.NearV3.Assembly.UniqNative — the honest `uniqV3` entries (`UEnt` producer)

`uniqV3` receives, per store entry, `DIGS (eid, τ, i, digest[i])` for `i < 32` — exactly the
`DIGS` windows the node table (revealed kids `NPRE(c)`, revealed values `VPRE(i)`) and the
head table (roots `NPRE(rid)`) send.  The honest entry list is these windows, one `UEnt` per
window (`rawEnts`), sorted by the key `(τ, le256 digest)` with a tie-break `rk eid`
(`uniqOf rk vs hs`, a `List.mergeSort`).  The tie-break fixes the order inside an
equal-digest class (the order of the `DUP` chain, `StoreDuplicateChain`); it does not affect
`DIGS` or `UOk`.

* `uniqOf_digsBal` — **`DIGS` balance** (`Link3.DigsBal`): the node and head `DIGS` sends are,
  as a multiset, the honest `uniq` receives.  No hypothesis.
* `uniqOf_ok` — **`UOk`** from explicit facts about the raw windows (`RawOk`): 32 digest bytes
  `< 256`, `eid < P`, `τ + 1 < P`, at most `2^17` windows, at least one head, and `τ`-coverage
  (every instance below a window's instance has a window — the heads give it).
-/

namespace ZkFormal.NearV3.Assembly.UniqNative

open ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Render ZkFormal.NearV3.Link3 ZkFormal.Algebra

/-- The `uniq` entries of one node record's `DIGS` windows. -/
def entsOf (s : NodeS3) : List UEnt :=
  (s.v.revealed.map fun (c, _, _, pre, _) => (⟨msgId K_NPRE c, s.tau, pre⟩ : UEnt)) ++
  (match s.v.value with
   | some (i, _, pre, _, _) => [(⟨msgId K_VPRE i, s.tau, pre⟩ : UEnt)]
   | none => [])

/-- The `uniq` entry of one head's root window. -/
def entH (h : HeadE) : UEnt := ⟨msgId K_NPRE h.rid, h.tau, h.pre⟩

/-- All `DIGS` windows, unsorted. -/
def rawEnts (vs : List NodeS3) (hs : List HeadE) : List UEnt := vs.flatMap entsOf ++ hs.map entH

/-- The sort key: instance, then the digest as a little-endian integer, then the tie-break. -/
def ule (rk : Nat → Nat) (a b : UEnt) : Bool :=
  decide (a.tau < b.tau ∨ (a.tau = b.tau ∧ (le256 a.bytes < le256 b.bytes ∨
    (le256 a.bytes = le256 b.bytes ∧ rk a.eid ≤ rk b.eid))))

theorem ule_trans (rk : Nat → Nat) (a b c : UEnt) (h1 : ule rk a b = true) (h2 : ule rk b c = true) :
    ule rk a c = true := by
  simp only [ule, decide_eq_true_eq] at *
  omega

theorem ule_total (rk : Nat → Nat) (a b : UEnt) : (ule rk a b || ule rk b a) = true := by
  simp only [ule, Bool.or_eq_true, decide_eq_true_eq]
  omega

/-- **The honest `uniqV3` entry list.** -/
def uniqOf (rk : Nat → Nat) (vs : List NodeS3) (hs : List HeadE) : List UEnt :=
  (rawEnts vs hs).mergeSort (ule rk)

theorem uniqOf_perm (rk : Nat → Nat) (vs : List NodeS3) (hs : List HeadE) :
    (uniqOf rk vs hs).Perm (rawEnts vs hs) :=
  List.mergeSort_perm _ _

theorem uniqOf_sorted (rk : Nat → Nat) (vs : List NodeS3) (hs : List HeadE) :
    (uniqOf rk vs hs).Pairwise (fun a b => ule rk a b = true) :=
  List.pairwise_mergeSort (ule_trans rk) (ule_total rk) _

/-! ## `DIGS` -/

/-- The `DIGS` messages `uniqV3` receives for one entry. -/
def digsU (e : UEnt) : List Msg := (List.range 32).map fun j => [e.eid, e.tau, j, e.bytes.getD j 0]

theorem uniqEntries_digs (L : List UEnt) :
    uniqRecvs (uniqEntries L) B_DIGS = L.flatMap digsU := by
  rw [digsR]
  have h : (uniqEntries L).map (fun e => (e.eid, e.tau, e.bytes)) = L.map (fun e => (e.eid, e.tau, e.bytes)) := by
    apply List.ext_getElem
    · simp [uniqEntries]
    · intro t h1 h2
      simp only [uniqEntries, List.getElem_map, List.getElem_range, UniqGen.ent]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h2), Option.getD_some]
  have hf : ∀ (M : List UniqE), M.flatMap (fun e => (List.range 32).map fun j => [e.eid, e.tau, j, e.bytes.getD j 0]) =
      (M.map (fun e => (e.eid, e.tau, e.bytes))).flatMap
        (fun x => (List.range 32).map fun j => [x.1, x.2.1, j, x.2.2.getD j 0]) := by
    intro M; simp [List.flatMap_map]
  have hg : L.flatMap digsU = (L.map (fun e => (e.eid, e.tau, e.bytes))).flatMap
        (fun x => (List.range 32).map fun j => [x.1, x.2.1, j, x.2.2.getD j 0]) := by
    rw [List.flatMap_map]; rfl
  rw [hf, h, hg]

theorem entsOf_digs (s : NodeS3) : (entsOf s).flatMap digsU = digsOf s := by
  unfold entsOf digsOf
  rw [List.flatMap_append, List.flatMap_map]
  congr 1
  rcases s.v.value with _ | ⟨i, l, pre, po, w⟩ <;> simp [digsU]

theorem rawEnts_digs (vs : List NodeS3) (hs : List HeadE) :
    (rawEnts vs hs).flatMap digsU = nodeSends3 vs B_DIGS ++ headSends hs B_DIGS := by
  rw [digsS, rawEnts, List.flatMap_append, List.flatMap_assoc, List.flatMap_map]
  congr 1
  · have : ∀ (l : List NodeS3) (k : Nat), (l.zip (List.range' k l.length)).flatMap (fun x => digsOf x.1) =
        l.flatMap digsOf := by
      intro l
      induction l with
      | nil => intro k; rfl
      | cons a l ih => intro k; simp [List.range'_succ, List.flatMap_cons, ih]
    rw [List.range_eq_range', this]
    simp only [entsOf_digs]

/-- **`DIGS` balance** of the honest entries. -/
theorem uniqOf_digsBal (rk : Nat → Nat) (vs : List NodeS3) (hs : List HeadE) :
    DigsBal vs hs (uniqEntries (uniqOf rk vs hs)) := by
  unfold DigsBal
  rw [uniqEntries_digs, ← rawEnts_digs]
  exact ((uniqOf_perm rk vs hs).flatMap_right digsU).map _ |>.symm

/-! ## `UOk` -/

/-- Explicit facts about the raw windows that make the sorted list a legal `uniqV3` input. -/
structure RawOk (vs : List NodeS3) (hs : List HeadE) : Prop where
  pos : 0 < hs.length
  cap : (rawEnts vs hs).length ≤ 2 ^ 17
  mem : ∀ e ∈ rawEnts vs hs, e.bytes.length = 32 ∧ (∀ y ∈ e.bytes, y < 256) ∧ e.eid < P ∧ e.tau + 1 < P
  /-- every instance below a window's instance has a window -/
  cover : ∀ e ∈ rawEnts vs hs, ∀ τ', τ' ≤ e.tau → ∃ e' ∈ rawEnts vs hs, e'.tau = τ'

theorem uniqOf_ok (rk : Nat → Nat) (vs : List NodeS3) (hs : List HeadE) (h : RawOk vs hs) :
    UOk (uniqOf rk vs hs) := by
  have hp := uniqOf_perm rk vs hs
  have hs' := List.pairwise_iff_getElem.mp (uniqOf_sorted rk vs hs)
  have hmem : ∀ e, e ∈ uniqOf rk vs hs ↔ e ∈ rawEnts vs hs := fun e => hp.mem_iff
  have hlen : (uniqOf rk vs hs).length = (rawEnts vs hs).length := hp.length_eq
  have hadj : ∀ t (ht : t + 1 < (uniqOf rk vs hs).length),
      ule rk (uniqOf rk vs hs)[t] (uniqOf rk vs hs)[t + 1] = true :=
    fun t ht => hs' t (t + 1) (by omega) ht (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hlen, rawEnts, List.length_append, List.length_map]; have := h.pos; omega
  · rw [hlen]; have := h.cap; omega
  · intro e he; exact h.mem e ((hmem e).mp he)
  · intro t ht
    have h1 := hadj t ht
    simp only [ule, decide_eq_true_eq] at h1
    apply Classical.byContradiction
    intro hne
    -- an instance strictly between two adjacent entries has no window
    obtain ⟨e', he', hτ⟩ := h.cover _ ((hmem _).mp (List.getElem_mem ht))
      ((uniqOf rk vs hs)[t].tau + 1) (by omega)
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ((hmem e').mpr he')
    by_cases hit : i ≤ t
    · rcases Nat.lt_or_eq_of_le hit with hlt | heq
      · have := hs' i t hi (by omega) hlt
        simp only [ule, decide_eq_true_eq] at this; omega
      · subst heq; omega
    · have hle : t + 1 ≤ i := by omega
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · have := hs' (t + 1) i ht hi hlt
        simp only [ule, decide_eq_true_eq] at this; omega
      · subst heq; omega
  · intro t ht heq
    have h1 := hadj t ht
    simp only [ule, decide_eq_true_eq] at h1
    omega

end ZkFormal.NearV3.Assembly.UniqNative
