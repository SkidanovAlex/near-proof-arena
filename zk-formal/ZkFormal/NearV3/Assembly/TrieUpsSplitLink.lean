import ZkFormal.NearV3.Render.Ups.TreePlan
import ZkFormal.NearV3.Render.Ups.TreeSplitMemoryLink
import ZkFormal.NearV3.Render.Ups.TreeInsertDispatch

/-!
# ZkFormal.NearV3.Assembly.TrieUpsSplitLink — split parts read their child's output memory

`traceUpsert_splitLinked`: in every native upsert run, a `WEX` part's child memory
(`splitChildMemory`) is the output memory of the part before it, and in the cases
`LSb, LSc, ESl0, ESn0` the `SPB` part's child memory is the output memory of part 0 (the moved
node).
-/

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows UpsSpec

def TreeRun.SplitLinked (run : TreeRun) : Prop :=
  ∀ r p, run.parts[r]? = some p →
    (p.kind = .WEX → 0 < r ∧ ∃ q, run.parts[r-1]? = some q ∧ splitChildMemory run.matched p = q.output.memD) ∧
    (p.kind = .SPB → (run.terminal = .LSb ∨ run.terminal = .LSc ∨ run.terminal = .ESl0 ∨ run.terminal = .ESn0) →
      ∃ q, run.parts[0]? = some q ∧ splitChildMemory run.matched p = q.output.memD)

theorem linked_push {run : TreeRun} (h : run.SplitLinked) (part : TreePart)
    (hu : part.kind.upper = true) : (pushPart run part).SplitLinked := by
  intro r p hp
  simp only [pushPart] at hp ⊢
  by_cases hr : r < run.parts.length
  · rw [List.getElem?_append_left hr] at hp
    obtain ⟨h1, h2⟩ := h r p hp
    refine ⟨fun hk => ?_, fun hk hc => ?_⟩
    · obtain ⟨hpos, q, hq, hm⟩ := h1 hk
      exact ⟨hpos, q, by rw [List.getElem?_append_left (by omega)]; exact hq, hm⟩
    · obtain ⟨q, hq, hm⟩ := h2 hk hc
      exact ⟨q, by rw [List.getElem?_append_left (by omega)]; exact hq, hm⟩
  · rw [List.getElem?_append_right (by omega)] at hp
    have : r - run.parts.length = 0 := by
      cases hp' : r - run.parts.length with
      | zero => rfl
      | succ n => rw [hp'] at hp; simp at hp
    rw [this] at hp
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
    subst hp
    constructor
    · intro hk; rw [hk] at hu; simp [UKind.upper] at hu
    · intro hk; rw [hk] at hu; simp [UKind.upper] at hu

theorem drop_succ_of {k xs : List Nat} {n x : Nat} (h : k.drop n = x :: xs) : k.drop (n + 1) = xs := by
  have := congrArg (List.drop 1) h
  simpa [List.drop_drop, Nat.add_comm] using this

theorem leafSplitRun_linked (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    (leafSplitRun k s m key v).SplitLinked := by
  unfold leafSplitRun
  generalize commonPrefix k key = p
  cases h1 : k.drop p.length with
  | nil =>
    cases h2 : key.drop p.length with
    | nil =>
      simp only [h1, h2]
      intro r q hq
      rcases r with _|r <;> simp [terminalRun] at hq
      subst hq; simp
    | cons y ys =>
      simp only [h1, h2]
      intro r q hq
      cases p with
      | nil =>
        rcases r with _|_|r <;> simp [terminalRun, wrapRun] at hq <;> subst hq <;> simp [terminalRun, wrapRun]
      | cons a as =>
        rcases r with _|_|_|r <;> simp [terminalRun, wrapRun, pushPart] at hq <;> subst hq <;>
          simp [terminalRun, wrapRun, pushPart, splitChildMemory, wrapExt]
  | cons x xs =>
    have hx := drop_succ_of h1
    cases h2 : key.drop p.length with
    | nil =>
      simp only [h1, h2]
      intro r q hq
      cases p with
      | nil =>
        rcases r with _|_|r <;> simp [terminalRun, wrapRun] at hq <;> subst hq <;>
          simp [terminalRun, wrapRun, splitChildMemory, hx, PTrie.memD, PTrie.mem?] <;> (try (simp [List.drop_one] at hx; simp [hx]))
      | cons a as =>
        have hx2 : List.drop (as.length + 1 + 1) k = xs := by
          rw [← hx]; simp
        rcases r with _|_|_|r <;> simp [terminalRun, wrapRun, pushPart] at hq <;> subst hq <;>
          simp [terminalRun, wrapRun, pushPart, splitChildMemory, wrapExt, hx2, PTrie.memD, PTrie.mem?]
    | cons y ys =>
      simp only [h1, h2]
      intro r q hq
      cases p with
      | nil =>
        rcases r with _|_|_|r <;> simp [terminalRun, wrapRun] at hq <;> subst hq <;>
          simp [terminalRun, wrapRun, splitChildMemory, hx, PTrie.memD, PTrie.mem?] <;> (try (simp [List.drop_one] at hx; simp [hx]))
      | cons a as =>
        have hx2 : List.drop (as.length + 1 + 1) k = xs := by
          rw [← hx]; simp
        rcases r with _|_|_|_|r <;> simp [terminalRun, wrapRun, pushPart] at hq <;> subst hq <;>
          simp [terminalRun, wrapRun, pushPart, splitChildMemory, wrapExt, hx2, PTrie.memD, PTrie.mem?]

theorem extSplitRun_linked (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    (extSplitRun k c m key v).SplitLinked := by
  unfold extSplitRun
  generalize commonPrefix k key = p
  cases h1 : k.drop p.length with
  | nil =>
    simp only [h1]
    intro r q hq
    simp [terminalRun] at hq
  | cons x xs =>
    have hx := drop_succ_of h1
    simp only [h1]
    cases h2 : key.drop p.length with
    | nil =>
      simp only [h2]
      intro r q hq
      cases xs with
      | nil =>
        cases p with
        | nil => rcases r with _|r <;> simp [terminalRun, wrapRun] at hq <;> subst hq <;> simp [terminalRun, wrapRun]
        | cons a as =>
          rcases r with _|_|r <;> simp [terminalRun, wrapRun, pushPart] at hq <;> subst hq <;>
            simp [terminalRun, wrapRun, pushPart, splitChildMemory, wrapExt]
      | cons z zs =>
        cases p with
        | nil =>
          have hx2 : k.tail = z :: zs := by rw [← hx]; simp [List.drop_one]
          rcases r with _|_|r <;> simp [terminalRun, wrapRun] at hq <;> subst hq <;>
            simp [terminalRun, wrapRun, splitChildMemory, hx2, PTrie.memD, PTrie.mem?]
        | cons a as =>
          have hx2 : List.drop (as.length + 1 + 1) k = z :: zs := by rw [← hx]; simp
          rcases r with _|_|_|r <;> simp [terminalRun, wrapRun, pushPart] at hq <;> subst hq <;>
            simp [terminalRun, wrapRun, pushPart, splitChildMemory, wrapExt, hx2, PTrie.memD, PTrie.mem?]
    | cons y ys =>
      simp only [h2]
      intro r q hq
      cases xs with
      | nil =>
        cases p with
        | nil => rcases r with _|_|r <;> simp [terminalRun, wrapRun] at hq <;> subst hq <;> simp [terminalRun, wrapRun]
        | cons a as =>
          rcases r with _|_|_|r <;> simp [terminalRun, wrapRun, pushPart] at hq <;> subst hq <;>
            simp [terminalRun, wrapRun, pushPart, splitChildMemory, wrapExt]
      | cons z zs =>
        cases p with
        | nil =>
          have hx2 : k.tail = z :: zs := by rw [← hx]; simp [List.drop_one]
          rcases r with _|_|_|r <;> simp [terminalRun, wrapRun] at hq <;> subst hq <;>
            simp [terminalRun, wrapRun, splitChildMemory, hx2, PTrie.memD, PTrie.mem?]
        | cons a as =>
          have hx2 : List.drop (as.length + 1 + 1) k = z :: zs := by rw [← hx]; simp
          rcases r with _|_|_|_|r <;> simp [terminalRun, wrapRun, pushPart] at hq <;> subst hq <;>
            simp [terminalRun, wrapRun, pushPart, splitChildMemory, wrapExt, hx2, PTrie.memD, PTrie.mem?]

theorem linked_of_kinds {run : TreeRun} (h : ∀ p ∈ run.parts, p.kind ≠ .WEX ∧ p.kind ≠ .SPB) :
    run.SplitLinked := by
  intro r p hp
  have hm := h p (List.mem_of_getElem? hp)
  exact ⟨fun hk => absurd hk hm.1, fun hk => absurd hk hm.2⟩

theorem kids_close_linked {run : KidsRun} (hp : run.Planned) (hl : run.inserted = false → run.inner.SplitLinked)
    (source output : PTrie) (slot : Nat) :
    (pushPart run.inner ⟨if run.inserted then .RBI else .RDB,source,output,slot⟩).SplitLinked := by
  cases hb : run.inserted with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    exact linked_push (hl hb) _ (by simp [UKind.upper])
  | true =>
    simp only [KidsRun.Planned, hb, ite_true] at hp
    apply linked_of_kinds
    intro q hq
    simp only [pushPart, ite_true, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · have : q.kind ∈ run.inner.parts.map TreePart.kind := List.mem_map.mpr ⟨q, hq, rfl⟩
      rw [hp.2.2] at this
      simp only [List.mem_singleton] at this
      rw [this]; decide
    · simp

mutual
theorem traceUpsert_splitLinked : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → run.SplitLinked
  | .hash _, _, _, _, h => by simp [traceUpsert] at h
  | .leaf k s m, key, v, run, h => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at h
      subst run
      apply linked_of_kinds
      intro q hq
      simp [terminalRun] at hq
      subst hq; simp
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at h
      subst run
      exact leafSplitRun_linked k s m key v
  | .ext k c m, key, v, run, h => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at h
      subst run
      exact extSplitRun_linked k c m key v
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at h
      | some cm =>
        cases hr : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hr] at h
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hr,Option.some.injEq] at h
          subst run
          apply linked_push (traceUpsert_splitLinked c (key.drop k.length) v inner hr)
          cases k <;> rfl
  | .branch bv cs m, [], v, run, h => by
    cases bv <;> simp only [traceUpsert,Option.isSome_none,Option.isSome_some,
      Bool.false_eq_true,ite_false,ite_true,Option.some.injEq] at h <;> subst run <;>
      apply linked_of_kinds <;> intro q hq <;> simp [terminalRun] at hq <;> subst hq <;> simp
  | .branch bv cs m, n::key, v, run, h => by
    cases hr : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hr] at h
    | some inner =>
      simp only [traceUpsert,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact kids_close_linked (traceKids_plan _ _ _ _ _ _ inner hr)
        (traceKids_splitLinked (.branch bv cs m) (n::key) cs n key v inner hr) _ _ _

theorem traceKids_splitLinked : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun), traceKids source wholeKey cs n key v=some run →
    run.inserted = false → run.inner.SplitLinked
  | _, _, .nil, _, _, _, _, h, _ => by simp [traceKids] at h
  | source, wholeKey, .none rest, 0, key, v, run, h, hi => by
    simp only [traceKids,Option.some.injEq] at h
    subst run; simp at hi
  | source, wholeKey, .some c rest, 0, key, v, run, h, _ => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert c key v with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run
        exact traceUpsert_splitLinked c key v inner hr
  | source, wholeKey, .none rest, n+1, key, v, run, h, hi => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_splitLinked source wholeKey rest n key v inner hr hi
  | source, wholeKey, .some c rest, n+1, key, v, run, h, hi => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_splitLinked source wholeKey rest n key v inner hr hi
end

end ZkFormal.NearV3.Render.UpsGen
