import ZkFormal.NearV3.Render.CodecDefs
import ZkFormal.NearV3.Sched.Complete.Trace

/-!
# Codec row cells: lookups of the honest assignments

`lookup_ite`/`lookup_cons`: the cell simp set for the row assignments of `CodecDefs`; `keys_*`: every
assigned column is `< width` (so `setAll width A` reads `lookup A c 0` at every column);
`gd_setAll`: the array read.  The per-column values used by the modular constraints are proved for
symbolic `f, gg` (`rec_*`), header (`hdr_*`), hash (`hash_*`) and `sha256(all_shards)` (`ash_*`).
-/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Codec ZkFormal.Chacha.Table.E ZkFormal.NearV3.Candidates.SchedSetAll
open ZkFormal.NearV3.Sched.Complete (gd natCell natRow)

theorem lookup_ite (C : Prop) [Decidable C] (L : List (Nat × Nat)) (c v : Nat) :
    lookup (if C then L else []) c v = if C then lookup L c v else v := by
  split <;> rfl

theorem lookup_cons (a b : Nat) (L : List (Nat × Nat)) (c v : Nat) :
    lookup ((a, b) :: L) c v = lookup L c (if a = c then b else v) := by
  simp only [lookup, List.foldl_cons]

/-- Not a `rfl` lemma on purpose: `dsimp` with it makes the kernel unfold symbolic field inverses. -/
theorem lookup_nil (c v : Nat) : lookup [] c v = v := by simp only [lookup, List.foldl_nil]

theorem lookup_app (xs ys : List (Nat × Nat)) (c v : Nat) :
    lookup (xs ++ ys) c v = lookup ys c (lookup xs c v) := append xs ys c v

theorem lookup_bound (A : List (Nat × Nat)) (c v B : Nat) (hv : v < B) (h : ∀ p ∈ A, p.2 < B) :
    lookup A c v < B := by
  induction A generalizing v with
  | nil => exact hv
  | cons p ps ih =>
    rw [show lookup (p :: ps) c v = lookup ps c (if p.1 = c then p.2 else v) from rfl]
    apply ih _ _ (fun q hq => h q (by simp [hq]))
    split
    · exact h p (by simp)
    · exact hv

theorem lookup_out (A : List (Nat × Nat)) (c w : Nat) (h : ∀ p ∈ A, p.1 < w) (hc : w ≤ c) :
    lookup A c 0 = 0 :=
  lookup_miss A c 0 (fun p hp => by have := h p hp; omega)

theorem gd_setAll (A : List (Nat × Nat)) (c : Nat) (h : ∀ p ∈ A, p.1 < Codec.width) :
    gd (setAll Codec.width A) c = lookup A c 0 := by
  by_cases hc : c < Codec.width
  · rw [← cell Codec.width A c hc]
    simp only [gd, Array.getD_eq_getD_getElem?]
    have hs := width Codec.width A
    simp [getElem!_def, Array.getElem?_eq_getElem (show c < (setAll Codec.width A).size by omega)]
  · rw [lookup_out A c Codec.width h (by omega)]
    simp only [gd, Array.getD_eq_getD_getElem?]
    have hs := width Codec.width A
    rw [Array.getElem?_eq_none (by omega)]
    rfl

/-! ## Keys -/

theorem keys_pbits (x : Nat) : ∀ p ∈ pbits x, p.1 < Codec.width := by
  intro p hp
  simp only [pbits, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  simp only [pbit, Codec.width]; omega

theorem keys_qbits (x : Nat) : ∀ p ∈ qbits x, p.1 < Codec.width := by
  intro p hp
  simp only [qbits, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  simp only [prbit, Codec.width]; omega

theorem keys_regA (vals : Nat → Nat) : ∀ p ∈ regA vals, p.1 < Codec.width := by
  intro p hp
  simp only [regA, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  simp only [reg, overlay, Codec.width]
  split
  · rename_i h
    have : i ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30] := by
      simp; omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
      rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · decide

theorem keys_lit {L : List (Nat × Nat)} (h : (L.all fun p => decide (p.1 < Codec.width)) = true) :
    ∀ p ∈ L, p.1 < Codec.width := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  simpa using this

theorem keys_app {xs ys : List (Nat × Nat)} (h1 : ∀ p ∈ xs, p.1 < Codec.width)
    (h2 : ∀ p ∈ ys, p.1 < Codec.width) : ∀ p ∈ xs ++ ys, p.1 < Codec.width := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact h1 p h
  · exact h2 p h

theorem keys_ite (C : Prop) [Decidable C] {L : List (Nat × Nat)} (h : ∀ p ∈ L, p.1 < Codec.width) :
    ∀ p ∈ (if C then L else []), p.1 < Codec.width := by
  split
  · exact h
  · intro p hp; simp at hp

theorem keys_instA (I : Inst) : ∀ p ∈ instA I, p.1 < Codec.width := keys_lit (by rfl)

theorem keys_hdrA (I : Inst) (p : Nat) : ∀ q ∈ hdrA I p, q.1 < Codec.width := by
  unfold hdrA
  exact keys_app (keys_app (keys_app (keys_app (keys_instA I) (keys_lit (by rfl))) (keys_regA _))
    (keys_pbits _)) (keys_qbits _)

theorem keys_recA (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv : Nat) :
    ∀ q ∈ recA I R f gg bpo bpr apv apostv bigv, q.1 < Codec.width := by
  unfold recA
  refine keys_app (keys_app (keys_app (keys_app (keys_app (keys_app (keys_app (keys_app
    (keys_app (keys_instA I) (keys_lit (by rfl))) (keys_pbits _)) (keys_qbits _)) (keys_lit (by rfl)))
    (keys_ite _ (keys_lit (by rfl)))) (keys_ite _ (keys_lit (by rfl)))) (keys_ite _ (keys_lit (by rfl))))
    (keys_ite _ (keys_lit (by rfl)))) (keys_ite _ (keys_lit (by rfl)))

theorem keys_hashA (I : Inst) (dig hpre : List Nat) (j : Nat) : ∀ q ∈ hashA I dig hpre j, q.1 < Codec.width := by
  unfold hashA
  exact keys_app (keys_app (keys_app (keys_app (keys_instA I) (keys_lit (by rfl))) (keys_regA _))
    (keys_pbits _)) (keys_qbits _)

theorem keys_ashA (I : Inst) (ash : List Nat) (j : Nat) : ∀ q ∈ ashA I ash j, q.1 < Codec.width := by
  unfold ashA
  exact keys_app (keys_instA I) (keys_lit (by rfl))

end ZkFormal.NearV3.Render.Cdc
