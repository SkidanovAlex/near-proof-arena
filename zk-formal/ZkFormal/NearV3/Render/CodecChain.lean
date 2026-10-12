import ZkFormal.NearV3.Render.CodecTable

/-!
# Codec descriptor chains: appending, flattening, ranges (copy of `SsdChain` for `Cdc.Desc`)

`Chain l`: every adjacent pair of `l` is admissible (`Desc.Adj`).  `chain_append` joins two
chains through an admissible junction; `chain_flatten` joins a list of blocks whose nonempty
members start with an `S`-descriptor and end with an `E`-descriptor when every `E` may be followed
by every `S`; `chain_map_range` builds a chain from an index function.
-/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def Chain (l : List Desc) : Prop := ∀ k (hk : k + 1 < l.length), Desc.Adj l[k] l[k+1]

theorem chain_nil : Chain [] := fun _ hk => by simp at hk

theorem chain_single (d : Desc) : Chain [d] := fun _ hk => by simp at hk

theorem chain_append (a b : List Desc) (ha : Chain a) (hb : Chain b)
    (hj : ∀ x y, a.getLast? = some x → b.head? = some y → Desc.Adj x y) : Chain (a ++ b) := by
  intro k hk
  simp only [List.length_append] at hk
  by_cases h1 : k + 1 < a.length
  · rw [List.getElem_append_left (by omega), List.getElem_append_left h1]
    exact ha k h1
  · by_cases h2 : k + 1 = a.length
    · rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]
      apply hj
      · rw [List.getLast?_eq_getElem?]
        simp only [show a.length - 1 = k by omega]
        exact List.getElem?_eq_getElem _
      · rw [List.head?_eq_getElem?]
        simp only [show k + 1 - a.length = 0 by omega]
        exact List.getElem?_eq_getElem _
    · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      have := hb (k - a.length) (by omega)
      simp only [show k + 1 - a.length = k - a.length + 1 by omega]
      exact this

theorem chain_cons (d : Desc) (l : List Desc) (hl : Chain l)
    (hj : ∀ y, l.head? = some y → Desc.Adj d y) : Chain (d :: l) := by
  have := chain_append [d] l (chain_single d) hl (fun x y hx hy => by
    simp at hx; subst hx; exact hj y hy)
  simpa using this

theorem chain_flatten (Ls : List (List Desc)) (S E : Desc → Prop)
    (hSE : ∀ x y, E x → S y → Desc.Adj x y)
    (h : ∀ L ∈ Ls, Chain L ∧ (∀ x, L.head? = some x → S x) ∧ (∀ x, L.getLast? = some x → E x)) :
    Chain Ls.flatten ∧ (∀ x, Ls.flatten.head? = some x → S x) ∧
      (∀ x, Ls.flatten.getLast? = some x → E x) := by
  induction Ls with
  | nil => exact ⟨chain_nil, fun _ h => by simp at h, fun _ h => by simp at h⟩
  | cons L Ls ih =>
    obtain ⟨hc, hs, he⟩ := h L (List.mem_cons_self ..)
    obtain ⟨ic, is, ie⟩ := ih (fun L' hL' => h L' (List.mem_cons_of_mem _ hL'))
    simp only [List.flatten_cons]
    refine ⟨chain_append _ _ hc ic (fun x y hx hy => hSE x y (he x hx) (is y hy)), ?_, ?_⟩
    · intro x hx
      rw [List.head?_append] at hx
      cases hL : L.head? with
      | none => rw [hL] at hx; exact is x (by simpa using hx)
      | some z => rw [hL] at hx; simp at hx; subst hx; exact hs _ hL
    · intro x hx
      rw [List.getLast?_append] at hx
      cases hF : Ls.flatten.getLast? with
      | none => rw [hF] at hx; exact he x (by simpa using hx)
      | some z => rw [hF] at hx; simp at hx; subst hx; exact ie _ hF

theorem chain_map_range (n : Nat) (f : Nat → Desc) (h : ∀ k, k + 1 < n → Desc.Adj (f k) (f (k+1))) :
    Chain ((List.range n).map f) := by
  intro k hk
  simp only [List.length_map, List.length_range] at hk
  simp only [List.getElem_map, List.getElem_range]
  exact h k hk

/-- `table_local` for a chain with an admissible head and tail. -/
theorem table_local_chain (ds : List Desc) (hcap : ds.length < 2 ^ 22) (hv : ∀ d ∈ ds, d.Valid)
    (hc : Chain ds) (hh : ∀ x, ds.head? = some x → x.FirstOk)
    (hl : ∀ x, ds.getLast? = some x → x.Final) (t : Nat) (pub : List ZkFormal.Algebra.Fp) :
    ZkFormal.Near.TableLocal Codec.table (codecTrace ds) t pub := by
  refine table_local ds hcap hv hc (fun h => hh _ ?_) (fun h => hl _ ?_) t pub
  · rw [List.head?_eq_getElem?]; exact List.getElem?_eq_getElem _
  · rw [List.getLast?_eq_getElem?]; exact List.getElem?_eq_getElem _

end ZkFormal.NearV3.Render.Cdc
