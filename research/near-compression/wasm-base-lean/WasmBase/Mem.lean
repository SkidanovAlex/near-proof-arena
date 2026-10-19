import NearSpecV3.Wasm.Exec
/-!
# WasmBase.Mem — byte-level facts about the spec's linear memory

`readLE` / `writeLE` are `for` loops over `readByte` / `writeByte`.  Here: `readLE` is the
little-endian value `leVal` of the bytes; `writeLE` changes only `pages`, keeps the page sizes, and
overwrites exactly the bytes `[a, a + w)` (when they are in bounds and every page has `pageSize`
bytes — `PagesOK`).
-/
namespace WasmBase
open NearSpecV3.Wasm

/-- Little-endian value of `w` bytes `f a, f (a+1), …`. -/
def leVal (f : Nat → Nat) (a : Nat) : Nat → Nat
  | 0 => 0
  | w + 1 => leVal f a w + f (a + w) * 256 ^ w

theorem foldl_range'_le (f : Nat → Nat) (a w : Nat) :
    (List.range' 0 w).foldl (fun v i => v + f (a + i) * 256 ^ i) 0 = leVal f a w := by
  induction w with
  | zero => rfl
  | succ w ih => rw [List.range'_concat, List.foldl_append, ih]; simp [leVal]

theorem readLE_eq (s : St) (a w : Nat) : readLE s a w = leVal (fun b => (readByte s b).toNat) a w := by
  unfold readLE
  simp
  rw [← foldl_range'_le]
  rfl

/-- Every page has exactly `pageSize` bytes. -/
def PagesOK (s : St) : Prop := ∀ i (h : i < s.pages.size), (s.pages[i]'h).size = pageSize

theorem ba_get_set (p : ByteArray) (i j : Nat) (x : UInt8) (h : i < p.size) :
    (p.set! i x).get! j = if i = j then x else p.get! j := by
  obtain ⟨bs⟩ := p
  simp only [ByteArray.set!, ByteArray.get!, ByteArray.size] at h ⊢
  by_cases hij : i = j
  · subst hij; simp [Array.set!, h]
  · simp only [hij, ite_false]
    rw [Array.set!_eq_setIfInBounds]
    by_cases hj : j < bs.size
    · simp [getElem!_pos, hj, Array.getElem_setIfInBounds, hij]
    · simp [getElem!_neg, hj]

theorem ba_size_set (p : ByteArray) (i : Nat) (x : UInt8) : (p.set! i x).size = p.size := by
  obtain ⟨bs⟩ := p
  simp [ByteArray.set!, ByteArray.size, Array.set!_eq_setIfInBounds]

theorem writeByte_pages (s : St) (a : Nat) (x : UInt8) :
    writeByte s a x = { s with pages := s.pages.modify (a / pageSize) (fun p => p.set! (a % pageSize) x) } := rfl

theorem writeByte_size (s : St) (a : Nat) (x : UInt8) : (writeByte s a x).pages.size = s.pages.size := by
  simp [writeByte]

theorem writeByte_ok {s : St} (hP : PagesOK s) (a : Nat) (x : UInt8) : PagesOK (writeByte s a x) := by
  intro i h
  have h' : i < s.pages.size := by rw [writeByte_size] at h; exact h
  simp only [writeByte, Array.getElem_modify]
  split
  · rw [ba_size_set]; exact hP i h'
  · exact hP i h'

theorem readByte_writeByte {s : St} (hP : PagesOK s) {a : Nat} (ha : a < memBytes s) (x : UInt8) (b : Nat) :
    readByte (writeByte s a x) b = if a = b then x else readByte s b := by
  have hps : 0 < pageSize := by decide
  have hpa : a / pageSize < s.pages.size := by
    unfold memBytes at ha; exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at ha)
  unfold readByte
  simp only [writeByte]
  by_cases hb : b / pageSize < s.pages.size
  · rw [Array.getElem?_eq_getElem (by simpa using hb), Array.getElem?_eq_getElem hb]
    simp only [Array.getElem_modify]
    by_cases hq : a / pageSize = b / pageSize
    · simp only [hq, ite_true]
      rw [ba_get_set _ _ _ _ (by rw [hP _ hb]; exact Nat.mod_lt _ hps)]
      by_cases hab : a = b
      · subst hab; simp
      · have : a % pageSize ≠ b % pageSize := by
          intro hm; apply hab
          rw [← Nat.div_add_mod a pageSize, ← Nat.div_add_mod b pageSize, hq, hm]
        simp [this, hab]
    · have hab : a ≠ b := fun e => hq (by rw [e])
      simp [hq, hab]
  · have hab : a ≠ b := fun e => hb (by rw [← e]; exact hpa)
    rw [Array.getElem?_eq_none (by simpa using Nat.le_of_not_lt hb), Array.getElem?_eq_none (Nat.le_of_not_lt hb)]
    simp [hab]

theorem writeLE_eq (s : St) (a w v : Nat) :
    writeLE s a w v = (List.range' 0 w).foldl (fun s i => writeByte s (a + i) (UInt8.ofNat ((v / 256 ^ i) % 256))) s := by
  unfold writeLE
  simp
  rfl

/-- `writeLE` only rewrites `pages`, keeps their number and sizes, and sets exactly `[a, a + w)`. -/
theorem writeLE_facts {s : St} (hP : PagesOK s) {a w : Nat} (ha : a + w ≤ memBytes s) (v : Nat) :
    (∃ pg, writeLE s a w v = { s with pages := pg }) ∧ (writeLE s a w v).pages.size = s.pages.size ∧
    PagesOK (writeLE s a w v) ∧
    ∀ b, readByte (writeLE s a w v) b =
      if a ≤ b ∧ b < a + w then UInt8.ofNat ((v / 256 ^ (b - a)) % 256) else readByte s b := by
  rw [writeLE_eq]
  induction w with
  | zero =>
    refine ⟨⟨s.pages, rfl⟩, rfl, hP, fun b => ?_⟩
    simp only [List.range'_zero, List.foldl_nil]
    rw [if_neg (by omega)]
  | succ w ih =>
    obtain ⟨⟨pg, hpg⟩, hsz, hok, hrd⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add, Nat.one_mul]
    generalize hS : List.foldl _ s (List.range' 0 w) = S at hpg hsz hok hrd
    have hmS : memBytes S = memBytes s := by unfold memBytes; rw [hsz]
    refine ⟨⟨_, by rw [writeByte_pages, hpg]⟩, by rw [writeByte_size, hsz], writeByte_ok hok _ _, fun b => ?_⟩
    rw [readByte_writeByte hok (by rw [hmS]; omega), hrd b]
    by_cases hb : a + w = b
    · subst hb; simp
    · rw [if_neg hb]
      by_cases h1 : a ≤ b ∧ b < a + w
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]

end WasmBase
