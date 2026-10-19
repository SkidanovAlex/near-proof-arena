import ZkFormal.PQ.StatePort.Swirl
import ZkFormal.PQ.StatePort.Bridge

/-!
# ZkFormal.PQ.StatePort.Tape — the canonical TAPE and its net-multiplicity identity (P4)

Lane `pq-state-port`.  In the port, the classical public segments (which the *classical verifier*
puts on the buses itself) become one committed `TAPE` table.  `VdChecks.tape` assumes that TAPE
carries the net public multiplicity of every message on every translated bus (`TapeNet`).  That
assumption is discharged, on the Rust side, by V_d recomputing the TAPE commitment from the
public messages (the same pattern as the cached `CODE` table in `pq-wasm-base`,
`results/pq-wasm-base/STATEMENT.md` §2): under commitment binding, the proved table must be the
canonical TAPE.

This module defines that canonical TAPE and proves the parts of `TapeNet` that are list algebra:

* `tapeCanon AP pub` — one row per distinct `(bus, msg)` of `pubMsgs AP pub`, the row's count is
  `pubCount … true − pubCount … false`, and its selectors mark that row's `(bus, len)` key;
* `canonKeys_count_le`, `canonMsgs_count_le` — every key and every message occurs **at most
  once**, so the selector/message match in `TapeRow.sum` is unambiguous.

The remaining step is `tapeNet_canon : TapeNet off AP pub (tapeCanon AP pub)`: that the field sum
of those rows on bus `off + b` and message `m` is exactly `netF AP pub b m`.  It needs the
canonical key list to contain exactly the key of each message (which `eraseDups` gives via
`List.mem_eraseDups`) and `m.take m.length = m`.  This is small, purely mechanical list work, and
it is the one piece of P4's Lean side not landed here; the Rust and statement sides of P4 are
implemented and tested (the cached TAPE root is recomputed in `check_statement` and the 19/19 and
23/23 tamper suites exercise it).
-/

namespace ZkFormal.PQ.StatePort

open ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra ZkFormal.Udr ZkFormal.Udr.Np

/-! ## `eraseDups` keeps at most one copy -/

/-- Strong-induction helper: `eraseDups` keeps at most one copy of `a`. -/
theorem count_eraseDups_aux {α : Type} [BEq α] [LawfulBEq α] (a : α) :
    ∀ (n : Nat) (l : List α), l.length ≤ n → (l.eraseDups).count a ≤ 1
  | 0, l, hl => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst this
    simp
  | n + 1, [], _ => by simp
  | n + 1, x :: xs, hl => by
    rw [List.eraseDups_cons, List.count_cons]
    by_cases hx : x == a
    · rw [if_pos hx]
      have hzero : ((xs.filter fun b => !b == x).eraseDups).count a = 0 :=
        List.count_eq_zero.mpr fun hmem => by
          have hf := (List.mem_filter.mp (List.mem_eraseDups.mp hmem)).2
          have hxa : x = a := LawfulBEq.eq_of_beq hx
          subst hxa
          simp at hf
      omega
    · rw [if_neg hx]
      apply count_eraseDups_aux a n (xs.filter fun b => !b == x)
      simp at hl
      have := List.length_filter_le (fun b => !b == x) xs
      omega

/-- **`eraseDups` keeps at most one copy of each element.** -/
theorem count_eraseDups_le_one {α : Type} [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    (l.eraseDups).count a ≤ 1 :=
  count_eraseDups_aux a l.length l (Nat.le_refl _)

/-! ## The canonical TAPE -/

/-- The distinct `(bus, length)` keys of the public messages, **on the translated buses**
`off + bus`: `TapeNet` looks up SWIRL bus `off + b`, so TAPE's keys are the translated ids (the
driver builds TAPE the same way). -/
def canonKeys (off : Nat) (AP : AirP) (pub : List Fp) : List (Nat × Nat) :=
  ((pubMsgs AP pub).map fun x => (off + x.1, x.2.2.length)).eraseDups

/-- The distinct `(bus, message)` pairs of the public messages, on translated buses. -/
def canonMsgs (off : Nat) (AP : AirP) (pub : List Fp) : List (Nat × List Fp) :=
  ((pubMsgs AP pub).map fun x => (off + x.1, x.2.2)).eraseDups

/-- One canonical row per distinct message: its net count, and a `1` selector at its own key. -/
noncomputable def canonRows (off : Nat) (AP : AirP) (pub : List Fp) : List TapeRow :=
  (canonMsgs off AP pub).map fun k =>
    { msg := k.2
      cnt := ((pubCount AP pub (k.1 - off) true k.2 : Nat) : Fp)
        - ((pubCount AP pub (k.1 - off) false k.2 : Nat) : Fp)
      sel := (canonKeys off AP pub).map fun kk => if kk = (k.1, k.2.length) then 1 else 0 }

/-- **The canonical TAPE**: what V_d must reconstruct from the public messages. -/
noncomputable def tapeCanon (off : Nat) (AP : AirP) (pub : List Fp) : Tape :=
  { keys := canonKeys off AP pub, rows := canonRows off AP pub }

/-- Every canonical key occurs at most once, so a row's selector match is unique. -/
theorem canonKeys_count_le (off : Nat) (AP : AirP) (pub : List Fp) (k : Nat × Nat) :
    (canonKeys off AP pub).count k ≤ 1 :=
  count_eraseDups_le_one k _

/-- Every canonical message occurs at most once, so a bus/message match identifies one row. -/
theorem canonMsgs_count_le (off : Nat) (AP : AirP) (pub : List Fp) (k : Nat × List Fp) :
    (canonMsgs off AP pub).count k ≤ 1 :=
  count_eraseDups_le_one k _

/-- Every canonical message's key is among the canonical keys (so its selector is `1`). -/
theorem canonKey_mem (off : Nat) (AP : AirP) (pub : List Fp) (k : Nat × List Fp)
    (hk : k ∈ canonMsgs off AP pub) : (k.1, k.2.length) ∈ canonKeys off AP pub := by
  rw [canonKeys, List.mem_eraseDups]
  rw [canonMsgs, List.mem_eraseDups] at hk
  obtain ⟨x, hx, hkx⟩ := List.mem_map.mp hk
  refine List.mem_map.mpr ⟨x, hx, ?_⟩
  rw [← hkx]

end ZkFormal.PQ.StatePort
