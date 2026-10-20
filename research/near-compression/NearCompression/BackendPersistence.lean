import NearCompression.RealInstruction

/-! Backend presence is distinct from preservation of a backing store when present. -/
namespace NearCompression
open NearSpecV3.Wasm

def ResultKeepsBackend (s : St) : Res → Prop
  | .cont t | .fin t | .abort t _ => t.real.isSome = s.real.isSome
  | .unmodeled _ => True

theorem sync_keeps_backend (s t : St) (hs : sync s = .ok t) : t.real = s.real := by
  unfold sync at hs
  dsimp only at hs
  repeat' (split at hs <;> (try simp_all only []))
  all_goals cases hs <;> rfl

theorem charge_keeps_backend (s : St) (fee : Fee) (count : Nat) :
    ResultKeepsBackend s (charge s fee count) := by
  unfold charge
  dsimp only
  repeat' split
  all_goals simp only [ResultKeepsBackend]
  all_goals first
    | trivial
    | (exact congrArg Option.isSome (sync_keeps_backend _ _ (by assumption)))
    | rfl

theorem return_keeps_backend (p : Prepared) (s : St) :
    ResultKeepsBackend s (doReturn p s) := by
  unfold doReturn
  repeat' split
  all_goals first | rfl | trivial

theorem branch_keeps_backend (p : Prepared) (s : St) (f : Frame) (l : Nat) :
    ResultKeepsBackend s (doBr p s f l) := by
  unfold doBr
  split
  · exact return_keeps_backend p s
  · split
    · trivial
    · change (setFrame _ _).real.isSome = s.real.isSome
      rw [set_frame_real]

theorem result_bind_keeps_backend (s : St) (r : Res) (f : St → Res)
    (hr : ResultKeepsBackend s r) (hf : ∀ u, ResultKeepsBackend u (f u)) :
    ResultKeepsBackend s (r.bind f) := by
  cases r with
  | cont u =>
    change ResultKeepsBackend s (f u)
    have hu := hf u
    cases he : f u <;> simp only [he, ResultKeepsBackend] at hu ⊢
    all_goals first | exact hu.trans hr | trivial
  | fin u => exact hr
  | abort u e => exact hr
  | unmodeled e => trivial

theorem backend_invariant_cont (s u : St) (r : Res)
    (hr : ResultKeepsBackend s r) (hc : r = .cont u) : u.real.isSome = s.real.isSome := by
  subst r
  exact hr

theorem enter_keeps_backend (p : Prepared) (s : St) (fi : Nat) :
    ResultKeepsBackend s (enter p s fi) := by
  unfold enter
  dsimp only
  split
  · trivial
  · rename_i pf hp
    split
    · split
      · trivial
      · rename_i t ht
        exact congrArg Option.isSome (sync_keeps_backend s t ht)
    · have hc := charge_keeps_backend
        { s with stackRem := s.stackRem - pf.stackCharge } (Fee.const pf.prologueGas) 0
      split <;> rename_i he
      all_goals simp only [he, ResultKeepsBackend] at hc
      all_goals exact hc

end NearCompression
