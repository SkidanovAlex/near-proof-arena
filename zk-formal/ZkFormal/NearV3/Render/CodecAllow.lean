import ZkFormal.NearV3.Candidates.ProcActualInput
import ZkFormal.NearV3.Sched.Model
import ZkFormal.NearV3.Render.CodecNative

/-!
# The repaired process allowances are the frozen codec's source-mapped allowances (canonical priors)

`ProcActualInput.allowances ids prev` (the native `indexOf` fold over `prev.links`) equals
`a0Src ids prev` (record `srcOf ids l` of the canonical prior, `0` when none) whenever the prior's link
pairs are the layout's `ids × ids` in order (`canonical0f`), with or without duplicate shard ids
(`Sched.allow0_src`).  This is the identity behind `B_SCMP` (the frozen codec compares
`(apR + fair, MA, cb)` with `apR` from `a0Src`; the repaired comparisons use `allowances`).
-/
namespace ZkFormal.NearV3.Render.CdcAllow
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Candidates

theorem pairs_eq (S R : List Nat) :
    S.flatMap (fun s => R.map fun r => (s, r)) =
      (List.range (S.length * R.length)).map fun l => (S.getD (l / R.length) 0, R.getD (l % R.length) 0) := by
  induction S with
  | nil => simp
  | cons s S ih =>
    rw [List.flatMap_cons, ih, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm _ R.length,
      List.range_add, List.map_append, List.map_map]
    by_cases hR : R.length = 0
    · rw [List.length_eq_zero_iff] at hR; subst hR; simp
    congr 1
    · apply List.ext_getElem (by simp)
      intro l h1 h2
      simp only [List.length_map] at h1
      simp only [List.getElem_map, List.getElem_range, Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt h1,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some, List.getElem?_cons_zero]
    · apply List.map_congr_left
      intro l _
      have hpos : 0 < R.length := Nat.pos_of_ne_zero hR
      simp only [Function.comp_apply, Nat.add_mod_left]
      rw [Nat.add_comm, Nat.add_div_right _ hpos, List.getD_cons_succ]

theorem allowances_canon (ids : List Nat) (prev : NearSpec.Bandwidth.State)
    (hL : prev.links.map (fun la => (la.sender, la.receiver)) = ids.flatMap fun s => ids.map fun r => (s, r)) :
    ProcActualInput.allowances ids prev = a0Src ids prev := by
  have hlen : prev.links.length = ids.length * ids.length := by
    have := congrArg List.length hL
    rw [pairs_eq] at this
    simpa using this
  have ha : ∀ l (hl : l < prev.links.length), (a0Canon ids.length prev)[l]! = (prev.links[l]).allowance := by
    intro l hl
    simp only [a0Canon, hlen, ite_true]
    rw [getElem!_pos _ l (by simp; omega)]
    simp
  have hlinks : prev.links = (List.range (ids.length * ids.length)).map fun l =>
      (⟨ids.getD (l / ids.length) 0, ids.getD (l % ids.length) 0, (a0Canon ids.length prev)[l]!⟩ :
        NearSpec.Bandwidth.LinkAllowance) := by
    apply List.ext_getElem (by simp [hlen])
    intro l h1 h2
    have hl : l < ids.length * ids.length := by omega
    have hp := congrArg (fun xs => xs[l]?) hL
    simp only [pairs_eq, List.getElem?_map, List.getElem?_eq_getElem h1,
      List.getElem?_range hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp
    simp only [List.getElem_map, List.getElem_range, ha l h1]
    cases hx : prev.links[l]
    rw [hx] at hp
    simp only at hp
    rw [hp.1, hp.2]
  unfold ProcActualInput.allowances a0Src
  conv => lhs; rw [hlinks]
  exact allow0_src ids fun k => (a0Canon ids.length prev)[k]!

/-- **The frozen codec's prior allowance of link `kk` is the repaired process allowance** (present,
canonical prior). -/
theorem a0s_canon (b : Assembly.CodecDigest.NativeBlock) (hpres : b.prior.isSome = true)
    (hL : b.old.links.map (fun la => (la.sender, la.receiver)) =
      b.pub.ids.flatMap fun s => b.pub.ids.map fun r => (s, r))
    (hn : b.run.n = b.pub.ids.length)
    (kk : Nat) (hk : kk < b.pub.ids.length * b.pub.ids.length) :
    ((Render.Cdc.blkOf b).recs kk).a0s = (ProcActualInput.allowances b.pub.ids b.old)[kk]! := by
  rw [allowances_canon _ _ hL]
  simp only [a0Src, srcArr]
  rw [getElem!_pos _ kk (by simp [hk])]
  simp only [Array.getElem_map, List.getElem_toArray, List.getElem_range, Render.Cdc.blkOf, hpres, ite_true, hn]
  rfl

end ZkFormal.NearV3.Render.CdcAllow
