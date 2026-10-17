import ZkFormal.Udr.GrandProduct

namespace NearCompression
open Lean.Grind ArenaCore.Security ZkFormal.Udr

private theorem conditional_count {A B : Type} (xs : List A) (ys : List B)
    (bad : A → Prop) (accept : A → B → Prop) (limit : Nat)
    (good : ∀ x ∈ xs, ¬bad x → count ys (accept x) ≤ limit) :
    (xs.map (fun x => count ys (accept x))).sum ≤
      count xs bad * ys.length + xs.length * limit := by
  classical
  induction xs with
  | nil => simp [count]
  | cons x xs ih =>
    have tail := ih (fun y hy => good y (by simp [hy]))
    have head := good x (by simp)
    have maximum : count ys (accept x) ≤ ys.length := List.countP_le_length
    simp only [List.map_cons,List.sum_cons,count,List.countP_cons,List.length_cons] at *
    by_cases h : bad x <;> simp_all <;> grind

/-- Joint ideal alpha/gamma bound for fixed unequal expanded message multisets.
`support` bounds distinct message encodings, while expanded lengths count the
natural multiplicities. Both lists are fixed before either challenge. This
is not a commitment extraction or Fiat-Shamir theorem. -/
theorem bus_joint_challenge_bound {K : Type} [Field K]
    (width : Nat) (send receive support : List (List K))
    (alphas gammas : List K) (alphaDistinct : alphas.Nodup) (gammaDistinct : gammas.Nodup)
    (shape : ∀ m, m ∈ send ++ receive → m ∈ support ∧ m.length=width)
    (unbalanced : ¬send.Perm receive) :
    count (alphas.flatMap (fun a => gammas.map (fun g => (a,g))))
      (fun pair => ((send.map (fp pair.1)).map (pair.2 - ·)).prod =
                   ((receive.map (fp pair.1)).map (pair.2 - ·)).prod) ≤
      support.length * width * gammas.length +
      alphas.length * max send.length receive.length := by
  let bad := fun a => (send.map (fp a)).Perm (receive.map (fp a))
  let accept := fun a g => ((send.map (fp a)).map (g - ·)).prod =
                           ((receive.map (fp a)).map (g - ·)).prod
  have alphaBound := gpAlpha K width send receive support alphas alphaDistinct shape unbalanced
  have conditional := conditional_count alphas gammas bad accept (max send.length receive.length)
    (by
      intro a _ h
      have bound := gpGamma K (send.map (fp a)) (receive.map (fp a)) gammas gammaDistinct h
      simpa only [List.length_map] using bound)
  have scaled := Nat.mul_le_mul_right gammas.length alphaBound
  have total := Nat.le_trans conditional (Nat.add_le_add_right scaled
    (alphas.length * max send.length receive.length))
  simpa only [count,List.countP_flatMap,List.countP_map,Function.comp_def,bad,accept] using total

end NearCompression
