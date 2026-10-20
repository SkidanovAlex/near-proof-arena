import NearCompression.BusJointChallengeBound

namespace NearCompression
open Lean.Grind ArenaCore.Security ZkFormal.Udr
variable {K : Type} [Field K]

private def padMessage (width : Nat) (message : List K) : List K :=
  message ++ List.replicate (width-message.length) 0

private theorem fp_zeros (alpha : K) : ∀ n, fp alpha (List.replicate n 0)=0
  | 0 => rfl
  | n+1 => by rw [List.replicate_succ,fp_cons,fp_zeros alpha n]; grind

private theorem fp_pad (alpha : K) (width : Nat) (message : List K) :
    fp alpha (padMessage width message)=fp alpha message := by
  unfold padMessage fp
  rw [List.foldr_append]
  have h:=fp_zeros alpha (width-message.length)
  unfold fp at h
  rw [h]

private theorem drop_zeros [DecidableEq K] (xs : List K) : ∀ n,
    (List.replicate n (0:K) ++ xs).dropWhile (fun x => x==0)=xs.dropWhile (fun x => x==0)
  | 0 => rfl
  | n+1 => by rw [List.replicate_succ,List.cons_append,List.dropWhile_cons_of_pos (by simp),drop_zeros xs n]

private def unpadMessage [DecidableEq K] (message : List K) : List K :=
  (message.reverse.dropWhile (fun x=>x==0)).reverse

private theorem unpad_tagged [DecidableEq K] (width : Nat) (message : List K) (tag : K) (hne : tag≠0) :
    unpadMessage (padMessage width (message++[tag]))=message++[tag] := by
  unfold unpadMessage padMessage
  rw [List.reverse_append,List.reverse_replicate,drop_zeros,List.reverse_append,
    List.reverse_singleton,List.singleton_append,List.dropWhile_cons_of_neg (by simpa using hne)]
  simp

/-- Trailing nonzero bus tags make zero-padding injective even when messages
have different lengths. Without the tag condition this statement is false. -/
theorem bus_tagged_padding_injective (width : Nat) (a b : List K) (x y : K)
    (hx : x≠0) (hy : y≠0)
    (equal : a++[x]++List.replicate (width-(a++[x]).length) 0 =
             b++[y]++List.replicate (width-(b++[y]).length) 0) : a=b ∧ x=y := by
  classical
  have h:=congrArg (unpadMessage (K:=K)) equal
  change unpadMessage (padMessage width (a++[x]))=unpadMessage (padMessage width (b++[y])) at h
  rw [unpad_tagged width a x hx,unpad_tagged width b y hy] at h
  simpa using h

/-- The verifier appends the bus tag at exactly the next power of alpha.
This identity fixes the ordering; putting the tag first changes the statement. -/
theorem bus_tagged_fingerprint (alpha tag : K) (message : List K) :
    fp alpha (message++[tag])=fp alpha message+alpha^message.length*tag := by
  induction message with
  | nil => simp only [List.nil_append,List.length_nil,fp, List.foldr_cons,List.foldr_nil,
      Semiring.pow_zero]; grind
  | cons x xs ih =>
    simp only [List.cons_append,fp_cons,ih,List.length_cons,Semiring.pow_succ]
    grind

/-- Joint bound on the actual unpadded fingerprint polynomials, with variable
message widths and a nonzero final bus tag. No padding is sent on the wire. -/
theorem bus_tagged_joint_challenge_bound (width : Nat) (send receive support : List (List K))
    (alphas gammas : List K) (alphaDistinct : alphas.Nodup) (gammaDistinct : gammas.Nodup)
    (shape : ∀ m, m∈send++receive → m∈support ∧ m.length≤width ∧
      ∃ body tag, m=body++[tag] ∧ tag≠0)
    (unbalanced : ¬send.Perm receive) :
    count (alphas.flatMap (fun a=>gammas.map (fun g=>(a,g))))
      (fun pair=>((send.map (fp pair.1)).map (pair.2 - ·)).prod =
                  ((receive.map (fp pair.1)).map (pair.2 - ·)).prod) ≤
      support.length*width*gammas.length+alphas.length*max send.length receive.length := by
  classical
  have recover (xs : List (List K)) (subset : ∀ m∈xs,m∈send++receive) :
      (xs.map (padMessage width)).map unpadMessage=xs := by
    rw [List.map_map]
    conv => rhs; rw [←List.map_id xs]
    apply List.map_congr_left
    intro m hm
    obtain ⟨_,_,body,tag,rfl,hne⟩:=shape m (subset m hm)
    exact unpad_tagged width body tag hne
  have different : ¬(send.map (padMessage width)).Perm (receive.map (padMessage width)) := by
    intro h
    have mapped:=h.map (unpadMessage (K:=K))
    rw [recover send (fun m hm=>List.mem_append_left _ hm),
      recover receive (fun m hm=>List.mem_append_right _ hm)] at mapped
    exact unbalanced mapped
  have bound:=bus_joint_challenge_bound width (send.map (padMessage width))
    (receive.map (padMessage width)) (support.map (padMessage width)) alphas gammas
    alphaDistinct gammaDistinct (by
      intro m hm
      rw [←List.map_append] at hm
      obtain ⟨original,member,rfl⟩:=List.mem_map.mp hm
      have hs:=shape original member
      refine ⟨List.mem_map.mpr ⟨original,hs.1,rfl⟩,?_⟩
      simp only [padMessage,List.length_append,List.length_replicate]
      omega) different
  simpa only [List.length_map,List.map_map,Function.comp_def,fp_pad] using bound

end NearCompression
