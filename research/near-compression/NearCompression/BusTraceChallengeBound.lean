import ZkFormal.V2.VerifierDefs
import NearCompression.BusTraceMultiset
import NearCompression.BusTaggedChallengeBound
import ZkFormal.Algebra.Fp8

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.V2 ArenaCore.Security ZkFormal.Udr

private theorem list_map_injective {A B : Type} (f : A→B)
    (injective : ∀ a b,f a=f b→a=b) (xs ys : List A) (equal : xs.map f=ys.map f) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at equal
    | cons y ys =>
      have pair:=List.cons.inj equal
      rw [injective x y pair.1,ih ys pair.2]

private theorem mapped_not_perm {A B : Type} (fallback : A) (f : A→B) (xs ys : List A)
    (injective : ∀ x∈xs++ys,∀ y∈xs++ys,f x=f y→x=y)
    (different : ¬xs.Perm ys) : ¬(xs.map f).Perm (ys.map f) := by
  classical
  let recover := fun b => if h:∃ a,a∈xs++ys ∧ f a=b then Classical.choose h else fallback
  have inverse (a : A) (ha : a∈xs++ys) : recover (f a)=a := by
    have h : ∃ x,x∈xs++ys ∧ f x=f a:=⟨a,ha,rfl⟩
    simp only [recover,dite_eq_left h]
    exact injective _ (Classical.choose_spec h).1 a ha (Classical.choose_spec h).2
  have left (ls : List A) (subset : ∀ x∈ls,x∈xs++ys) : (ls.map f).map recover=ls := by
    rw [List.map_map]
    conv => rhs; rw [←List.map_id ls]
    apply List.map_congr_left
    intro x hx
    exact inverse x (subset x hx)
  intro h
  have mapped:=h.map recover
  rw [left xs (fun x hx=>List.mem_append_left _ hx),left ys (fun x hx=>List.mem_append_right _ hx)] at mapped
  exact different mapped

def busEncodeMessage {F K : Type} (embed : F→K) (tag : Nat→K) (message : Nat × List F) : List K :=
  message.2.map embed ++ [tag message.1]

/-- Bounded tags suffice: natural bus identifiers need not inject globally
into a finite field. Payload embedding and tag injectivity are separate. -/
theorem bus_encode_message_injective {F K : Type} (embed : F→K) (tag : Nat→K) (limit : Nat)
    (embedding : ∀ a b,embed a=embed b→a=b)
    (tags : ∀ a<limit,∀ b<limit,tag a=tag b→a=b)
    (x y : Nat × List F) (hx : x.1<limit) (hy : y.1<limit)
    (equal : busEncodeMessage embed tag x=busEncodeMessage embed tag y) : x=y := by
  obtain ⟨xb,xm⟩:=x
  obtain ⟨yb,ym⟩:=y
  have pair : xm.map embed=ym.map embed ∧ tag xb=tag yb := by simpa [busEncodeMessage] using equal
  have messages:=list_map_injective embed embedding xm ym pair.1
  have buses:=tags xb hx yb hy pair.2
  simp only [messages,buses]

/-- Concrete AIR natural imbalance implies a joint ideal challenge bound.
Public field values are unrestricted. Source/auxiliary authentication is not
assumed proved: this theorem starts with one fixed trace and public vector. -/
theorem bus_trace_joint_challenge_bound {F K : Type} [CommRing F] [DecidableEq F] [PubVal F] [Field K]
    (air : AirP) (tr : Trace F) (pub : List F) (embed : F→K) (tag : Nat→K)
    (limit width : Nat) (support : List (Nat × List F))
    (embedding : ∀ a b,embed a=embed b→a=b)
    (tags : ∀ a<limit,∀ b<limit,tag a=tag b→a=b)
    (nonzero : ∀ a<limit,tag a≠0)
    (covered : ∀ m,m∈busTraceMessages air tr pub true++busTraceMessages air tr pub false → m∈support)
    (shape : ∀ m∈support,m.1<limit ∧ m.2.length+1≤width)
    (unbalanced : ¬∀ b m,busCount air.toAir tr pub b true m+pubCount air pub b true m=
      busCount air.toAir tr pub b false m+pubCount air pub b false m)
    (alphas gammas : List K) (alphaDistinct : alphas.Nodup) (gammaDistinct : gammas.Nodup) :
    let send := (busTraceMessages air tr pub true).map (busEncodeMessage embed tag)
    let receive := (busTraceMessages air tr pub false).map (busEncodeMessage embed tag)
    count (alphas.flatMap (fun a=>gammas.map (fun g=>(a,g))))
      (fun pair=>((send.map (fp pair.1)).map (pair.2 - ·)).prod =
                  ((receive.map (fp pair.1)).map (pair.2 - ·)).prod) ≤
      support.length*width*gammas.length+alphas.length*
        max (busTraceMessages air tr pub true).length (busTraceMessages air tr pub false).length := by
  dsimp only
  have different:=mapped_not_perm (0,([]:List F)) (busEncodeMessage embed tag)
    (busTraceMessages air tr pub true) (busTraceMessages air tr pub false)
    (by
      intro x hx y hy equal
      exact bus_encode_message_injective embed tag limit embedding tags x y
        (shape x (covered x hx)).1 (shape y (covered y hy)).1 equal)
    (bus_trace_unbalanced_not_perm air tr pub unbalanced)
  have bound:=bus_tagged_joint_challenge_bound width
    ((busTraceMessages air tr pub true).map (busEncodeMessage embed tag))
    ((busTraceMessages air tr pub false).map (busEncodeMessage embed tag))
    (support.map (busEncodeMessage embed tag)) alphas gammas alphaDistinct gammaDistinct
    (by
      intro message member
      rw [←List.map_append] at member
      obtain ⟨original,ho,rfl⟩:=List.mem_map.mp member
      have hs:=covered original ho
      have dimensions:=shape original hs
      refine ⟨List.mem_map.mpr ⟨original,hs,rfl⟩,?_,original.2.map embed,tag original.1,rfl,
        nonzero original.1 dimensions.1⟩
      simpa [busEncodeMessage] using dimensions.2) different
  simpa only [List.length_map] using bound

open ZkFormal.Algebra

/-- The concrete extension embedding and bus+1 tags satisfy the generic
adapter assumptions for every bus below P-1 (the slice uses buses 0 through 3). -/
theorem bus_fp8_encoding_conditions :
    (∀ a b : Fp,Fp8.ofBase a=Fp8.ofBase b→a=b) ∧
    (∀ a<P-1,∀ b<P-1,((a+1:Nat):Fp8)=((b+1:Nat):Fp8)→a=b) ∧
    (∀ a<P-1,((a+1:Nat):Fp8)≠0) := by
  refine ⟨fun _ _ h=>Fp8.ofBase_inj h,?_,?_⟩
  · intro a ha b hb equal
    have h:=congrArg (fun x:Fp8=>x.c0.toNat) equal
    change (Fp.ofNat (a+1)).toNat=(Fp.ofNat (b+1)).toNat at h
    rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at h
    omega
  · intro a ha equal
    have h:=congrArg (fun x:Fp8=>x.c0.toNat) equal
    change (Fp.ofNat (a+1)).toNat=0 at h
    rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at h
    omega

/-- Concrete BabyBear/Ext8 natural-count-to-fingerprint bound. The fixed
trace and public vector remain explicit; no authenticated trace is invented. -/
theorem bus_trace_fp8_joint_bound
    (air : AirP) (tr : Trace Fp) (pub : List Fp) (width : Nat) (support : List (Nat × List Fp))
    (covered : ∀ m,m∈busTraceMessages air tr pub true++busTraceMessages air tr pub false → m∈support)
    (shape : ∀ m∈support,m.1<P-1 ∧ m.2.length+1≤width)
    (unbalanced : ¬∀ b m,busCount air.toAir tr pub b true m+pubCount air pub b true m=
      busCount air.toAir tr pub b false m+pubCount air pub b false m)
    (alphas gammas : List Fp8) (alphaDistinct : alphas.Nodup) (gammaDistinct : gammas.Nodup) :
    let encode := busEncodeMessage Fp8.ofBase (fun b=>((b+1:Nat):Fp8))
    let send := (busTraceMessages air tr pub true).map encode
    let receive := (busTraceMessages air tr pub false).map encode
    count (alphas.flatMap (fun a=>gammas.map (fun g=>(a,g))))
      (fun pair=>((send.map (fp pair.1)).map (pair.2 - ·)).prod =
                  ((receive.map (fp pair.1)).map (pair.2 - ·)).prod) ≤
      support.length*width*gammas.length+alphas.length*
        max (busTraceMessages air tr pub true).length (busTraceMessages air tr pub false).length := by
  exact bus_trace_joint_challenge_bound air tr pub Fp8.ofBase (fun b=>((b+1:Nat):Fp8))
    (P-1) width support bus_fp8_encoding_conditions.1 bus_fp8_encoding_conditions.2.1
    bus_fp8_encoding_conditions.2.2 covered shape unbalanced alphas gammas alphaDistinct gammaDistinct

end NearCompression
