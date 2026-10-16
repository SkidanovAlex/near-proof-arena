import ZkFormal.Air.Basic

/-! Exact finite preimage arithmetic for rejection sampling a field residue
from a 32-bit word. This does not assert uniformity or independence of hash
outputs, and makes no QROM or quantum-security claim. -/
set_option autoImplicit false
namespace NearCompression

def rejectionAccept (p w : Nat) : Prop := w<2*p

def rejectionValue (p w : Nat) : Nat := w%p

/-- The accepted preimages of residue a are exactly a and a+p. -/
theorem rejection_preimages (p a w : Nat) (hp : 0<p) (ha : a<p) :
    (rejectionAccept p w ∧ rejectionValue p w=a) ↔ w=a ∨ w=a+p := by
  constructor
  · intro h
    unfold rejectionAccept rejectionValue at h
    have divbound : w/p<2 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
    have decomposition := Nat.mod_add_div w p
    have small : ∀ k : Nat,k<2 → k=0 ∨ k=1 := by omega
    rcases small (w/p) divbound with hdiv | hdiv
    · left
      simp only [hdiv,Nat.mul_zero,Nat.add_zero] at decomposition
      omega
    · right
      simp only [hdiv,Nat.mul_one] at decomposition
      omega
  · intro h
    rcases h with rfl | rfl
    · exact ⟨by unfold rejectionAccept; omega, Nat.mod_eq_of_lt ha⟩
    · constructor
      · unfold rejectionAccept; omega
      · unfold rejectionValue
        simp [Nat.mod_eq_of_lt ha]

theorem rejection_preimages_distinct (p a : Nat) (hp : 0<p) : a≠a+p := by omega

/-- Both preimages fit the word space whenever the accepted interval does. -/
theorem rejection_preimages_word_bound (p a bits : Nat) (hp : 0<p) (ha : a<p)
    (fits : 2*p≤2^bits) : a<2^bits ∧ a+p<2^bits := by omega

/-- A concrete two-element preimage enumeration; no large range is evaluated. -/
def rejectionPreimages (p a : Nat) : List Nat := [a,a+p]

theorem rejection_preimages_mem (p a w : Nat) (hp : 0<p) (ha : a<p) :
    w∈rejectionPreimages p a ↔ rejectionAccept p w ∧ rejectionValue p w=a := by
  simp only [rejectionPreimages,List.mem_cons,List.not_mem_nil,or_false]
  exact (rejection_preimages p a w hp ha).symm

theorem rejection_preimages_nodup (p a : Nat) (hp : 0<p) :
    (rejectionPreimages p a).Nodup := by
  simp [rejectionPreimages,show p≠0 by omega]

theorem rejection_preimages_card (p a : Nat) : (rejectionPreimages p a).length=2 := rfl

/-- Every residue has the same exact number of accepted word preimages. -/
theorem rejection_equal_preimage_counts (p a b bits : Nat) (hp : 0<p)
    (ha : a<p) (hb : b<p) (fits : 2*p≤2^bits) :
    (rejectionPreimages p a).length=(rejectionPreimages p b).length ∧
    (∀ w,w∈rejectionPreimages p a ↔ w<2^bits ∧ rejectionAccept p w ∧ rejectionValue p w=a) ∧
    (∀ w,w∈rejectionPreimages p b ↔ w<2^bits ∧ rejectionAccept p w ∧ rejectionValue p w=b) := by
  refine ⟨rfl,?_,?_⟩
  all_goals
    intro w
    rw [rejection_preimages_mem _ _ _ hp (by assumption)]
    constructor
    · intro h; exact ⟨by have hw := h.1; unfold rejectionAccept at hw; omega,h⟩
    · exact fun h => h.2

/-- The concrete prime used by the diagnostic, proved by arithmetic only. -/
theorem rejection_prime32 (a w : Nat) (ha : a<2013265921) :
    (w<2^32 ∧ rejectionAccept 2013265921 w ∧ rejectionValue 2013265921 w=a) ↔
      w=a ∨ w=a+2013265921 := by
  have h := rejection_preimages 2013265921 a w (by omega) ha
  constructor
  · exact fun hw => h.mp hw.2
  · intro hw
    have accepted := h.mpr hw
    exact ⟨by have bound := accepted.1; unfold rejectionAccept at bound; omega,accepted⟩
/-- Literal accepted preimages filtered from the complete finite word space. -/
def rejectionWordPreimages (bits p a : Nat) : List Nat :=
  (List.range (2^bits)).filter (fun w => decide (w<2*p ∧ w%p=a))

theorem rejection_word_preimages_perm (bits p a : Nat) (hp : 0<p) (ha : a<p)
    (fits : 2*p≤2^bits) :
    (rejectionWordPreimages bits p a).Perm (rejectionPreimages p a) := by
  apply (List.perm_ext_iff_of_nodup _ (rejection_preimages_nodup p a hp)).mpr
  · intro w
    simp only [rejectionWordPreimages,List.mem_filter,List.mem_range,decide_eq_true_eq]
    rw [rejection_preimages_mem p a w hp ha]
    change (w<2^bits ∧ w<2*p ∧ w%p=a) ↔ w<2*p ∧ w%p=a
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨by omega,h⟩
  · exact List.nodup_range.filter _

/-- Exact cardinality two in the finite word space, without enumeration. -/
theorem rejection_word_preimages_card (bits p a : Nat) (hp : 0<p) (ha : a<p)
    (fits : 2*p≤2^bits) : (rejectionWordPreimages bits p a).length=2 :=
  (rejection_word_preimages_perm bits p a hp ha fits).length_eq

theorem rejection_prime32_card (a : Nat) (ha : a<2013265921) :
    (rejectionWordPreimages 32 2013265921 a).length=2 :=
  rejection_word_preimages_card 32 2013265921 a (by omega) ha (by omega)
theorem rejection_word_equal_counts (bits p a b : Nat) (hp : 0<p) (ha : a<p) (hb : b<p)
    (fits : 2*p≤2^bits) :
    (rejectionWordPreimages bits p a).length=(rejectionWordPreimages bits p b).length := by
  rw [rejection_word_preimages_card bits p a hp ha fits,rejection_word_preimages_card bits p b hp hb fits]
end NearCompression
