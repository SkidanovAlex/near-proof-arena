import NearCompression.WordModularProduct
namespace NearCompression

/-- Exact unsigned 128-bit addition from the low carry and two high additions.
The carry variables denote the MSB overflow bit, not the whole carry bitmap. -/
theorem word128_add_identity (ah al bh bl lo carry h0 overflow0 hi overflow1 : Nat)
    (low : al+bl=carry*2^64+lo)
    (high0 : ah+bh=overflow0*2^64+h0)
    (high1 : h0+carry=overflow1*2^64+hi)
    (no0 : overflow0=0) (no1 : overflow1=0) :
    (ah*2^64+al)+(bh*2^64+bl)=hi*2^64+lo := by
  subst overflow0; subst overflow1
  simp only [Nat.zero_mul,Nat.zero_add] at *
  omega

/-- Fused coefficient reduction permits a numerator larger than 64 bits.
Canonical remainder plus exact high/low identities determines its field value. -/
theorem word128_remainder_sound (numerator p q r nh nl qh ql lo carry hi : Nat)
    (num : numerator=nh*2^64+nl)
    (product : q*p=qh*2^64+ql)
    (low : ql+r=carry*2^64+lo)
    (high : qh+carry=hi)
    (sameHigh : nh=hi) (sameLow : nl=lo)
    (canonical : r<p) : numerator%p=r := by
  have identity : numerator=q*p+r := by omega
  rw [identity,Nat.add_mod]
  simp [Nat.mul_mod,Nat.mod_eq_of_lt canonical]

#print axioms word128_add_identity
#print axioms word128_remainder_sound
end NearCompression
