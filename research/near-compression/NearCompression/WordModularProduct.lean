import NearCompression.SHA384TranscriptDraw
namespace NearCompression

/-- The mathematical obligation for the word-circuit quotient/remainder gadget.
The identity must be over naturals, not merely modulo 2^64. -/
theorem canonical_product_remainder (a b q r p : Nat)
    (canonical : r < p) (identity : a*b = q*p+r) : a*b%p=r := by
  rw [identity, Nat.add_mod]
  simp [Nat.mul_mod, Nat.mod_eq_of_lt canonical]

/-- Explicit high-word and carry obligations convert the machine-word equations
into an integer identity. These premises still need a frontend refinement proof. -/
theorem word_product_identity (a b q r p lo hi qlo qhi sum carry : Nat)
    (product : a*b = hi*2^64+lo)
    (quotient : q*p = qhi*2^64+qlo)
    (addition : qlo+r = carry*2^64+sum)
    (high_zero : hi=0) (qhigh_zero : qhi=0) (carry_zero : carry=0)
    (equal_low : lo=sum) : a*b = q*p+r := by
  subst hi; subst qhi; subst carry
  simp only [Nat.zero_mul, Nat.zero_add] at *
  omega

/-- Canonical remainder uniquely determines the represented field product. -/
theorem word_product_modular_sound (a b q r p lo hi qlo qhi sum carry : Nat)
    (product : a*b = hi*2^64+lo)
    (quotient : q*p = qhi*2^64+qlo)
    (addition : qlo+r = carry*2^64+sum)
    (high_zero : hi=0) (qhigh_zero : qhi=0) (carry_zero : carry=0)
    (equal_low : lo=sum) (canonical : r<p) : a*b%p=r := by
  exact canonical_product_remainder a b q r p canonical
    (word_product_identity a b q r p lo hi qlo qhi sum carry
      product quotient addition high_zero qhigh_zero carry_zero equal_low)

#print axioms canonical_product_remainder
#print axioms word_product_identity
#print axioms word_product_modular_sound
end NearCompression
