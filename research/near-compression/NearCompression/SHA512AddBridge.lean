import NearCompression.InstructionAdd64
import NearSpecV3.SHA512

namespace NearCompression
open NearSpecV3.Wasm ZkFormal.Algebra

/-- The same range-constrained addition implements SHA-512's actual word helper. -/
theorem sha512_add_air_sound (row : Nat → Fp) (h : instructionAdd64Holds row) :
    NearSpecV3.SHA512.add64 (instructionAdd64Word row 0) (instructionAdd64Word row 4) =
      instructionAdd64Word row 8 := by
  have hb := instruction_add64_binop row h
  simpa only [Num.binop, Option.some.injEq, NearSpecV3.SHA512.add64] using hb

/-- Input wiring for the seven binary additions in a SHA-512 round. Sigma,
choice and majority outputs are supplied by the actual specification here;
their bit-operation AIR constraints are a separate obligation. -/
def sha512RoundAddInputs (v : NearSpecV3.SHA512.Vars) (k w : Nat)
    (rows : Nat → Nat → Fp) : Nat → Nat × Nat
  | 0 => (v.h, NearSpecV3.SHA512.bsig1 v.e)
  | 1 => (instructionAdd64Word (rows 0) 8, NearSpecV3.SHA512.ch v.e v.f v.g)
  | 2 => (instructionAdd64Word (rows 1) 8, k)
  | 3 => (instructionAdd64Word (rows 2) 8, w)
  | 4 => (NearSpecV3.SHA512.bsig0 v.a, NearSpecV3.SHA512.maj v.a v.b v.c)
  | 5 => (instructionAdd64Word (rows 3) 8, instructionAdd64Word (rows 4) 8)
  | 6 => (v.d, instructionAdd64Word (rows 3) 8)
  | _ => (0, 0)

/-- Seven correctly wired addition rows produce the exact two updated round
words. This proves composition, not the missing SHA-512 boolean/rotation AIR. -/
theorem sha512_round_addition_composition (v : NearSpecV3.SHA512.Vars) (k w : Nat)
    (rows : Nat → Nat → Fp)
    (holds : ∀ i, i < 7 → instructionAdd64Holds (rows i))
    (inputs : ∀ i, i < 7 →
      instructionAdd64Word (rows i) 0 = (sha512RoundAddInputs v k w rows i).1 ∧
      instructionAdd64Word (rows i) 4 = (sha512RoundAddInputs v k w rows i).2) :
    (NearSpecV3.SHA512.round v k w).a = instructionAdd64Word (rows 5) 8 ∧
    (NearSpecV3.SHA512.round v k w).e = instructionAdd64Word (rows 6) 8 := by
  have eqs (i : Nat) (hi : i < 7) :
      NearSpecV3.SHA512.add64 (sha512RoundAddInputs v k w rows i).1
        (sha512RoundAddInputs v k w rows i).2 = instructionAdd64Word (rows i) 8 := by
    have h := sha512_add_air_sound (rows i) (holds i hi)
    rw [(inputs i hi).1, (inputs i hi).2] at h
    exact h
  have h0 := eqs 0 (by decide)
  have h1 := eqs 1 (by decide)
  have h2 := eqs 2 (by decide)
  have h3 := eqs 3 (by decide)
  have h4 := eqs 4 (by decide)
  have h5 := eqs 5 (by decide)
  have h6 := eqs 6 (by decide)
  simp only [sha512RoundAddInputs] at h0 h1 h2 h3 h4 h5 h6
  simp only [NearSpecV3.SHA512.round, h0, h1, h2, h3, h4, h5, h6, and_self]

end NearCompression
