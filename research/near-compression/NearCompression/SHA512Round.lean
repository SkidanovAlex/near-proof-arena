import NearCompression.SHA512Relocate
import NearCompression.SHA512Bits
import NearCompression.SHA512AddBridge

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound ZkFormal.Sha.View

/-- Field evaluation of a bit-reconstruction expression, without a no-wrap
assumption. The later sixteen-bit bound makes its integer decoding exact. -/
theorem sha512_bit_expr_field (row : Nat → Fp) (base n : Nat) :
    (instructionBitExpr base n).evalWith (instructionAddEnv row) =
      Fp.ofNat (ofBits (fun bit => (row (base + bit)).toNat) n) := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih =>
    have split : ofBits (fun bit => (row (base + bit)).toNat) (n + 1) =
        (row base).toNat + 2 * ofBits (fun bit => (row (base + 1 + bit)).toNat) n := by
      rw [show n + 1 = 1 + n by omega, ofBits_add]
      simp only [ofBits, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul, Nat.pow_one]
      congr 2
      apply ofBits_congr
      intro bit _
      rw [Nat.add_assoc]
    change row base + Fp.ofNat 2 * (instructionBitExpr (base + 1) n).evalWith (instructionAddEnv row) = _
    rw [ih, split]
    have ca (a b : Nat) : Fp.ofNat (a + b) = Fp.ofNat a + Fp.ofNat b :=
      Lean.Grind.Semiring.natCast_add a b
    have cm (a b : Nat) : Fp.ofNat (a * b) = Fp.ofNat a * Fp.ofNat b :=
      Lean.Grind.Semiring.natCast_mul a b
    rw [ca, cm, Fp.ofNat_toNat]

/-- Four sixteen-bit groups reconstruct a full word without field aliasing. -/
theorem sha512_word_bits_split (row : Nat → Fp) (base : Nat) :
    sha512BitsWord row base =
      ofBits (fun bit => (row (base + bit)).toNat) 16 +
      65536 * ofBits (fun bit => (row (base + 16 + bit)).toNat) 16 +
      4294967296 * ofBits (fun bit => (row (base + 32 + bit)).toNat) 16 +
      281474976710656 * ofBits (fun bit => (row (base + 48 + bit)).toNat) 16 := by
  unfold sha512BitsWord
  rw [show 64 = 48 + 16 from rfl, ofBits_add,
      show 48 = 32 + 16 from rfl, ofBits_add,
      show 32 = 16 + 16 from rfl, ofBits_add]
  simp only [Nat.add_assoc]

theorem sha512_bits_output_boolean (row : Nat → Fp) (h : sha512BitsHolds row)
    (slot bit : Nat) (hs : slot < 6) (hb : bit < 64) :
    (row (192 + 64 * slot + bit)).toNat ≤ 1 := by
  rw [sha512_bits_output_bit row h slot bit hs hb, Fp.toNat_ofNat]
  have hbit := bt_le (sha512BitsFunction slot (sha512BitsWord row 0)
    (sha512BitsWord row 64) (sha512BitsWord row 128)) bit
  have hp : bt (sha512BitsFunction slot (sha512BitsWord row 0)
    (sha512BitsWord row 64) (sha512BitsWord row 128)) bit < ZkFormal.Algebra.P := by
    unfold ZkFormal.Algebra.P; omega
  rwa [Nat.mod_eq_of_lt hp]

/-- A field equality to a sixteen-bit reconstruction binds the exact integer
limb, because the reconstructed integer is below BabyBear's modulus. -/
theorem sha512_bit_limb_binding (row : Nat → Fp) (target source : Nat)
    (boolean : ∀ bit, bit < 16 → (row (source + bit)).toNat ≤ 1)
    (eq : row target = (instructionBitExpr source 16).evalWith (instructionAddEnv row)) :
    (row target).toNat = ofBits (fun bit => (row (source + bit)).toNat) 16 := by
  rw [sha512_bit_expr_field] at eq
  rw [eq, Fp.toNat_ofNat]
  have bound := ofBits_lt boolean
  apply Nat.mod_eq_of_lt
  change ofBits (fun bit => (row (source + bit)).toNat) 16 < 65536 at bound
  unfold ZkFormal.Algebra.P
  omega

theorem sha512_bit_word_binding (row : Nat → Fp) (target source : Nat)
    (boolean : ∀ bit, bit < 64 → (row (source + bit)).toNat ≤ 1)
    (eqs : ∀ limb, limb < 4 → row (target + limb) =
      (instructionBitExpr (source + 16 * limb) 16).evalWith (instructionAddEnv row)) :
    instructionAdd64Word row target = sha512BitsWord row source := by
  have limb (i : Nat) (hi : i < 4) :
      (row (target + i)).toNat = ofBits (fun bit => (row (source + 16 * i + bit)).toNat) 16 := by
    apply sha512_bit_limb_binding row (target + i) (source + 16 * i) _ (eqs i hi)
    intro bit hb
    have h := boolean (16 * i + bit) (by omega)
    simpa only [Nat.add_assoc] using h
  have l0 := limb 0 (by decide)
  have l1 := limb 1 (by decide)
  have l2 := limb 2 (by decide)
  have l3 := limb 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul] at l0 l1 l2 l3
  rw [sha512_word_bits_split]
  unfold instructionAdd64Word
  rw [l0, l1, l2, l3]

def sha512RoundAddBase (i : Nat) : Nat := 1152 + 208 * i

def sha512RoundBitsRow (row : Nat → Fp) (i : Nat) : Nat → Fp := fun col => row (576 * i + col)
def sha512RoundAddRow (row : Nat → Fp) (i : Nat) : Nat → Fp := fun col => row (sha512RoundAddBase i + col)

structure SHA512RoundWire where
  target : Nat
  source : Nat
  bitSource : Bool
  deriving DecidableEq

def sha512RoundWireExpr (wire : SHA512RoundWire) (limb : Nat) : Expr :=
  if wire.bitSource then instructionBitExpr (wire.source + 16 * limb) 16
  else .col (wire.source + limb) false

def sha512RoundWireConstraints (wire : SHA512RoundWire) : List Expr :=
  (List.range 4).map (fun limb => .add (.col (wire.target + limb) false)
    (.neg (sha512RoundWireExpr wire limb)))

/-- Ten word dependencies, each enforced through four sixteen-bit limbs. -/
def sha512RoundWires : List SHA512RoundWire := [
  ⟨1156, 832, true⟩, ⟨1360, 1160, false⟩, ⟨1364, 1024, true⟩,
  ⟨1568, 1368, false⟩, ⟨1776, 1576, false⟩,
  ⟨1984, 192, true⟩, ⟨1988, 512, true⟩,
  ⟨2192, 1784, false⟩, ⟨2196, 1992, false⟩, ⟨2404, 1784, false⟩]

/-- The other round words are free constrained inputs, not unconstrained host
computations: a,b,c,e,f,g are bit vectors; d,h,k,w are adder operands. -/
def sha512RoundVars (row : Nat → Fp) : NearSpecV3.SHA512.Vars := {
  a := sha512BitsWord (sha512RoundBitsRow row 0) 0
  b := sha512BitsWord (sha512RoundBitsRow row 0) 64
  c := sha512BitsWord (sha512RoundBitsRow row 0) 128
  d := instructionAdd64Word (sha512RoundAddRow row 6) 0
  e := sha512BitsWord (sha512RoundBitsRow row 1) 0
  f := sha512BitsWord (sha512RoundBitsRow row 1) 64
  g := sha512BitsWord (sha512RoundBitsRow row 1) 128
  h := instructionAdd64Word (sha512RoundAddRow row 0) 0 }

def sha512RoundK (row : Nat → Fp) : Nat := instructionAdd64Word (sha512RoundAddRow row 2) 4
def sha512RoundW (row : Nat → Fp) : Nat := instructionAdd64Word (sha512RoundAddRow row 3) 4

def sha512RoundComponents : List (Nat × List Expr) :=
  [(0, sha512BitsConstraints), (576, sha512BitsConstraints)] ++
    (List.range 7).map (fun i => (sha512RoundAddBase i, instructionAdd64Constraints))

def sha512RoundConstraints : List Expr :=
  sha512RoundComponents.flatMap (fun component => component.2.map (sha512RelocateExpr component.1)) ++
    sha512RoundWires.flatMap sha512RoundWireConstraints

def sha512RoundTable : Table := ⟨2608, sha512RoundConstraints, [], 22⟩

def sha512RoundHolds (row : Nat → Fp) : Prop :=
  ∀ e ∈ sha512RoundConstraints, e.evalWith (instructionAddEnv row) = 0

theorem sha512_round_component_holds (row : Nat → Fp) (h : sha512RoundHolds row)
    (offset : Nat) (constraints : List Expr)
    (component : (offset, constraints) ∈ sha512RoundComponents) :
    ∀ e ∈ constraints, e.evalWith (instructionAddEnv (fun c => row (offset + c))) = 0 := by
  intro e he
  have hv := h (sha512RelocateExpr offset e) (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨(offset, constraints), component, List.mem_map.mpr ⟨e, he, rfl⟩⟩))
  rwa [sha512_relocate_eval] at hv

theorem sha512_round_bits_holds (row : Nat → Fp) (h : sha512RoundHolds row)
    (i : Nat) (hi : i < 2) : sha512BitsHolds (sha512RoundBitsRow row i) := by
  apply sha512_round_component_holds row h (576 * i) sha512BitsConstraints
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with hi | hi <;> subst i <;> simp [sha512RoundComponents]

theorem sha512_round_add_holds (row : Nat → Fp) (h : sha512RoundHolds row)
    (i : Nat) (hi : i < 7) : instructionAdd64Holds (sha512RoundAddRow row i) := by
  apply sha512_round_component_holds row h (sha512RoundAddBase i) instructionAdd64Constraints
  exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

theorem sha512_round_wire_limb (row : Nat → Fp) (h : sha512RoundHolds row)
    (wire : SHA512RoundWire) (hw : wire ∈ sha512RoundWires) (limb : Nat) (hl : limb < 4) :
    row (wire.target + limb) = (sha512RoundWireExpr wire limb).evalWith (instructionAddEnv row) := by
  have hv := h (.add (.col (wire.target + limb) false) (.neg (sha512RoundWireExpr wire limb)))
    (List.mem_append_right _ (List.mem_flatMap.mpr ⟨wire, hw,
      List.mem_map.mpr ⟨limb, List.mem_range.mpr hl, rfl⟩⟩))
  change row (wire.target + limb) + -(sha512RoundWireExpr wire limb).evalWith (instructionAddEnv row) = 0 at hv
  grind

theorem sha512_round_limb_word_wire (row : Nat → Fp) (h : sha512RoundHolds row)
    (target source : Nat) (hw : ⟨target, source, false⟩ ∈ sha512RoundWires) :
    instructionAdd64Word row target = instructionAdd64Word row source := by
  have eqs (i : Nat) (hi : i < 4) : row (target + i) = row (source + i) :=
    sha512_round_wire_limb row h _ hw i hi
  have h0 := eqs 0 (by decide)
  have h1 := eqs 1 (by decide)
  have h2 := eqs 2 (by decide)
  have h3 := eqs 3 (by decide)
  simp only [Nat.add_zero] at h0
  simp only [instructionAdd64Word, h0, h1, h2, h3]

theorem sha512_round_bit_word_wire (row : Nat → Fp) (h : sha512RoundHolds row)
    (target bitRow slot : Nat) (hi : bitRow < 2) (hs : slot < 6)
    (hw : ⟨target, 576 * bitRow + (192 + 64 * slot), true⟩ ∈ sha512RoundWires) :
    instructionAdd64Word row target = sha512BitsWord (sha512RoundBitsRow row bitRow) (192 + 64 * slot) := by
  have boolean (bit : Nat) (hb : bit < 64) :
      (row (576 * bitRow + (192 + 64 * slot) + bit)).toNat ≤ 1 := by
    have hb' := sha512_bits_output_boolean (sha512RoundBitsRow row bitRow)
      (sha512_round_bits_holds row h bitRow hi) slot bit hs hb
    simpa only [sha512RoundBitsRow, Nat.add_assoc] using hb'
  have eq := sha512_bit_word_binding row target (576 * bitRow + (192 + 64 * slot)) boolean
    (fun limb hl => sha512_round_wire_limb row h _ hw limb hl)
  simpa only [sha512BitsWord, sha512RoundBitsRow, Nat.add_assoc] using eq

/-- All seven addition inputs are bound by actual field constraints to the
proper bit-function outputs or prior addition results. -/
theorem sha512_round_inputs (row : Nat → Fp) (h : sha512RoundHolds row) :
    ∀ i, i < 7 → instructionAdd64Word (sha512RoundAddRow row i) 0 =
      (sha512RoundAddInputs (sha512RoundVars row) (sha512RoundK row) (sha512RoundW row)
        (sha512RoundAddRow row) i).1 ∧
      instructionAdd64Word (sha512RoundAddRow row i) 4 =
      (sha512RoundAddInputs (sha512RoundVars row) (sha512RoundK row) (sha512RoundW row)
        (sha512RoundAddRow row) i).2 := by
  have b0 := sha512_round_bits_holds row h 0 (by decide)
  have b1 := sha512_round_bits_holds row h 1 (by decide)
  have w0 := sha512_round_bit_word_wire row h 1156 1 1 (by decide) (by decide) (by decide)
  have w1 := sha512_round_limb_word_wire row h 1360 1160 (by decide)
  have w2 := sha512_round_bit_word_wire row h 1364 1 4 (by decide) (by decide) (by decide)
  have w3 := sha512_round_limb_word_wire row h 1568 1368 (by decide)
  have w4 := sha512_round_limb_word_wire row h 1776 1576 (by decide)
  have w5 := sha512_round_bit_word_wire row h 1984 0 0 (by decide) (by decide) (by decide)
  have w6 := sha512_round_bit_word_wire row h 1988 0 5 (by decide) (by decide) (by decide)
  have w7 := sha512_round_limb_word_wire row h 2192 1784 (by decide)
  have w8 := sha512_round_limb_word_wire row h 2196 1992 (by decide)
  have w9 := sha512_round_limb_word_wire row h 2404 1784 (by decide)
  rw [sha512_bits_output _ b1 1 (by decide)] at w0
  rw [sha512_bits_output _ b1 4 (by decide)] at w2
  rw [sha512_bits_output _ b0 0 (by decide)] at w5
  rw [sha512_bits_output _ b0 5 (by decide)] at w6
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases cases with hi | hi | hi | hi | hi | hi | hi <;> subst i
  all_goals simp only [sha512RoundAddInputs, sha512RoundVars, sha512RoundK, sha512RoundW,
    sha512BitsFunction] at w0 w2 w5 w6 ⊢
  all_goals simp only [instructionAdd64Word, sha512RoundAddRow, sha512RoundAddBase,
    Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd] at w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 ⊢
  all_goals constructor <;> first | trivial | assumption

/-- Round soundness has no external sigma/ch/maj or intermediate wiring premise. -/
theorem sha512_round_sound (row : Nat → Fp) (h : sha512RoundHolds row) :
    (NearSpecV3.SHA512.round (sha512RoundVars row) (sha512RoundK row) (sha512RoundW row)).a =
      instructionAdd64Word (sha512RoundAddRow row 5) 8 ∧
    (NearSpecV3.SHA512.round (sha512RoundVars row) (sha512RoundK row) (sha512RoundW row)).e =
      instructionAdd64Word (sha512RoundAddRow row 6) 8 :=
  sha512_round_addition_composition _ _ _ _ (sha512_round_add_holds row h) (sha512_round_inputs row h)

def sha512RoundOutput (row : Nat → Fp) : NearSpecV3.SHA512.Vars := {
  a := instructionAdd64Word (sha512RoundAddRow row 5) 8
  b := (sha512RoundVars row).a
  c := (sha512RoundVars row).b
  d := (sha512RoundVars row).c
  e := instructionAdd64Word (sha512RoundAddRow row 6) 8
  f := (sha512RoundVars row).e
  g := (sha512RoundVars row).f
  h := (sha512RoundVars row).g }

theorem sha512_round_full_output (row : Nat → Fp) (h : sha512RoundHolds row) :
    NearSpecV3.SHA512.round (sha512RoundVars row) (sha512RoundK row) (sha512RoundW row) =
      sha512RoundOutput row := by
  have result := sha512_round_sound row h
  simp only [NearSpecV3.SHA512.round] at result
  simp only [NearSpecV3.SHA512.round, sha512RoundOutput, result.1, result.2]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem sha512_round_table_wf : sha512RoundTable.wf ⟨[sha512RoundTable], 0, 0⟩ 3 = true := by decide

set_option maxRecDepth 65536 in
theorem sha512_round_table_size :
    sha512RoundTable.width = 2608 ∧ sha512RoundTable.constraints.length = 2676 := by decide

end NearCompression
