import NearCompression.SHA512BitSemantics
import NearCompression.InstructionAddRange

/-! SHA-512 bit-function AIR, not a complete hash circuit. Inputs x,y,z occupy
columns0..191; bsig0,bsig1,ssig0,ssig1,ch,maj outputs occupy192..575. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound ZkFormal.Sha.View

def sha512XorExpr (a b : Expr) : Expr :=
  .add (.add a b) (.neg (.mul (.const 2) (.mul a b)))
def sha512Xor3Expr (a b c : Expr) : Expr := sha512XorExpr (sha512XorExpr a b) c
def sha512RotExpr (n bit : Nat) : Expr := .col ((bit + n) % 64) false
def sha512ShiftExpr (n bit : Nat) : Expr :=
  if bit + n < 64 then .col (bit + n) false else .const 0
def sha512ChoiceExpr (a b c : Expr) : Expr :=
  .add (.mul a b) (.mul (.add (.const 1) (.neg a)) c)
def sha512MajorityExpr (a b c : Expr) : Expr :=
  .add (.add (.add (.mul a b) (.mul a c)) (.mul b c))
    (.neg (.mul (.const 2) (.mul (.mul a b) c)))
def sha512BitsExpr (slot bit : Nat) : Expr :=
  match slot with
  | 0 => sha512Xor3Expr (sha512RotExpr 28 bit) (sha512RotExpr 34 bit) (sha512RotExpr 39 bit)
  | 1 => sha512Xor3Expr (sha512RotExpr 14 bit) (sha512RotExpr 18 bit) (sha512RotExpr 41 bit)
  | 2 => sha512Xor3Expr (sha512RotExpr 1 bit) (sha512RotExpr 8 bit) (sha512ShiftExpr 7 bit)
  | 3 => sha512Xor3Expr (sha512RotExpr 19 bit) (sha512RotExpr 61 bit) (sha512ShiftExpr 6 bit)
  | 4 => sha512ChoiceExpr (.col bit false) (.col (64 + bit) false) (.col (128 + bit) false)
  | _ => sha512MajorityExpr (.col bit false) (.col (64 + bit) false) (.col (128 + bit) false)
def sha512BitsFunction (slot x y z : Nat) : Nat :=
  match slot with
  | 0 => NearSpecV3.SHA512.bsig0 x
  | 1 => NearSpecV3.SHA512.bsig1 x
  | 2 => NearSpecV3.SHA512.ssig0 x
  | 3 => NearSpecV3.SHA512.ssig1 x
  | 4 => NearSpecV3.SHA512.ch x y z
  | _ => NearSpecV3.SHA512.maj x y z

def sha512BitsConstraints : List Expr :=
  (List.range 192).map instructionBitConstraint ++
    (List.range 6).flatMap (fun slot => (List.range 64).map (fun bit =>
      .add (.col (192 + 64 * slot + bit) false) (.neg (sha512BitsExpr slot bit))))
def sha512BitsTable : Table := ⟨576, sha512BitsConstraints, [], 22⟩
def sha512BitsHolds (row : Nat → Fp) : Prop :=
  ∀ e ∈ sha512BitsConstraints, e.evalWith (instructionAddEnv row) = 0
def sha512BitsWord (row : Nat → Fp) (base : Nat) : Nat :=
  ofBits (fun bit => (row (base + bit)).toNat) 64

theorem sha512_xor_field (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) :
    Fp.ofNat a + Fp.ofNat b + -(Fp.ofNat 2 * (Fp.ofNat a * Fp.ofNat b)) =
      Fp.ofNat ((a + b) % 2) := by
  have ca : a = 0 ∨ a = 1 := by omega
  have cb : b = 0 ∨ b = 1 := by omega
  rcases ca with ca | ca <;> rcases cb with cb | cb <;> subst a <;> subst b <;> decide

theorem sha512_choice_field (a b c : Nat) (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) :
    Fp.ofNat a * Fp.ofNat b + (Fp.ofNat 1 + -Fp.ofNat a) * Fp.ofNat c =
      Fp.ofNat ((a * b + ((a + 1) % 2) * c) % 2) := by
  have ca : a = 0 ∨ a = 1 := by omega
  have cb : b = 0 ∨ b = 1 := by omega
  have cc : c = 0 ∨ c = 1 := by omega
  rcases ca with ca | ca <;> rcases cb with cb | cb <;> rcases cc with cc | cc <;>
    subst a <;> subst b <;> subst c <;> decide

theorem sha512_majority_field (a b c : Nat) (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) :
    Fp.ofNat a * Fp.ofNat b + Fp.ofNat a * Fp.ofNat c + Fp.ofNat b * Fp.ofNat c +
      -(Fp.ofNat 2 * (Fp.ofNat a * Fp.ofNat b * Fp.ofNat c)) =
      Fp.ofNat (((a * b + a * c) % 2 + b * c) % 2) := by
  have ca : a = 0 ∨ a = 1 := by omega
  have cb : b = 0 ∨ b = 1 := by omega
  have cc : c = 0 ∨ c = 1 := by omega
  rcases ca with ca | ca <;> rcases cb with cb | cb <;> rcases cc with cc | cc <;>
    subst a <;> subst b <;> subst c <;> decide

theorem sha512_bits_input_boolean (row : Nat → Fp) (h : sha512BitsHolds row)
    (col : Nat) (hc : col < 192) : (row col).toNat ≤ 1 := by
  exact instruction_add_boolean_bound _ (h (instructionBitConstraint col)
    (List.mem_append_left _ (List.mem_map.mpr ⟨col, List.mem_range.mpr hc, rfl⟩)))
theorem sha512_bits_input_bound (row : Nat → Fp) (h : sha512BitsHolds row)
    (slot : Nat) (hs : slot < 3) : sha512BitsWord row (64 * slot) < 2 ^ 64 := by
  apply ofBits_lt
  intro bit hb
  exact sha512_bits_input_boolean row h _ (by omega)
theorem sha512_bits_input_bit (row : Nat → Fp) (h : sha512BitsHolds row)
    (slot bit : Nat) (hs : slot < 3) (hb : bit < 64) :
    row (64 * slot + bit) = Fp.ofNat (bt (sha512BitsWord row (64 * slot)) bit) := by
  have eq := bt_ofBits (fun k hk => sha512_bits_input_boolean row h (64 * slot + k) (by omega)) hb
  change bt (sha512BitsWord row (64 * slot)) bit = _ at eq
  rw [eq, Fp.ofNat_toNat]
theorem sha512_xor3_expr_eval (row : Nat → Fp) (a b c : Expr) (x y z bit : Nat)
    (ha : a.evalWith (instructionAddEnv row) = Fp.ofNat (bt x bit))
    (hb : b.evalWith (instructionAddEnv row) = Fp.ofNat (bt y bit))
    (hc : c.evalWith (instructionAddEnv row) = Fp.ofNat (bt z bit)) :
    (sha512Xor3Expr a b c).evalWith (instructionAddEnv row) = Fp.ofNat (bt (x ^^^ y ^^^ z) bit) := by
  simp only [sha512Xor3Expr, sha512XorExpr, Expr.evalWith, instructionAddEnv] at ha hb hc ⊢
  rw [ha, hb, hc]
  rw [sha512_xor_field _ _ (bt_le _ _) (bt_le _ _)]
  rw [sha512_xor_field _ _ (by omega) (bt_le _ _)]
  rw [bt_xor, bt_xor]

theorem sha512_rot_expr_eval (row : Nat → Fp) (x n bit : Nat)
    (hx : x < 2 ^ 64) (hn : n < 64) (hb : bit < 64)
    (bits : ∀ k, k < 64 → row k = Fp.ofNat (bt x k)) :
    (sha512RotExpr n bit).evalWith (instructionAddEnv row) = Fp.ofNat (bt (NearSpecV3.SHA512.rotr x n) bit) := by
  change row ((bit + n) % 64) = _
  rw [bits _ (Nat.mod_lt _ (by decide)), sha512_bt_rotr hx hn hb]

theorem sha512_shift_expr_eval (row : Nat → Fp) (x n bit : Nat)
    (hx : x < 2 ^ 64)
    (bits : ∀ k, k < 64 → row k = Fp.ofNat (bt x k)) :
    (sha512ShiftExpr n bit).evalWith (instructionAddEnv row) = Fp.ofNat (bt (x >>> n) bit) := by
  rw [bt_shiftRight, Nat.add_comm n bit]
  by_cases h : bit + n < 64
  · simp only [sha512ShiftExpr, if_pos h, Expr.evalWith, instructionAddEnv]
    exact bits _ h
  · simp only [sha512ShiftExpr, if_neg h, Expr.evalWith, instructionAddEnv]
    rw [bt_of_lt hx (by omega)]

theorem sha512_bits_expr_correct (row : Nat → Fp) (x y z slot bit : Nat)
    (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (hz : z < 2 ^ 64)
    (hs : slot < 6) (hb : bit < 64)
    (xb : ∀ k, k < 64 → row k = Fp.ofNat (bt x k))
    (yb : ∀ k, k < 64 → row (64 + k) = Fp.ofNat (bt y k))
    (zb : ∀ k, k < 64 → row (128 + k) = Fp.ofNat (bt z k)) :
    (sha512BitsExpr slot bit).evalWith (instructionAddEnv row) =
      Fp.ofNat (bt (sha512BitsFunction slot x y z) bit) := by
  have cases : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 ∨ slot = 4 ∨ slot = 5 := by omega
  rcases cases with hs | hs | hs | hs | hs | hs <;> subst slot
  · exact sha512_xor3_expr_eval row _ _ _ _ _ _ bit
      (sha512_rot_expr_eval row x 28 bit hx (by decide) hb xb)
      (sha512_rot_expr_eval row x 34 bit hx (by decide) hb xb)
      (sha512_rot_expr_eval row x 39 bit hx (by decide) hb xb)
  · exact sha512_xor3_expr_eval row _ _ _ _ _ _ bit
      (sha512_rot_expr_eval row x 14 bit hx (by decide) hb xb)
      (sha512_rot_expr_eval row x 18 bit hx (by decide) hb xb)
      (sha512_rot_expr_eval row x 41 bit hx (by decide) hb xb)
  · exact sha512_xor3_expr_eval row _ _ _ _ _ _ bit
      (sha512_rot_expr_eval row x 1 bit hx (by decide) hb xb)
      (sha512_rot_expr_eval row x 8 bit hx (by decide) hb xb)
      (sha512_shift_expr_eval row x 7 bit hx xb)
  · exact sha512_xor3_expr_eval row _ _ _ _ _ _ bit
      (sha512_rot_expr_eval row x 19 bit hx (by decide) hb xb)
      (sha512_rot_expr_eval row x 61 bit hx (by decide) hb xb)
      (sha512_shift_expr_eval row x 6 bit hx xb)
  · change row bit * row (64 + bit) + (Fp.ofNat 1 + -row bit) * row (128 + bit) = _
    rw [xb bit hb, yb bit hb, zb bit hb, sha512_choice_field _ _ _ (bt_le _ _) (bt_le _ _) (bt_le _ _)]
    exact congrArg Fp.ofNat (sha512_bt_ch hb).symm
  · change row bit * row (64 + bit) + row bit * row (128 + bit) + row (64 + bit) * row (128 + bit) +
      -(Fp.ofNat 2 * (row bit * row (64 + bit) * row (128 + bit))) = _
    rw [xb bit hb, yb bit hb, zb bit hb, sha512_majority_field _ _ _ (bt_le _ _) (bt_le _ _) (bt_le _ _)]
    exact congrArg Fp.ofNat (sha512_bt_maj x y z bit).symm

theorem sha512_bits_function_bound (x y z slot : Nat)
    (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (hz : z < 2 ^ 64) :
    sha512BitsFunction slot x y z < 2 ^ 64 := by
  cases slot with
  | zero => exact sha512_sig3_lt x 28 34 39
  | succ slot => cases slot with
    | zero => exact sha512_sig3_lt x 14 18 41
    | succ slot => cases slot with
      | zero => exact sha512_sigS_lt hx 1 8 7
      | succ slot => cases slot with
        | zero => exact sha512_sigS_lt hx 19 61 6
        | succ slot => cases slot with
          | zero => exact sha512_ch_lt x hy hz
          | succ slot => exact sha512_maj_lt x hy hz

theorem sha512_bits_output_bit (row : Nat → Fp) (h : sha512BitsHolds row)
    (slot bit : Nat) (hs : slot < 6) (hb : bit < 64) :
    row (192 + 64 * slot + bit) = Fp.ofNat (bt
      (sha512BitsFunction slot (sha512BitsWord row 0) (sha512BitsWord row 64) (sha512BitsWord row 128)) bit) := by
  have residual := h (.add (.col (192 + 64 * slot + bit) false) (.neg (sha512BitsExpr slot bit)))
    (List.mem_append_right _ (List.mem_flatMap.mpr ⟨slot, List.mem_range.mpr hs,
      List.mem_map.mpr ⟨bit, List.mem_range.mpr hb, rfl⟩⟩))
  change row (192 + 64 * slot + bit) + -(sha512BitsExpr slot bit).evalWith (instructionAddEnv row) = 0 at residual
  have eval := sha512_bits_expr_correct row (sha512BitsWord row 0) (sha512BitsWord row 64)
    (sha512BitsWord row 128) slot bit
    (sha512_bits_input_bound row h 0 (by decide))
    (sha512_bits_input_bound row h 1 (by decide))
    (sha512_bits_input_bound row h 2 (by decide)) hs hb
    (by intro k hk; simpa only [Nat.mul_zero, Nat.zero_add] using sha512_bits_input_bit row h 0 k (by decide) hk)
    (fun k hk => sha512_bits_input_bit row h 1 k (by decide) hk)
    (fun k hk => sha512_bits_input_bit row h 2 k (by decide) hk)
  rw [eval] at residual
  grind

/-- Concrete polynomial satisfaction implies each actual SHA-512 bit function. -/
theorem sha512_bits_output (row : Nat → Fp) (h : sha512BitsHolds row)
    (slot : Nat) (hs : slot < 6) :
    sha512BitsWord row (192 + 64 * slot) =
      sha512BitsFunction slot (sha512BitsWord row 0) (sha512BitsWord row 64) (sha512BitsWord row 128) := by
  have bits : ∀ bit, bit < 64 → (row (192 + 64 * slot + bit)).toNat = bt
      (sha512BitsFunction slot (sha512BitsWord row 0) (sha512BitsWord row 64) (sha512BitsWord row 128)) bit := by
    intro bit hb
    rw [sha512_bits_output_bit row h slot bit hs hb, Fp.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have hbit := bt_le (sha512BitsFunction slot (sha512BitsWord row 0) (sha512BitsWord row 64)
      (sha512BitsWord row 128)) bit
    unfold ZkFormal.Algebra.P
    omega
  unfold sha512BitsWord
  rw [ofBits_congr bits, ofBits_bt]
  apply Nat.mod_eq_of_lt
  exact sha512_bits_function_bound _ _ _ slot
    (sha512_bits_input_bound row h 0 (by decide))
    (sha512_bits_input_bound row h 1 (by decide))
    (sha512_bits_input_bound row h 2 (by decide))

def sha512BitsInput (x y z : UInt64) (slot : Nat) : Nat :=
  match slot with | 0 => x.toNat | 1 => y.toNat | _ => z.toNat

def sha512BitsWitness (x y z : UInt64) (col : Nat) : Fp :=
  if col < 192 then Fp.ofNat (bt (sha512BitsInput x y z (col / 64)) (col % 64)) else
    Fp.ofNat (bt (sha512BitsFunction ((col - 192) / 64) x.toNat y.toNat z.toNat) ((col - 192) % 64))

theorem sha512_bits_witness_input_bit (x y z : UInt64) (slot bit : Nat)
    (hs : slot < 3) (hb : bit < 64) :
    sha512BitsWitness x y z (64 * slot + bit) = Fp.ofNat (bt (sha512BitsInput x y z slot) bit) := by
  have hc : 64 * slot + bit < 192 := by omega
  have hd : (64 * slot + bit) / 64 = slot := by omega
  have hm : (64 * slot + bit) % 64 = bit := by omega
  simp only [sha512BitsWitness, if_pos hc, hd, hm]

theorem sha512_bits_witness_output_bit (x y z : UInt64) (slot bit : Nat)
    (hb : bit < 64) :
    sha512BitsWitness x y z (192 + 64 * slot + bit) =
      Fp.ofNat (bt (sha512BitsFunction slot x.toNat y.toNat z.toNat) bit) := by
  have hc : ¬192 + 64 * slot + bit < 192 := by omega
  have hd : (192 + 64 * slot + bit - 192) / 64 = slot := by omega
  have hm : (192 + 64 * slot + bit - 192) % 64 = bit := by omega
  simp only [sha512BitsWitness, if_neg hc, hd, hm]

theorem sha512_bits_witness_holds (x y z : UInt64) : sha512BitsHolds (sha512BitsWitness x y z) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨col, hc, he⟩ := List.mem_map.mp he
    subst e
    have hc' := List.mem_range.mp hc
    change sha512BitsWitness x y z col * (sha512BitsWitness x y z col + -Fp.ofNat 1) = 0
    simp only [sha512BitsWitness, if_pos hc']
    have hb := bt_le (sha512BitsInput x y z (col / 64)) (col % 64)
    have cases : bt (sha512BitsInput x y z (col / 64)) (col % 64) = 0 ∨
      bt (sha512BitsInput x y z (col / 64)) (col % 64) = 1 := by omega
    rcases cases with h | h <;> rw [h] <;> decide
  · obtain ⟨slot, hs, he⟩ := List.mem_flatMap.mp he
    obtain ⟨bit, hb, he⟩ := List.mem_map.mp he
    subst e
    have eval := sha512_bits_expr_correct (sha512BitsWitness x y z) x.toNat y.toNat z.toNat slot bit
      x.toNat_lt y.toNat_lt z.toNat_lt (List.mem_range.mp hs) (List.mem_range.mp hb)
      (by intro k hk; simpa only [Nat.mul_zero, Nat.zero_add, sha512BitsInput] using sha512_bits_witness_input_bit x y z 0 k (by decide) hk)
      (fun k hk => sha512_bits_witness_input_bit x y z 1 k (by decide) hk)
      (fun k hk => sha512_bits_witness_input_bit x y z 2 k (by decide) hk)
    change sha512BitsWitness x y z (192 + 64 * slot + bit) +
      -(sha512BitsExpr slot bit).evalWith (instructionAddEnv (sha512BitsWitness x y z)) = 0
    rw [sha512_bits_witness_output_bit x y z slot bit (List.mem_range.mp hb), eval]
    grind

set_option maxRecDepth 32768 in
theorem sha512_bits_table_wf : sha512BitsTable.wf ⟨[sha512BitsTable], 0, 0⟩ 3 = true := by decide

set_option maxRecDepth 32768 in
theorem sha512_bits_table_size : sha512BitsTable.width = 576 ∧ sha512BitsTable.constraints.length = 576 := by decide

theorem sha512_bits_witness_input (x y z : UInt64) (slot : Nat) (hs : slot < 3) :
    sha512BitsWord (sha512BitsWitness x y z) (64 * slot) = sha512BitsInput x y z slot := by
  have bits : ∀ bit, bit < 64 → (sha512BitsWitness x y z (64 * slot + bit)).toNat =
      bt (sha512BitsInput x y z slot) bit := by
    intro bit hb
    rw [sha512_bits_witness_input_bit x y z slot bit hs hb, Fp.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have h := bt_le (sha512BitsInput x y z slot) bit
    unfold ZkFormal.Algebra.P
    omega
  unfold sha512BitsWord
  rw [ofBits_congr bits, ofBits_bt]
  apply Nat.mod_eq_of_lt
  cases slot with
  | zero => exact x.toNat_lt
  | succ slot => cases slot with
    | zero => exact y.toNat_lt
    | succ slot => exact z.toNat_lt

end NearCompression
