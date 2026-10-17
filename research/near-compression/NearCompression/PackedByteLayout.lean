import NearCompression.PackedByteMacro

/-! Concrete column decoding for EXEC and CODE. Range and whole-AIR balance
remain premises of the eventual refinement; this module does not claim them. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra

inductive PackedSlot where
  | scalar (column : Nat)
  | byte (column bit : Nat)
  deriving DecidableEq, Repr

def packedExecRegions : List (Nat × Nat) :=
  [(43,256),(299,64),(363,64),(431,32),(470,32),(502,64)]
def packedCodeRegions : List (Nat × Nat) := [(69,32),(101,64)]

def packedColumnIndex (regions : List (Nat × Nat)) (c : Nat) : Nat :=
  c - (regions.map (fun (s,n) => 7 * min ((c-s)/8) (n/8))).sum

def packedColumnSlot (regions : List (Nat × Nat)) (c : Nat) : PackedSlot :=
  match regions.find? (fun (s,n) => s≤c && c<s+n) with
  | none => .scalar (packedColumnIndex regions c)
  | some (s,_) => .byte (packedColumnIndex regions (s+8*((c-s)/8))) ((c-s)%8)

def packedMacroBases (regions : List (Nat × Nat)) : List Nat :=
  regions.flatMap (fun (s,n) => (List.range (n/16)).map (fun i=>s+16*i))

def PackedLayoutConsistent (regions : List (Nat × Nat)) : Prop :=
  ∀ base ∈ packedMacroBases regions, ∀ k ∈ List.range 16,
    packedColumnSlot regions (base+k) =
      .byte (packedColumnIndex regions (if k<8 then base else base+8))
        (if k<8 then k else k-8)

instance (regions : List (Nat × Nat)) : Decidable (PackedLayoutConsistent regions) :=
  inferInstanceAs (Decidable (∀ base ∈ packedMacroBases regions, ∀ k ∈ List.range 16, _))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem packed_exec_layout_consistent : PackedLayoutConsistent packedExecRegions := by decide
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem packed_code_layout_consistent : PackedLayoutConsistent packedCodeRegions := by decide

def packedLiftEnv (regions : List (Nat × Nat)) (packed : Env Fp) : Env Fp :=
  {packed with col:=fun c nx => match packedColumnSlot regions c with
    | .scalar j => packed.col j nx
    | .byte j bit => Fp.ofNat ((packed.col j nx).toNat/2^bit%2)}

theorem packed_lift_shared (regions : List (Nat × Nat)) (packed : Env Fp) :
    PackedEnvAgreement (packedLiftEnv regions packed) packed := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem packed_lift_scalar (regions : List (Nat × Nat)) (packed : Env Fp)
    (c j : Nat) (nx : Bool) (slot : packedColumnSlot regions c=.scalar j) :
    (packedLiftEnv regions packed).col c nx=packed.col j nx := by
  simp [packedLiftEnv,slot]

/-- All macro bit-column premises are discharged by the concrete layout
consistency check, for an arbitrary packed environment and either row. -/
theorem packed_layout_macro_eval (regions : List (Nat × Nat))
    (consistent : PackedLayoutConsistent regions) (packed : Env Fp)
    (base : Nat) (member : base ∈ packedMacroBases regions) (nx : Bool)
    (hn : packed.ofNat=Fp.ofNat) (ha : packed.add=(·+·)) (hm : packed.mul=(·*·))
    (hl : (packed.col (packedColumnIndex regions base) nx).toNat<256)
    (hh : (packed.col (packedColumnIndex regions (base+8)) nx).toNat<256) :
    (packedTargetLimb (packedColumnIndex regions base)
      (packedColumnIndex regions (base+8)) nx).evalWith packed =
    (packedSourceLimb base nx).evalWith (packedLiftEnv regions packed) := by
  apply packed_byte_macro_eval (packedLiftEnv regions packed) packed base
    (packedColumnIndex regions base) (packedColumnIndex regions (base+8))
    _ _ nx hn ha hm hn ha hm hl hh
  · intro k hk
    have shape := consistent base member k (List.mem_range.mpr hk)
    simp only [packedLiftEnv,shape]
    split <;> rfl
  · exact (Fp.ofNat_toNat _).symm
  · exact (Fp.ofNat_toNat _).symm

/-- Every decoded bit is Boolean, regardless of the packed byte's range.
Range is needed for limb equality, not for Booleanity of extracted bits. -/
theorem packed_lift_bit_boolean (regions : List (Nat × Nat)) (packed : Env Fp)
    (c j bit : Nat) (nx : Bool) (slot : packedColumnSlot regions c=.byte j bit) :
    let b := (packedLiftEnv regions packed).col c nx
    b*(b-1)=0 := by
  simp only [packedLiftEnv,slot]
  have bound := Nat.mod_lt ((packed.col j nx).toNat/2^bit) (by decide : 0<2)
  have cases : (packed.col j nx).toNat/2^bit%2=0 ∨
      (packed.col j nx).toNat/2^bit%2=1 := by omega
  rcases cases with h | h <;> rw [h] <;> decide

/-- CODE's byte-level inactive-zero constraint restores each original bit's
inactive-zero constraint. It does not require assuming the active flag Boolean. -/
theorem packed_lift_bit_inactive (regions : List (Nat × Nat)) (packed : Env Fp)
    (c j bit : Nat) (nx : Bool) (active : Fp)
    (slot : packedColumnSlot regions c=.byte j bit)
    (inactive : (1-active)*packed.col j nx=0) :
    (1-active)*(packedLiftEnv regions packed).col c nx=0 := by
  by_cases hz : packed.col j nx=0
  · simp only [packedLiftEnv,slot,hz]
    have zeroNat : (0:Fp).toNat=0 := rfl
    simp only [zeroNat,Nat.zero_div,Nat.zero_mod]
    change (1-active)*0=0
    grind
  · have gate : 1-active=0 := by grind
    rw [gate]
    grind

end NearCompression
