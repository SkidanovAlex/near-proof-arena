import NearCompression.SHA384CallLinear
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512

/-- The actual unbatched descriptor format: a constant or a copied input slot. -/
structure CallLinearEquation where
  left : Nat
  right : Option Nat
  value : Nat
  deriving Repr, BEq

def CallLinearEquation.eval (e : CallLinearEquation) (privateValues : Nat→Fp) : Fp :=
  privateValues e.left - match e.right with
    | none => Fp.ofNat e.value
    | some i => privateValues i

/-- Full row-low/column-high mathematical private input. -/
def callPrivateValues (rows : Nat) (trace : Nat→Nat→Fp) (slot : Nat) : Fp :=
  trace (slot%rows) (slot/rows)

theorem call_private_cell (rows r c : Nat) (trace : Nat→Nat→Fp) (hr : r<rows) :
    callPrivateValues rows trace (r+rows*c)=trace r c := by
  unfold callPrivateValues
  rw [Nat.add_mul_div_left r c (by omega),Nat.div_eq_of_lt hr,Nat.zero_add]
  simp [Nat.add_mod,Nat.mod_eq_of_lt hr]

def callConstantEquations (rows row base : Nat) (expected : List Nat) : List CallLinearEquation :=
  (List.range (4*expected.length)).map (fun j=>
    ⟨row+rows*(base+j),none,expected.getD (j/4) 0/65536^(j%4)%65536⟩)

def callStateEquations (rows previous next : Nat) : List CallLinearEquation :=
  (List.range 32).map (fun j=>⟨next+rows*(3+j),some (previous+rows*(99+j)),0⟩)

def callDigestEquations (rows row : Nat) (digest : List UInt8) : List CallLinearEquation :=
  (List.range digest.length).map (fun j=>⟨row+rows*(131+j),none,(digest.getD j 0).toNat⟩)

theorem call_constant_equations_eval (rows row base : Nat) (trace : Nat→Nat→Fp)
    (expected : List Nat) (hr : row<rows) :
    (callConstantEquations rows row base expected).map (fun e=>e.eval (callPrivateValues rows trace))=
      callConstantResiduals (trace row) base expected := by
  simp only [callConstantEquations,callConstantResiduals,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro j hj
  simp only [CallLinearEquation.eval,call_private_cell rows row _ trace hr,callWordLimb]

theorem call_state_equations_eval (rows previous next : Nat) (trace : Nat→Nat→Fp)
    (hp : previous<rows) (hn : next<rows) :
    (callStateEquations rows previous next).map (fun e=>e.eval (callPrivateValues rows trace))=
      callStateLinkResiduals trace previous next := by
  simp only [callStateEquations,callStateLinkResiduals,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro j hj
  simp only [CallLinearEquation.eval,call_private_cell rows next _ trace hn,
    call_private_cell rows previous _ trace hp]

/-- Digest descriptors constrain each byte, not a reduced64-bit field value. -/
theorem call_digest_equations_sound (rows row : Nat) (trace : Nat→Nat→Fp)
    (digest : List UInt8) (hr : row<rows)
    (zero : ∀ e,e∈callDigestEquations rows row digest → e.eval (callPrivateValues rows trace)=0) :
    ∀ j,j<digest.length → (trace row (131+j)).toNat=(digest.getD j 0).toNat := by
  intro j hj
  have eq:=zero _ (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩)
  simp only [CallLinearEquation.eval,call_private_cell rows row _ trace hr] at eq
  have same : trace row (131+j)=Fp.ofNat (digest.getD j 0).toNat := by grind
  rw [same,Fp.toNat_ofNat,Nat.mod_eq_of_lt (show (digest.getD j 0).toNat<P from by
    have bound:=(digest.getD j 0).toNat_lt;unfold P;omega)]

/-- Per-call descriptors in the executable compiler's exact order. IV and
state-link equations precede each block, then final digest-byte equations. -/
def callBlockEquations (rows : Nat) : Option Nat→List (Nat × List Nat)→List CallLinearEquation
  | _,[] => []
  | previous,item::rest =>
      (match previous with
        | none => callConstantEquations rows item.1 3 sha384ChainIV
        | some p => callStateEquations rows p item.1) ++
      callConstantEquations rows item.1 35 (words item.2) ++
      callBlockEquations rows (some item.1) rest

def callEquations (rows : Nat) (items : List (Nat × List Nat)) (digest : List UInt8) : List CallLinearEquation :=
  callBlockEquations rows none items ++
  match items.getLast? with
    | none => []
    | some item => callDigestEquations rows item.1 digest

end NearCompression
