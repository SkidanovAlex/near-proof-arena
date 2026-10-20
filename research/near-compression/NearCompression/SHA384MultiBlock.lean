import NearCompression.SHA384Chain
import ZkFormal.V2.Export

/-! Fixed message-length SHA384 AIR. Public inputs are message bytes followed
by 48 digest bytes. Intermediate states are private and linked by bus zero.
The compression projection below is deterministic; fingerprint collision
bounds and the bus-to-chain semantic theorem are separate obligations. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.SHA512
set_option maxRecDepth 65536

def sha384PaddedLength (n : Nat) : Nat := ((n+16)/128+1)*128

def sha384PaddedByte (n i : Nat) : Expr :=
  if i<n then .pub i
  else if i=n then .const 128
  else if sha384PaddedLength n-16≤i then
    .const ((8*n)/256^(sha384PaddedLength n-1-i)%256)
  else .const 0

def sha384BlockByteConstraint (n block j : Nat) : Expr :=
  .mul .isFirst (.add
    (instructionBitExpr (sha512ScheduleWindowBase (j/8)+8*(7-j%8)) 8)
    (.neg (sha384PaddedByte n (block*128+j))))

def sha384IVConstraint (i limb : Nat) : Expr :=
  .mul .isFirst (.add
    (instructionBitExpr (sha512FeedForwardInputBase i+16*limb) 16)
    (.neg (.const ((sha384ChainIV.getD i 0)/65536^limb%65536))))

def sha384DigestConstraint (n j : Nat) : Expr :=
  .mul (.col 5231 false) (.add
    (instructionBitExpr (sha512FeedForwardBase (j/8)+144+8*(7-j%8)) 8)
    (.neg (.pub (n+j))))

def sha384StateMessage (tag offset : Nat) : List Expr :=
  .const tag :: (List.range 8).flatMap (fun i => (List.range 4).map
    (fun limb => .col (sha512FeedForwardBase i+offset+limb) false))

def sha384BlockInteractions (n block : Nat) : List Interaction :=
  (if 0<block then [⟨0,[.isFirst],sha384StateMessage (block-1) 0,false⟩] else []) ++
  (if block+1<sha384PaddedLength n/128 then
    [⟨0,[.col 5231 false],sha384StateMessage block 8,true⟩] else [])

def sha384BlockBoundaryConstraints (n block : Nat) : List Expr :=
  (List.range 128).map (sha384BlockByteConstraint n block) ++
  (if block=0 then (List.range 8).flatMap (fun i =>
    (List.range 4).map (sha384IVConstraint i)) else []) ++
  (if block+1=sha384PaddedLength n/128 then
    (List.range 48).map (sha384DigestConstraint n) else [])

def sha384MultiBlockTable (n block : Nat) : Table :=
  ⟨6944,sha512FeedForwardConstraints ++ sha384BlockBoundaryConstraints n block,
    sha384BlockInteractions n block,7⟩

def sha384MultiBlockAir (n : Nat) : ZkFormal.V2.AirP := {
  tables := (List.range (sha384PaddedLength n/128)).map (sha384MultiBlockTable n)
  numBuses := 1
  numPub := n+48
  maxPub := n+48
  pubSegs := [] }

/-- Every claimed multiblock table contains the existing full compression AIR;
no assumed compression equality or new validity premise is introduced. -/
theorem sha384_multiblock_ff_holds (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (n block : Nat)
    (table : air.tables[t]=sha384MultiBlockTable n block) (holds : Holds air pub tr) :
    Holds ⟨[sha512FeedForwardTable],0,0⟩ pub (sha512CombinedProjection tr t 0) := by
  constructor
  · intro j hj
    have hz : j=0 := by simpa using hj
    subst j
    have h := holds.logBound t ht
    rw [table] at h
    exact h
  · intro j hj r hr e he
    have hz : j=0 := by simpa using hj
    subst j
    rw [←sha512_combined_relocate_eval,sha512_relocate_zero]
    have hc := holds.constr t ht r hr e
    rw [table] at hc
    exact hc (List.mem_append_left _ he)
  · intro j hj r hr i hi
    have hz : j=0 := by simpa using hj
    subst j
    simp [sha512FeedForwardTable] at hi
  · intro b m
    simp [busCount,busCount.go,tableBusCount,sha512FeedForwardTable]

end NearCompression
