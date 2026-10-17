import NearCompression.SHA512Public

/-! Verifier-side composition of actual public compression claims. The ordered
input concatenation, state links, padding equality, and digest serialization
are explicit checks. This introduces neither an AIR multiblock bus nor a
recursive proof or an AIR padding gadget. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.SHA512

structure SHA512ChainItem where
  pub : List Fp
  trace : Trace Fp

def sha512ChainInput (items : List SHA512ChainItem) : List Nat :=
  items.flatMap (fun item => sha512PublicBlock item.pub)

def sha512ChainWiring (initial : List Nat) : List SHA512ChainItem → List Nat → Bool
  | [], final => final==initial
  | item::rest, final => (sha512PublicState item.pub==initial) &&
      sha512ChainWiring (sha512PublicOutput item.pub) rest final

def sha512ChainClaims (items : List SHA512ChainItem) : Prop :=
  ∀ item ∈ items,sha512PublicClaim item.pub item.trace

def sha512ChainLinks (initial : List Nat) (items : List SHA512ChainItem) (final : List Nat) : Prop :=
  sha512ChainClaims items ∧ sha512ChainWiring initial items final=true

def sha512ChainClaim (initial input final : List Nat) (items : List SHA512ChainItem) : Prop :=
  input=sha512ChainInput items ∧ sha512ChainLinks initial items final

def sha512ChainBoundaryCheck (initial input final : List Nat) (items : List SHA512ChainItem) : Bool :=
  (input==sha512ChainInput items) && sha512ChainWiring initial items final

def sha512MessageBoundaryCheck (message digest : ArenaCore.Bytes) (final : List Nat)
    (items : List SHA512ChainItem) : Bool :=
  sha512ChainBoundaryCheck H0 (pad (message.map UInt8.toNat)) final items && (digest==digestBytes final)

def sha512MessageClaim (message digest : ArenaCore.Bytes) (items : List SHA512ChainItem) : Prop :=
  ∃ final,sha512ChainClaim H0 (pad (message.map UInt8.toNat)) final items ∧ digest=digestBytes final

theorem sha512_chain_check_iff (initial input final : List Nat) (items : List SHA512ChainItem) :
    sha512ChainClaim initial input final items ↔
      sha512ChainClaims items ∧ sha512ChainBoundaryCheck initial input final items=true := by
  simp only [sha512ChainClaim,sha512ChainLinks,sha512ChainBoundaryCheck,Bool.and_eq_true,beq_iff_eq]
  constructor
  · intro ⟨inputEq,claims,wiring⟩
    exact ⟨claims,inputEq,wiring⟩
  · intro ⟨claims,inputEq,wiring⟩
    exact ⟨inputEq,claims,wiring⟩

theorem sha512_chain_empty (initial input final : List Nat) :
    sha512ChainClaim initial input final [] ↔ input=[] ∧ final=initial := by
  simp [sha512ChainClaim,sha512ChainInput,sha512ChainLinks,sha512ChainClaims,sha512ChainWiring]

theorem sha512_chain_input_length (items : List SHA512ChainItem) :
    (sha512ChainInput items).length=128*items.length := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    change (sha512PublicBlock item.pub ++ sha512ChainInput rest).length=128*(rest.length+1)
    rw [List.length_append,(sha512_public_block_bytes item.pub).1,ih]
    omega

theorem sha512_chain_input_bytes (items : List SHA512ChainItem) (byte : Nat)
    (hb : byte ∈ sha512ChainInput items) : byte<256 := by
  obtain ⟨item,hi,hb⟩ := List.mem_flatMap.mp hb
  exact (sha512_public_block_bytes item.pub).2 byte hb

/-- One exact 128-byte block is consumed; neither truncation nor leftover bytes
are hidden in the composition step. -/
theorem sha512_blocks_cons_exact (n : Nat) (initial block rest : List Nat)
    (hlen : block.length=128) :
    blocks (n+1) initial (block++rest)=blocks n (compress initial block) rest := by
  have nonempty : block++rest≠[] := by
    intro empty
    have len := congrArg List.length empty
    simp only [List.length_append,List.length_nil,hlen] at len
    omega
  have step (msg : List Nat) (hn : msg≠[]) :
      blocks (n+1) initial msg=blocks n (compress initial (msg.take 128)) (msg.drop 128) := by
    cases msg with
    | nil => contradiction
    | cons x xs => rfl
  rw [step _ nonempty,←hlen,List.take_append_length,List.drop_append_length]

/-- Per-block compression equalities are derived from actual AIR claims, not
assumed as hypotheses of the chain. -/
theorem sha512_chain_links_blocks (initial final : List Nat) (items : List SHA512ChainItem)
    (links : sha512ChainLinks initial items final) :
    final=blocks items.length initial (sha512ChainInput items) := by
  induction items generalizing initial with
  | nil => simpa [sha512ChainLinks,sha512ChainWiring,blocks] using links.2
  | cons item rest ih =>
    have headClaim := links.1 item (List.mem_cons_self ..)
    have wiring : sha512PublicState item.pub=initial ∧
        sha512ChainWiring (sha512PublicOutput item.pub) rest final=true := by
      simpa only [sha512ChainWiring,Bool.and_eq_true,beq_iff_eq] using links.2
    have tailClaims : sha512ChainClaims rest := fun other hm => links.1 other (List.mem_cons_of_mem _ hm)
    have tailResult := ih (sha512PublicOutput item.pub) ⟨tailClaims,wiring.2⟩
    have headResult := sha512_public_compression item.pub item.trace headClaim
    rw [wiring.1] at headResult
    change final=blocks (rest.length+1) initial (sha512PublicBlock item.pub++sha512ChainInput rest)
    rw [sha512_blocks_cons_exact _ _ _ _ (sha512_public_block_bytes item.pub).1,←headResult]
    exact tailResult

/-- Exact count and ordered consumption using the specification's blocks function. -/
theorem sha512_chain_sound (initial input final : List Nat) (items : List SHA512ChainItem)
    (claim : sha512ChainClaim initial input final items) :
    final=blocks items.length initial input ∧ input.length=128*items.length := by
  rw [claim.1]
  exact ⟨sha512_chain_links_blocks initial final items claim.2,sha512_chain_input_length items⟩

theorem sha512_chain_consumed (initial input final : List Nat) (items : List SHA512ChainItem)
    (claim : sha512ChainClaim initial input final items) :
    input.length/128=items.length ∧ input.drop (128*items.length)=[] := by
  have len := (sha512_chain_sound initial input final items claim).2
  constructor
  · rw [len]
    omega
  · rw [←len]
    exact List.drop_length

/-- Includes the exact specification padding and digest bytes as verifier-side
bindings. This is a full-message semantic theorem, not a new recursive AIR. -/
theorem sha512_message_sound (message digest : ArenaCore.Bytes) (items : List SHA512ChainItem)
    (claim : sha512MessageClaim message digest items) : digest=NearSpecV3.sha512 message := by
  obtain ⟨final,chain,digestEq⟩ := claim
  have result := (sha512_chain_sound _ _ _ _ chain).1
  have count := (sha512_chain_consumed _ _ _ _ chain).1
  rw [digestEq,result]
  change digestBytes (blocks items.length H0 (pad (message.map UInt8.toNat))) =
    digestBytes (blocks ((pad (message.map UInt8.toNat)).length/128) H0 (pad (message.map UInt8.toNat)))
  rw [count]

theorem sha512_message_check_sound (message digest : ArenaCore.Bytes) (final : List Nat)
    (items : List SHA512ChainItem) (claims : sha512ChainClaims items)
    (check : sha512MessageBoundaryCheck message digest final items=true) :
    digest=NearSpecV3.sha512 message := by
  have checks : sha512ChainBoundaryCheck H0 (pad (message.map UInt8.toNat)) final items=true ∧
      digest=digestBytes final := by
    simpa only [sha512MessageBoundaryCheck,Bool.and_eq_true,beq_iff_eq] using check
  apply sha512_message_sound message digest items
  exact ⟨final,(sha512_chain_check_iff _ _ _ _).mpr ⟨claims,checks.1⟩,checks.2⟩

theorem sha512_message_block_count (message digest : ArenaCore.Bytes) (items : List SHA512ChainItem)
    (claim : sha512MessageClaim message digest items) :
    items.length=(pad (message.map UInt8.toNat)).length/128 ∧ 0<items.length := by
  obtain ⟨final,chain,_⟩ := claim
  have count := (sha512_chain_consumed _ _ _ _ chain).1
  have len := (sha512_chain_sound _ _ _ _ chain).2
  have positive : 0<(pad (message.map UInt8.toNat)).length := by
    simp only [pad,List.length_append,List.length_singleton]
    omega
  exact ⟨count.symm,by omega⟩

end NearCompression
