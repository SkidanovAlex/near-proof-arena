import ZkFormal.Stark.Iop
import ZkFormal.Game
import ZkFormal.Stark.BcsDefs

/-!
# ZkFormal.Stark.Bcs — the BCS compiler: IOP verifier ↦ hash-query tree

`Bcs.compile V pub cb pb : OracleComp hashSpec Bool` is the deployed
non-interactive verifier of an `IopSpec` (DESIGN.md §4, byte format in
`docs/zk-formal/FORMATS.md` §2–§3):

1. reject proofs longer than `V.maxProofBytes`;
2. **parse** the commit-phase prefix of the proof (pure, total): header,
   then for every message slot of `V.schedule header` its parts (64-byte
   Merkle roots for oracles, canonical extension elements in the clear);
3. run the **transcript** (hash queries): `d₀ = WH(INIT, id ‖ |pub| ‖ pub ‖
   |cb| ‖ cb)`; a message with roots `ρ` and clear bytes `μ` is absorbed as
   `d ← WH(ABS, d ‖ u8 |ρ| ‖ ρ ‖ μ)`; a challenge steps the state
   `d ← WH(CHAL, d)` and is `decode(first 32 bytes of d)` (so every later
   state depends on it — lane L2's requirement); finally `numChunks` query answers
   `H(QUERY ‖ d ‖ le32 j)` give the positions;
4. parse and verify the **Merkle multiproofs** of every oracle at the
   positions (hash queries), collecting the opened rows;
5. require that no byte is left over, and decide with `V.global` and
   `V.check`, i.e. the IOP's own decision functions on the erased
   transcript.

Every function is total by structural recursion; malformed input yields
`false`.  Wide hash `WH(tag, m) = H(tag ‖ 1 ‖ m) ‖ H(tag ‖ 2 ‖ m)`
(64 bytes, two oracle queries).
-/

namespace ZkFormal.Stark

open ArenaCore ArenaCore.Security Lean.Grind

/-! ## Tags and wide hashing -/

theorem fit32_length (y : Bytes) : (fit32 y).length = 32 := by
  simp [fit32]

theorem fit32_of_length {y : Bytes} (h : y.length = 32) : fit32 y = y := by
  simp [fit32, h]

/-! ## Byte reading (pure, total) -/

/-! ### Compiled fast path (`@[csimp]`; see the note at `readInjF`) -/

section Fields
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]

end Fields

/-! ## The commit-phase prefix -/

section Prefix
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]

end Prefix

/-! ## Transcript -/

section Transcript
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]

end Transcript

/-! ## Merkle multiproofs (mixed heights) -/

section Merkle
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]

/-! ### Compiled fast paths (`@[csimp]`)

The definitions above are written for proofs; compiled, `take?` and the raw
slices `r.take (r.length - r'.length)` are linear in the *remaining proof*
at every read, i.e. quadratic overall.  The fast versions below are proved
equal in the kernel and installed with `@[csimp]` here, before any caller is
compiled, so compiled code (and only compiled code) uses them. -/

/-! ## Exact consumption of the readers -/

/-! ## Merkle readers -/

end Merkle

end ZkFormal.Stark

namespace ZkFormal.Stark

open ArenaCore ArenaCore.Security Lean.Grind

section Compile
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]

end Compile

end ZkFormal.Stark
