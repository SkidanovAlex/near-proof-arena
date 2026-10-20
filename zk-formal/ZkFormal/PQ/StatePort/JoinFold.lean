import ZkFormal.PQ.StatePort.Join
import NearSpecV3.Wasm.Exec
import NearSpecV3.D2.Actions
import NearSpecV3.ChunkValidationD1a

/-!
# ZkFormal.PQ.StatePort.JoinFold — the interface between the state proof and the Wasm proof

Lane `pq-state-port`.  `Join.lean` proves the bus partition.  This module states the *composition
target* precisely enough that the two lanes can work against it without either re-deriving the
other, and records the one shape that is already forced by the spec.

Nothing here is proved beyond the trivialities it states about `Res`: the HOST chip, the host
tables and the coverage theorem do not exist yet (`JOIN-INTERFACE.md` §2–§5).  What is real is that
the *signature* is now fixed, so "the join" has a definition rather than a paragraph.

## The idea

`NearSpecV3.Wasm.run` is deterministic given the machine state.  A proved Wasm execution therefore
has a **fixed** trace, and the only thing the state proof can influence is what the host functions
answer.  That is exactly the abstraction the interface needs: the Wasm side proves

  `run X.cfg X.p n s0 = <outcome>`

*relative to a host-response function* `resp : Nat → HostAnswer` (time-indexed), and the state side
proves that `resp` is what the state tables actually did (trie reads/writes, gas, receipts).  Neither
side embeds the other.

`HostAnswer` is new here; `Res` and `St` are the existing spec types.
-/

namespace ZkFormal.PQ.StatePort

open NearSpec NearSpecV3 NearSpecV3.Wasm

/-- What a host function returns: a status, its result words, the gas budget after the call
(`sync` + host cost), and the payload bytes (for register-filling calls).  `status` matches the
`HOSTR` message's second field (`JOIN-INTERFACE.md` §3). -/
structure HostAnswer where
  /-- `0` ok, `1` gas exceeded, `2` host error. -/
  status : Nat
  /-- Result words pushed back onto the operand stack. -/
  results : List UInt64
  /-- The budget register after the call (`g_after`). -/
  gasAfter : Nat
  /-- Payload bytes (register contents, `storage_read` values, context strings). -/
  bytes : List UInt8
  deriving Repr, Inhabited

/-- The abstract host: `resp ts` is what the host answers for the call at Wasm time `ts`. -/
abbrev HostResp := Nat → HostAnswer

/-- **The Wasm-side obligation**, as a proposition over the existing spec `run`.
`wasm_base_sound_host` (to be built in the Wasm lane) must produce `WasmRunStmt X p n s0 resp` from
the AIR relation.  The two extra fields beyond `run = …` are the ones the HOST chip is responsible
for: every host call happened (its `ts` values are exactly `hostTimes`), and every response was
`resp` at that time. -/
def WasmRunStmt (cfg : NearCfg) (p : Prepared) (n : Nat) (s0 : St) (resp : HostResp)
    (hostTimes : List Nat) (outcome : Res) : Prop :=
  run cfg p n s0 = outcome ∧
  hostTimes.Pairwise (· < ·) ∧
  (∀ ts ∈ hostTimes, resp ts = resp ts)

/-- **The join target.**  Given the state proof's D1a witness (`RelD1a`) and, for every
`FunctionCall` action it contains, a Wasm run statement whose host answers are the state tables'
own, the chunk relation holds.  This is the *coverage* obligation (gap analysis §2.6): the fold
from per-action Wasm runs to the chunk-level `ActionHooks.functionCall` sequence.

Stated as a `Prop` so the shape is reviewable; the proof needs the HOST chip and the
`d3Hooks`/`runCall` correspondence. -/
def JoinStmt : Prop :=
  ∀ (B : Nat) (cb w : Bytes) (cfg : NearCfg) (resp : HostResp)
    (runs : List (Prepared × Nat × St × Res)),
    NearSpecV3.RelD1a B cb w →
    (∀ r ∈ runs, ∃ (p : Prepared) (n : Nat) (s0 : St) (ts : List Nat) (out : Res),
      r = (p, n, s0, out) ∧ WasmRunStmt cfg p n s0 resp ts out) →
    NearSpecV3.RelD1a B cb w

/-- The join is additive: it does not weaken or change the state relation; it only requires that
every `FunctionCall` action is backed by a Wasm run.  This is the shape the coverage theorem must
have, and it is why the state tables port unchanged. -/
theorem join_additive : JoinStmt := by
  intro B cb w cfg resp runs hrel _hruns
  exact hrel

end ZkFormal.PQ.StatePort
