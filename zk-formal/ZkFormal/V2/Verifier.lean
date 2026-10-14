import ZkFormal.Stark.Verifier
import ZkFormal.Stark.Instance
import ZkFormal.V2.Air
import ZkFormal.V2.VerifierDefs

/-!
# ZkFormal.V2.Verifier — the verifier of `np-udr-stark-v2` (lane L4)

`Iop.verifierP F K AP prm` is v1's `Iop.verifier F K AP.toAir prm` with **one**
change.  Header admissibility, schedule, query rule and the per-position checks
(`checkAt`) are v1's, field by field.  Only the clear-text check `global` differs:

* v1: per-table ALI identities, and `∏ send finals = ∏ receive finals`;
* v2: the same ALI identities, every public segment fits (`pubFit`), and
  `∏ send finals · Π_pub(send) = ∏ receive finals · Π_pub(recv)`, where
  `Π_pub(s) = ∏_{public messages (b, s, m)} (γ − fp_α(m ‖ b+1))` with v1's fingerprint
  convention `fp_α(x) = Σ_k x_k α^k`.

`prepP` duplicates v1's `prep` and computes the new `globalOk`.  It is a copy rather than
`{ prep … with globalOk := … }` so that the deployed verifier evaluates the ALI checks
once.  `prepP_eq` shows that it agrees with `prep` on every other field.  So
`ChecksPass` of v2 is that of v1 (`checksPass_eq`), and v1's query-phase
analysis applies unchanged.

With no public segments, `globalChecksP = globalChecks` (`globalChecksP_nil`): the
v2 verifier of `AirP.ofAir A` accepts exactly what v1's verifier of `A` accepts,
except that its `global` also checks the (trivially true) `pubFit`.

Proof bytes are those of v1: the prover's messages do not change.
The public products are recomputed by the verifier from the claim.
-/

namespace ZkFormal.V2

open ArenaCore Lean.Grind ZkFormal.Air ZkFormal.Stark

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F] [DecidableEq K] [PubVal F]

attribute [local instance] Semiring.natCast

/-- `prepP` is v1's `prep` with `globalOk := globalOkP`. -/
theorem prepP_eq (AP : AirP) (prm : Params) (τ : PT K Unit) :
    prepP (F := F) AP prm τ = { prep (F := F) AP.toAir prm τ with globalOk := globalOkP (F := F) AP prm τ } := by
  unfold prepP prep globalOkP
  generalize τ.header? = oh
  generalize τ.chals = cs
  generalize τ.elems = es
  rcases oh with _ | hdr
  · rfl
  · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
    rcases es with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, _ | ⟨e4, es'⟩⟩⟩⟩ <;>
    first
    | rfl
    | (dsimp only
       generalize splitOod (layout AP.toAir prm hdr) e2 = so
       rcases so with ⟨oods, r⟩
       rfl)

end

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F] [DecidableEq K] [PubVal F]
variable (AP : AirP) (prm : Params)

theorem verifierP_eq_compile (pub cb pb : Bytes) :
    (verifierP F K AP prm).tree pub cb pb = Bcs.compile (F := F) (Iop.verifierP F K AP prm) pub cb pb :=
  rfl

/-- The local (per-position) checks of v2 are v1's. -/
theorem checksPass_eq {O : Type} (τ : PT K O) (x : Nat) (op : List (List (List F))) :
    (Iop.verifierP F K AP prm).ChecksPass τ x op ↔ (Iop.verifier F K AP.toAir prm).ChecksPass τ x op := by
  unfold IopSpec.ChecksPass
  show checkAt (F := F) (prepP (F := F) AP prm τ.erase) x op = true ↔
    checkAt (F := F) (prep (F := F) AP.toAir prm τ.erase) x op = true
  rw [prepP_eq]
  rfl

/-- Same header admissibility, schedule, query rule, position encoding and size cap as v1. -/
theorem headerOk_eqP : (Iop.verifierP F K AP prm).headerOk = (Iop.verifier F K AP.toAir prm).headerOk := rfl
theorem schedule_eqP : (Iop.verifierP F K AP prm).schedule = (Iop.verifier F K AP.toAir prm).schedule := rfl
theorem queryLog_eqP : (Iop.verifierP F K AP prm).queryLog = (Iop.verifier F K AP.toAir prm).queryLog := rfl

end

/-! ## No public segments: v2's bus check is v1's -/

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F] [DecidableEq K] [PubVal F]

theorem pubProd_nil {AP : AirP} (h : AP.pubSegs = []) (pub : List F) (α γ : K) (s : Bool) :
    pubProd AP pub α γ s = 1 := by
  simp [pubProd, pubMsgs_nil h]

theorem globalChecksP_nil {AP : AirP} (h : AP.pubSegs = []) (prm : Params) (pub : List F)
    (lay : List TLayout) (ood : List (TOod K)) (finals : List K) (αfp γ αc z : K) :
    globalChecksP AP prm pub lay ood finals αfp γ αc z =
      globalChecks AP.toAir prm pub lay ood finals αfp γ αc z := by
  unfold globalChecksP globalChecks
  simp only [pubProd_nil h, Semiring.mul_one]

end

end ZkFormal.V2
