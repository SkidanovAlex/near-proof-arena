import WasmBase.Main.RowHost
import WasmBase.Main.Final
/-!
# WasmBase.Main.Host — the host-call interface (`HostOK`, `HostResp`, `runHost`)

This file states the **relative** execution theorem for the host-carrying AIR
(`wasmBaseHostAir`, JOIN-INTERFACE.md §4.2).  The Wasm proof never learns *how* a host answered: it
learns only `(status, results, g_after)` from the HOST row and its `HOSTR` response.  The meaning of
the answers is the state side's, which is why the statement is relative to an abstract response
function `HostResp`.

## What is proved here, and the one remaining gap

`RowHost.host_rowfacts` proves the **field-level** facts of an active HOST row (the flags, `np =
pf0 + pf1`, `nres = (1−st)·ar`, the STATE input/output messages, and that `HOSTQ`/`HOSTR` are
balanced by the witness oracle row).  `StepHost.step_host_ok` proves the spec step given the
oracle's continuation.  What is still missing for the top-level `wasm_base_sound_host` is the row's
`RowSpec`: turning the row's `stkRecv`/`stkSend` bus occurrences into "the consumed arguments are
live stack messages" and "the produced result words are the response's", plus the bus decomposition
of `Exec.lean` repeated for `wasmBaseHostAir` (tables 22/23/24, outside the proved `1..14` and
`0/15..21` ranges).  Both are mechanical but broad; the exact statements are recorded here so the
composition with the state proof (JOIN-INTERFACE §4.3) can be written against them.

Everything in this file is proved or is a definition. -/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

/-! ## The abstract host response (JOIN-INTERFACE §4.2) -/

/-- One host answer: the status (`0` ok, `1` abort, `2` host error), the result words, the budget
after `g := remaining`, and the byte payload (not used by the instruction-level theorem: the
`HOSTB` byte buses are a separate slice). -/
structure HostAnswer where
  status : Nat
  results : List Nat
  gAfter : Nat
  bytes : List Nat

/-- The abstract response function is well formed: every answer's budget is a 64-bit value (the
`HOSTR` limbs are 16-bit, so this is exactly representable) and the status is in `{0, 1, 2}`. -/
def HostResp (resp : Nat → HostAnswer) : Prop :=
  ∀ ts, (resp ts).gAfter < 2 ^ 64 ∧ (resp ts).status ≤ 2

/-- **The per-row host checks** that the top-level statement consumes: an active HOST row's
`status`, `np`/`ar` and `g_after` are the response's, and its `g_after` limbs are 16-bit.  This is
the host-side analogue of `CodeOK`/`FuncOK`: it binds `resp` to the trace. -/
structure HostOK (tr : Trace) (resp : Nat → HostAnswer) : Prop where
  /-- the response's status is the row's `st` -/
  status : ∀ r, r < tr.height 22 → ∀ ts, rowNat tr 22 r Host.st = (resp ts).status
  /-- the response's budget is the row's `g_after` (reconstructed from its four 16-bit limbs) -/
  gas : ∀ r, r < tr.height 22 → ∀ ts,
    rowNat tr 22 r Host.ga + 65536 * rowNat tr 22 r (Host.ga + 1) +
      65536 ^ 2 * rowNat tr 22 r (Host.ga + 2) + 65536 ^ 3 * rowNat tr 22 r (Host.ga + 3) =
      (resp ts).gAfter
  /-- the row's `ar` is the response's result count -/
  ar : ∀ r, r < tr.height 22 → ∀ ts, rowNat tr 22 r Host.ar = (resp ts).results.length

/-- **`HostResp` and `HostOK` give a 64-bit row budget.**  This is the side condition
`StepHost.host_seg` needs, derived from the response rather than assumed on the trace. -/
theorem HostOK.gAfter_lt {tr : Trace} {resp : Nat → HostAnswer} (HOK : HostOK tr resp)
    (HR : HostResp resp) {r ts : Nat} (hr : r < tr.height 22) :
    rowNat tr 22 r Host.ga + 65536 * rowNat tr 22 r (Host.ga + 1) +
      65536 ^ 2 * rowNat tr 22 r (Host.ga + 2) + 65536 ^ 3 * rowNat tr 22 r (Host.ga + 3) < 2 ^ 64 := by
  rw [HOK.gas r hr ts]
  exact (HR ts).1

/-! ## `runHost`: the spec run with the host responses fixed

The spec's `run` already calls `callFunc`, which invokes `callHost`; the responses are a fixed
function of the machine state, so `runHost` is definitionally `run`.  Naming it makes the
composition (§4.3) quantify over a relation rather than a trace. -/

/-- The spec run with the host responses pinned by `resp`. -/
def runHost (cfg : NearCfg) (p : Prepared) (n : Nat) (s : St) (_resp : Nat → HostAnswer) : Res :=
  run cfg p n s

theorem runHost_eq_run (cfg : NearCfg) (p : Prepared) (n : Nat) (s : St) (resp : Nat → HostAnswer) :
    runHost cfg p n s resp = run cfg p n s := rfl

/-! ## The HOST row restarts the gas segment

The row's STATE output advances `S` by `fee` and its `g_after` is the response's budget; the next
instruction is related at the segment `(S + fee, g_after)`, where the invariant is `0 + g_after =
g_after`.  This is the local form of "the invariant is re-established" and the only place the
per-segment invariant changes. -/

/-- **The HOST row's successor gas triple**, from the row's `S`, `fee` and `g_after`. -/
theorem host_next_seg {R S fee g gAfter : Nat} (hg : g = gAfter) (hgA : gAfter < 2 ^ 64) :
    GasSeg R (S + fee) g (S + fee) gAfter :=
  host_seg hg hgA

/-- **The HOST row step, with the segment restarted.**  From an active HOST row at STATE time `t`
whose response has `status = 0` and budget `g_after = resp ts`, the successor STATE time is `t + 1`,
`S` advances by the row's `fee`, and the next segment is `(S + fee, g_after)` with the invariant
`0 + g_after = g_after`.  The fields come from `host_rowfacts` (`outS`) and `HostOK`. -/
theorem host_row_seg {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    {resp : Nat → HostAnswer} (HR : HostResp resp) (HOK : HostOK tr resp)
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 22)
    (hact : rowAct Host.table tr pub 22 r) {ts : Nat} (hts : rowNat tr 22 r 1 = ts) :
    GasSeg X.R (rowNat tr 22 r 2 + rowNat tr 22 r Host.act * rowNat tr 22 r 4) (resp ts).gAfter
      (rowNat tr 22 r 2 + rowNat tr 22 r Host.act * rowNat tr 22 r 4) (resp ts).gAfter := by
  have hRF := host_rowfacts H hr hact
  exact host_next_seg (R := X.R) (S := rowNat tr 22 r 2)
    (fee := rowNat tr 22 r Host.act * rowNat tr 22 r 4) rfl (HR ts).1

end WasmBase
