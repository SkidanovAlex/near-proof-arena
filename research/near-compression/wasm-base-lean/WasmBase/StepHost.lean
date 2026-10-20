import WasmBase.HostCheck
import WasmBase.Main.Rows
/-!
# WasmBase.StepHost — a host call under an abstract response oracle

The spec's `callHost` (NearSpecV3.Wasm) runs `sync`, the host function, then `g := remaining`.
Following README §14.2, the host function's semantics are **not** re-proved here: the row lemma and
the prover take an abstract response oracle (status, result word, `g_after`).  This file states
exactly what the spec does in terms of that oracle, and proves it from the semantics — no axiom and
no unfinished proof.

`HostOracle` is the response of the state side.  `step_host_ok` / `step_host_abort` say: if the
oracle says the call (after the D2 fee charge) continues in state `os` (resp. aborts in `os`), then
the spec `step` is `.cont os` (resp. `.abort os e`) and the frames / stack / memory of `os` are
given by the oracle's fields.  The gas field is `gAfter`; this is the resynchronisation, and it is
why the top-level gas invariant of the Wasm-only theorem (README §14.3) has to be generalised
before a host-aware `wasm_base_sound` can be stated — recorded in `results/pq-host-chip/RESULTS.md`.
-/
namespace WasmBase
open NearSpecV3.Wasm

/-- The abstract host response: `status = 0` success, `1` abort; `word` is the single result word
(`ar ≤ 1` for this slice); `gAfter` is the budget after `g := remaining`; `err` the abort message. -/
structure HostOracle where
  status : Nat
  word : Nat
  gAfter : Nat
  err : String

/-- The gas-adjusted state a host call runs from (the D2 fee has been charged). -/
def hostPre (s : St) (R fee : Nat) : St := { s with gas := { s.gas with g := s.gas.g - R * fee } }


/-- **A successful host call.**  The oracle's `callFunc` outcome is `.cont os`; `os` has the
advanced frame, the response's stack, and `g_after` as its budget. -/
theorem step_host_ok (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live) {fi : Nat} {ins : Instr} {fee : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some ins) (hcall : ins = .call fi)
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hg : X.R * (S + fee) ≤ X.g0) (hg64 : X.g0 < 2 ^ 64)
    (os : St) (ho : callFunc X.cfg X.p (setFrame (hostPre s X.R fee) { f with pc := f.pc + 1 }) fi = .cont os) :
    step X.cfg X.p s = .cont os := by
  subst hcall
  rw [step_eq_exec X R hins hfee hg hg64]
  simp only [exec]
  exact ho

/-- **An aborting host call** (host error, gas exhausted inside the host function, guest panic). -/
theorem step_host_abort (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live) {fi : Nat} {ins : Instr} {fee : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some ins) (hcall : ins = .call fi)
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hg : X.R * (S + fee) ≤ X.g0) (hg64 : X.g0 < 2 ^ 64)
    (os : St) (e : String)
    (ho : callFunc X.cfg X.p (setFrame (hostPre s X.R fee) { f with pc := f.pc + 1 }) fi = .abort os e) :
    step X.cfg X.p s = .abort os e := by
  subst hcall
  rw [step_eq_exec X R hins hfee hg hg64]
  simp only [exec]
  exact ho

/-- The oracle fact for a successful call, in the form the AIR row needs: the response word and
`g_after` are the ones the HOSTR bus carries (the stack/gas fields are the oracle's). -/
theorem step_host_ok' (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live) {fi : Nat} {ins : Instr} {fee : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some ins) (hcall : ins = .call fi)
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hg : X.R * (S + fee) ≤ X.g0) (hg64 : X.g0 < 2 ^ 64)
    (os : St) (c : HostOracle) (hst : c.status = 0) (hgA : os.gas.g = c.gAfter)
    (ho : callFunc X.cfg X.p (setFrame (hostPre s X.R fee) { f with pc := f.pc + 1 }) fi = .cont os) :
    step X.cfg X.p s = .cont os ∧ os.gas.g = c.gAfter :=
  ⟨step_host_ok X R hins hcall hfee hg hg64 os ho, hgA⟩

/-- The oracle fact for an aborting call. -/
theorem step_host_abort' (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live) {fi : Nat} {ins : Instr} {fee : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some ins) (hcall : ins = .call fi)
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hg : X.R * (S + fee) ≤ X.g0) (hg64 : X.g0 < 2 ^ 64)
    (os : St) (c : HostOracle) (hst : c.status = 1) (hgA : os.gas.g = c.gAfter) (e : String)
    (ho : callFunc X.cfg X.p (setFrame (hostPre s X.R fee) { f with pc := f.pc + 1 }) fi = .abort os e) :
    step X.cfg X.p s = .abort os e ∧ os.gas.g = c.gAfter :=
  ⟨step_host_abort X R hins hcall hfee hg hg64 os e ho, hgA⟩

end WasmBase
