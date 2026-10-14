import ZkFormal.Air.Basic
import ZkFormal.Stark.Bcs
import ZkFormal.Stark.ProtocolDefs

/-!
# ZkFormal.Stark.Protocol — `np-udr-stark-v1` as an `IopSpec` (lane L4)

`Iop.verifier A prm : IopSpec F K` is the IOP verifier of DESIGN.md §4 for the
AIR `A`; `verifier A prm : TreeVerifier` is its BCS compilation, the deployed
verifier model, and `verifier_eq_compile` holds by definition.  The exact
round structure, orderings and byte layout are specified in
`docs/zk-formal/FORMATS.md` §2–§4; this file is the normative definition.

Round structure for a header `logs` (table heights `2^logs[t]`, LDE logs
`m_t = logs[t] + logBlowup`, query domain `n0 = max m_t`):

| # | prover message                                  | challenge |
|---|-------------------------------------------------|-----------|
| 0 | header, main oracle (table `t`: `(m_t, width_t)`)| `α_fp`    |
| 1 | –                                               | `γ`       |
| 2 | aux oracle (`(m_t, 8·aux_t)`), finals (K)       | `α_c`     |
| 3 | quotient oracle (`(m_t, 8·quot_t)`)             | `z` (OOD) |
| 4 | OOD values (K)                                  | `r_1`     |
| 4+k | – (`k = 1 … L-1`)                             | `r_{k+1}` |
| FRI | per layer `i < ℓ`: [roll-in: – / `γ_i`], then `root_i` or – / `β_i` | |
| end | [roll-in at `ℓ`: – / `γ_ℓ`], final polynomial (2 K) | query phase |
-/

namespace ZkFormal.Stark

open ArenaCore Lean.Grind ZkFormal.Air

/-! ## Static layout (from the AIR, the parameters and the header) -/

/-! ## Header admissibility and the schedule -/

end ZkFormal.Stark
