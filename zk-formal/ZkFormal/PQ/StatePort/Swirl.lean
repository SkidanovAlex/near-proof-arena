import ZkFormal.V2.VerifierDefs

/-!
# ZkFormal.PQ.StatePort.Swirl — the classical v2 AIR read as SWIRL AIRs (lane pq-state-port)

The post-quantum port keeps the classical AIR `AP : AirP` (for NEAR: `nearAirV3`) **unchanged**
and translates it, table by table, into the AIRs of the SWIRL backend (a LogUp bus argument whose
balance holds **mod p**, not over ℕ).  This module states, over BabyBear `Fp`, what that
translation means; `PQ.StatePort.Bridge` proves that it implies the classical `HoldsP`.

## The translation (mirrors `research/near-compression/native/pq-state-port`)

* Table `t` of `AP` becomes one SWIRL AIR with the same columns, constraints
  `(AP.tables[t]).allConstraints` (user constraints plus multiplicity-bit booleanity), the same
  cyclic next row and the same selectors.  Its public values are a vector `pv t`; the statement
  verifier `V_d` checks that `pv t` agrees with the classical public vector `pub` on every index
  the table reads (`VdChecks.pvAgree`; a prefix of `pub` long enough suffices, `pvAgree_of_prefix`
  in `Bridge`).
* Interaction `i` becomes one LogUp interaction on SWIRL bus `off + i.bus` (`off` is a constant
  bus-id offset, `64` in Rust, reserved for joins with other tables), message `i.msg`, and **field**
  count `countF i = Σₖ 2^k · eval(bₖ)` (bits `i.mult`, least significant first), signed `+` for a
  send and `−` for a receive (`signed`).
* The classical public segments (`pubMsgs AP pub`) become one extra committed table **TAPE**
  without constraints (`Tape`): columns `msg[0..W)`, `cnt`, `sel[0..K)`; key `k = (bus_k, len_k)`
  of `Tape.keys`; on every row, interaction `k` sends `msg[..len_k]` on bus `bus_k` with field
  count `cnt * sel_k` (`TapeRow.sum`, `tapeSum`).

## What is enforced

* `SwirlRel` is what the SWIRL PIOP enforces (assumption **P5**, "SWIRL soundness", shared by every
  PQ AIR and not formalised here): every constraint vanishes on every row of every AIR, heights are
  `2^log` with `2 ≤ log ≤ 24`, and for **every** SWIRL bus `b` (including buses `b < off`, where only
  TAPE could contribute) and every message `m`, the field sum of the signed counts over all AIRs
  (`tablesSum` over the classical tables plus `tapeSum`) is `0`.
* `VdChecks` is what the light statement verifier `V_d` checks explicitly (height caps
  `log_t ≤ maxLog_t`, `pubFit`, the public-value vectors) together with `TapeNet`, the net public
  multiplicities carried by TAPE.  `V_d` recomputes TAPE's commitment from the claim; under
  commitment binding (an assumption) TAPE equals the canonical `PQ.StatePort.Tape.tapeCanon`, which
  satisfies `TapeNet` (`tapeNet_canon`).

`TapeNet` only constrains the buses `off + b`.  Soundness needs nothing else: a TAPE contribution on
another SWIRL bus is never read by `HoldsP` (completeness needs TAPE to vanish there, which the
canonical TAPE does, `tapeSum_canon_of_not_off`).
-/

namespace ZkFormal.PQ.StatePort

open ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra

/-! ## Field sums -/

/-- Sum of a list of field elements. -/
def fsum (l : List Fp) : Fp := l.foldr (· + ·) 0

/-- Table `t` of `AP` (the empty table out of range; same default as `Udr.Np.tableOf`). -/
def tableAt (AP : AirP) (t : Nat) : Table := AP.tables.getD t ⟨0, [], [], 0⟩

/-! ## Translated interactions -/

/-- The recursion behind `countF`, at top level so the bridge can induct on it. -/
def countFGo (tr : Trace Fp) (t r : Nat) (pv : List Fp) : List Expr → Nat → Fp
  | [], _ => 0
  | b :: bs, k => ((2 ^ k : Nat) : Fp) * b.eval tr t r pv + countFGo tr t r pv bs (k + 1)

/-- **Field count** of interaction `i` on row `r` of table `t` (public values `pv`):
`Σₖ 2^k · eval(bₖ)` over the multiplicity bits `i.mult` (least significant first). -/
def countF (i : Interaction) (tr : Trace Fp) (t r : Nat) (pv : List Fp) : Fp :=
  countFGo tr t r pv i.mult 0

/-- LogUp sign: `+x` for a send, `-x` for a receive. -/
def signed (send : Bool) (x : Fp) : Fp := if send then x else -x

/-- Signed field count of message `m` on SWIRL bus `b`, row `r` of table `t` (interactions `is`). -/
def rowSum (off : Nat) (is : List Interaction) (tr : Trace Fp) (t r : Nat) (pv : List Fp)
    (b : Nat) (m : List Fp) : Fp :=
  fsum (is.map fun i =>
    if off + i.bus = b ∧ i.msgVal tr t r pv = m then signed i.send (countF i tr t r pv) else 0)

/-- Signed field count of message `m` on SWIRL bus `b` over all rows of table `t`. -/
def tableSum (off : Nat) (is : List Interaction) (tr : Trace Fp) (t : Nat) (pv : List Fp)
    (b : Nat) (m : List Fp) : Fp :=
  fsum ((List.range (tr.height t)).map fun r => rowSum off is tr t r pv b m)

/-- **The translated classical tables' contribution** to SWIRL bus `b`, message `m`: the field
sum over all tables (table `t` evaluated with its own public values `pv t`). -/
def tablesSum (off : Nat) (AP : AirP) (tr : Trace Fp) (pv : Nat → List Fp) (b : Nat)
    (m : List Fp) : Fp :=
  fsum ((List.range AP.tables.length).map fun t =>
    tableSum off (tableAt AP t).interactions tr t (pv t) b m)

/-! ## The TAPE table -/

/-- One TAPE row: the message cells `msg[0..W)`, the count `cnt`, the key selectors `sel[0..K)`. -/
structure TapeRow where
  msg : List Fp
  cnt : Fp
  sel : List Fp
  deriving Repr, DecidableEq, Inhabited

/-- The TAPE table: its keys `(bus, len)` (one interaction each) and its rows. -/
structure Tape where
  keys : List (Nat × Nat)
  rows : List TapeRow
  deriving Repr, DecidableEq, Inhabited

/-- Field count with which one TAPE row sends message `m` on SWIRL bus `b`: interaction `k`
(key `(bus_k, len_k)`) sends `msg[..len_k]` on `bus_k` with count `cnt * sel_k`. -/
def TapeRow.sum (keys : List (Nat × Nat)) (row : TapeRow) (b : Nat) (m : List Fp) : Fp :=
  fsum ((keys.zip row.sel).map fun ks =>
    if ks.1.1 = b ∧ row.msg.take ks.1.2 = m then row.cnt * ks.2 else 0)

/-- **TAPE's contribution** to SWIRL bus `b`, message `m` (all sends). -/
def tapeSum (tape : Tape) (b : Nat) (m : List Fp) : Fp :=
  fsum (tape.rows.map fun row => row.sum tape.keys b m)

/-- Net public multiplicity of `m` on classical bus `b`, in the field: `#sends − #receives`. -/
def netF (AP : AirP) (pub : List Fp) (b : Nat) (m : List Fp) : Fp :=
  (pubCount AP pub b true m : Fp) - (pubCount AP pub b false m : Fp)

/-- **TAPE carries the public messages**: on every translated bus `off + b`, TAPE contributes the
net public multiplicity of every message.  (This is the consequence of `V_d`'s TAPE-root check
under commitment binding: TAPE is `tapeCanon`, `tapeNet_canon`.) -/
def TapeNet (off : Nat) (AP : AirP) (pub : List Fp) (tape : Tape) : Prop :=
  ∀ b m, tapeSum tape (off + b) m = netF AP pub b m

/-! ## The SWIRL relation and the statement verifier's checks -/

/-- Largest public index read by a table's expressions, plus one. -/
def tablePubBound (T : Table) : Nat := (T.exprs.map Expr.pubBound).foldr max 0

/-- **What the SWIRL PIOP enforces** on the translated AIRs (assumption P5, not formalised):
local constraints (with booleanity) on every row with the table's own public values, heights
`2^log` with `2 ≤ log ≤ 24`, and the LogUp balance **mod p** on every SWIRL bus. -/
structure SwirlRel (off : Nat) (AP : AirP) (pv : Nat → List Fp) (tr : Trace Fp) (tape : Tape) :
    Prop where
  constr : ∀ t (ht : t < AP.tables.length), ∀ r, r < tr.height t →
    ∀ e ∈ AP.tables[t].allConstraints, e.eval tr t r (pv t) = 0
  logBound : ∀ t (_ : t < AP.tables.length), 2 ≤ tr.log t ∧ tr.log t ≤ 24
  balance : ∀ b m, tablesSum off AP tr pv b m + tapeSum tape b m = 0

/-- **What the statement verifier `V_d` checks** (plus `TapeNet`, from the TAPE-root check under
commitment binding): height caps, fitting public segments, and public values that agree with
`pub` wherever the table reads them. -/
structure VdChecks (off : Nat) (AP : AirP) (pub : List Fp) (pv : Nat → List Fp) (tr : Trace Fp)
    (tape : Tape) : Prop where
  logCap : ∀ t (ht : t < AP.tables.length), tr.log t ≤ AP.tables[t].maxLog
  pubFit : pubFit AP pub = true
  pvAgree : ∀ t (ht : t < AP.tables.length), ∀ i, i < tablePubBound AP.tables[t] →
    (pv t).getD i 0 = pub.getD i 0
  tape : TapeNet off AP pub tape

end ZkFormal.PQ.StatePort
