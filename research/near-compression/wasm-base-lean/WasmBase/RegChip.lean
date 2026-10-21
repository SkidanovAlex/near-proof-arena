import WasmBase.HostChip
import WasmBase.RegisterSpace
/-!
# WasmBase.RegChip — the REG table: host bytes ↔ channel space 6

`results/pq-wasm-base/README.md` §14.2: "These live on the Wasm side as a new channel space 6, keyed
by `(register_id, pos)`, plus a length message per register.  A host function that fills a register
(`input`, context getters, `storage_read`, `promise_result`) receives the bytes on `HOSTB` from the
state side.  `read_register` / `write_register` are then Wasm-side only."

Registers are a **persistent state**, so a row is modelled like the globals (channel space 2): every
access **produces** the register's message at time `ts`, and consumes the previous one at `tp` unless
it is the first row that creates the register (`fresh = 0`).  That is what makes a register readable
twice: the read re-produces the message it consumed.

One REG row per **register byte** (`kind = 0`) or per **register length** (`kind = 1`):

```
act, kind, rd, rid, pos, len, byte, hid, ts, dir, gap, tp, hp, ptr
```

* `rd = 0` — **fill**: the row creates the register (`input`).  Its byte rows *receive* the bytes
  from `HOSTB` (`dir = 1`, state → Wasm); `HOSTB` carries the state-side half of the same message
  (`HOSTB.reg = 1`), so the wire balances across the two tables.  A fill row always has
  `fresh = 0` (`cFreshFill`).
* `rd = 1` — **read**: the row consumes the current message at `tp` and re-produces it at `ts`
  (`read_register`, `register_len`, `value_return` from a register).  A register read is Wasm-side
  only (README §14.2), so it emits no `HOSTB` message.  `ptr` is the destination address of a byte
  read, carried for the **deferred** MEMIO link (see below).

`dir = 1 − rd` on a byte row (`cDirRd`), matching `HOSTB`'s `reg = 1` half.

## Constraints (all degree ≤ 2)

| name | expression | meaning |
|---|---|---|
| `cAct` | `act·(act−1)` | row activity is a bit |
| `cKind` | `kind·(kind−1)` | `kind` is a bit |
| `cRd` | `rd·(rd−1)` | `rd` is a bit |
| `cDir` | `dir·(dir−1)` | `dir` is a bit |
| `cDirRd` | `act·(1−kind)·(dir − (1 − rd))` | a byte row's `dir` is `1 − rd` |
| `cFreshFill` | `act·(1−rd)·fresh` | a fill row creates the register (`fresh = 0`) |
| `cPosLtLen` | `act·(1−kind)·(len − pos − 1 − gap)` | `pos + gap + 1 = len` on an active byte row |
| time check | `r16 (ts−tp−1−65536·hp)`, `r16 (4·hp)` with count `act·fresh` | `tp < ts` on a consuming row |

plus the lookups: `byteQ 0 byte 0 0 (act·(1−kind))` (`byte < 256`), `r16 gap` (`act·(1−kind)`),
`r16 len` and `r16 rid` (`act`).

The counts are all bits (`act`, `kind`, `rd` are), so the space-6 and `HOSTB` sides of this table are
permutation buses in the sense of `WasmBase.Bus.perm_exact`.

## Domain conditions (explicit, decidable, not polynomial)

`rid, len < 2^16` from the R16 lookups, hence `pos < 2^16` (from `pos < len`), which is inside the
register model's key domain `pos, len < 2^24` (`Register.posOK`/`lenOK`).  The model's stricter
`rid ≤ 99` (`maxNumberRegisters = 100`) is the stated register domain (`Register.regOK`); it is not
a row constraint (a wider `rid` is harmless for the wire, and the state side already bounds it).
`reg_row_key_bounds` below records the implication for the AIR-visible bounds.

## What is *not* constrained (the named blocking sub-problem)

1. **The group walk.**  Nothing forces the byte rows of one register to be exactly `pos = 0 .. len−1`
   with no gaps, duplicates or extra rows, nor forces the length row's `len` to equal that count.
   That is exactly `Register.RegLenAgree` (stated, not proved).  It needs a `next`-based structure
   keyed by `(rid, ts)` plus a `cLast`-style endpoint pin — the shape HOSTB already uses for
   `(ts, dir)`.
2. **Joining REG into the `wasmBaseHostAir` execution theorem.**  REG carries space-6 CH
   interactions, so `Main/ExecHost.msgs_ch_host` and the bus decomposition would have to include it.
   This lane keeps the proved 26-table AIR byte-identical and exports REG as the separate
   `wasmBaseRegAir` (`wasmBaseHostAir ++ [REG]`, REG at index 26); the trace generator and the KAT
   use that for register programs.
-/
namespace WasmBase
namespace Chips

namespace Reg
def act : Nat := 0
def kind : Nat := 1
def rd : Nat := 2
def rid : Nat := 3
def pos : Nat := 4
def blen : Nat := 5
def bv : Nat := 6
def hid : Nat := 7
def ts : Nat := 8
def dir : Nat := 9
def gap : Nat := 10
def fresh : Nat := 11
def tp : Nat := 12
def hp : Nat := 13
def ptr : Nat := 14

def cols : List String := ["act", "kind", "rd", "rid", "pos", "len", "byte", "hid", "ts", "dir",
  "gap", "fresh", "tp", "hp", "ptr"]

/-- `1 − kind`: the byte rows. -/
def isB : Expr := 1 - v kind
/-- `kind`: the length rows. -/
def isL : Expr := v kind
/-- `1 − rd`: the fill (produce) rows. -/
def fill : Expr := 1 - v rd
/-- `rd`: the read (consume) rows. -/
def read : Expr := v rd

def cAct : Expr := bool (v act)
def cKind : Expr := bool (v kind)
def cRd : Expr := bool (v rd)
def cDir : Expr := bool (v dir)
def cFresh : Expr := bool (v fresh)
/-- On a byte row, `dir = 1 − rd`: a fill receives from the state, a read sends to it. -/
def cDirRd : Expr := v act * isB * (v dir - (1 - v rd))
/-- A fill row creates the register: nothing was there to consume. -/
def cFreshFill : Expr := v act * fill * v fresh

/-- `pos + gap + 1 = len` on an active byte row. -/
def cPosLtLen : Expr := v act * isB * (v blen - v pos - 1 - v gap)

def constraints : List Expr :=
  [cAct, cKind, cRd, cFresh, cDir, cDirRd, cFreshFill, cPosLtLen]

/-- The space-6 byte slot: `rid · 2^24 + pos + 1` (`Register.byteSlot rid pos`). -/
def byteSlotE : Expr := v rid * Expr.c Register.cap + v pos + 1
/-- The space-6 length slot: `rid · 2^24` (`Register.lenSlot rid`). -/
def lenSlotE : Expr := v rid * Expr.c Register.cap
/-- The `HOSTB` message of a fill byte. -/
def hbMsg : List Expr := [v ts, v hid, v dir, v pos, v bv]

def inters : List Inter :=
  [-- every active row produces the register's new message
   chSend (Expr.c Register.space) byteSlotE (Expr.c Register.byteTag) [v bv, 0, 0, 0] (v ts)
     (v act * isB),
   chSend (Expr.c Register.space) lenSlotE (Expr.c Register.lenTag) [v blen, 0, 0, 0] (v ts)
     (v act * isL),
   -- every active row except the creating fill consumes the previous message
   chRecv (Expr.c Register.space) byteSlotE (Expr.c Register.byteTag) [v bv, 0, 0, 0] (v tp)
     (v act * isB * v fresh),
   chRecv (Expr.c Register.space) lenSlotE (Expr.c Register.lenTag) [v blen, 0, 0, 0] (v tp)
     (v act * isL * v fresh),
   -- the HOSTB wire: a fill *receives* the byte from the state side
   ⟨busHostB, false, v act * isB * fill, hbMsg⟩,
   -- a read's producer time is earlier (`tp < ts`), as every CH consumer
   r16 (v ts - v tp - 1 - 65536 * v hp) (v act * v fresh),
   r16 (4 * v hp) (v act * v fresh),
   -- `byte < 256` and the 16-bit bounds
   byteQ 0 (v bv) 0 0 (v act * isB),
   r16 (v gap) (v act * isB),
   r16 (v blen) (v act),
   r16 (v rid) (v act)]

def table : Table := ⟨"REG", cols, constraints, inters⟩
end Reg

end Chips

/-- The direct-Wasm base AIR with host calls **and the register wire**: `wasmBaseHostAir` plus REG
(index 26).  `wasmBaseHostAir` is untouched, so every proved index (0-25) is unchanged. -/
def wasmBaseRegAir (nloc ngl : Nat) : Air :=
  { tables := (wasmBaseHostAir nloc ngl).tables ++ [Chips.Reg.table]
    numPub := (wasmBaseHostAir nloc ngl).numPub }

theorem reg_air_len (nloc ngl : Nat) : (wasmBaseRegAir nloc ngl).tables.length = 27 := rfl

theorem reg_air_26 (nloc ngl : Nat) :
    (wasmBaseRegAir nloc ngl).tables[26]'(by rw [reg_air_len]; decide) = Chips.Reg.table := rfl

/-- REG answers (never queries) R16. -/
theorem reg_table_r16 : Chips.Reg.table.inters.all
    (fun i => i.bus != Chips.busR16 || i.send) = true := by decide

/-- Every REG CH interaction is on channel space 6 (register byte / length).  In particular REG never
touches the operand stack (space 0), the locals (`≥ 16`), the globals (2), the memory (3), the call
records (4) or the budget (5). -/
theorem reg_space_ok : Chips.Reg.table.inters.all (fun i =>
    i.bus != Chips.busStk || i.msg.head? == some (Expr.c Register.space)) = true := by decide

/-- **The AIR-visible key bounds are inside the register model's key domain.**  From the R16
lookups (`rid, len < 2^16`), `pos + gap + 1 = len` and `gap < 2^16` we get `pos < 2^24` and
`len < 2^24`; with the stated `rid ≤ 99`, that is `Register.regOK`, `posOK` and `lenOK`. -/
theorem reg_row_key_bounds {rid pos len gap : Nat} (hrid : rid ≤ 99) (hgap : gap < 65536)
    (hlen : len < 65536) (hpos : pos + gap + 1 = len) :
    Register.posOK pos = true ∧ Register.lenOK len = true ∧ Register.regOK rid = true := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Register.posOK_iff]; omega
  · rw [Register.lenOK_iff]; omega
  · rw [Register.regOK_iff]; exact hrid

end WasmBase
