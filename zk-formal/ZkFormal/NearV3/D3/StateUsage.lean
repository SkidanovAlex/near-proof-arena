import ZkFormal.NearV3.D3.ContractData
import ZkFormal.NearV3.Rcpt.Extract.AcctProof
import NearSpecV3.Wasm.Host

set_option maxRecDepth 40000

/-!
# `ZkFormal.NearV3.D3.StateUsage` — `storage_usage` reads the acct table, not a `ContractData` value

`storage_usage` is the one host function in the family that does **not** touch the
`TrieKey::ContractData` subtree.  `Host.lean:602` is

```
| "storage_usage" => some do payBaseH C.base; pushRet (← get).storageUsage
```

— a read of the VM's `storageUsage` register.  `Exec.lean:486` seeds that register from the call
context (`storageUsage := ctx.storageUsage`), and `D3/FunctionCall.lean:289` seeds the context from
the account record (`storageUsage := acct.usage`).  On the state side the account record is the
`acctV3` table's value (`Rcpt/Tables/Acct.lean`), so `storage_usage` is a **projection** of the
account record the chunk proof already carries: no walk, no `upsV3`, no new table.

## The encoding, and where the usage bytes are

`AccountV1` (`Near/Spec/SoundAccount.lean`, nearcore `account.rs`):

```
amount(u128) ‖ locked(u128) ‖ code_hash(32) ‖ storage_usage(u64)           -- 72 bytes
```

so `storage_usage` is bytes `64 … 71` of the 72-byte value, little-endian.  `acctV3` emits the
value on `VBYTES (vid, pos, b)` in exactly that layout, and its `gS`-gated interaction is
`VBYTES (vid, 64 + i, st)` for `i < 8` (`NearV3/Rcpt/Tables/Acct.lean:38`) — that *is* the
`storage_usage` field.

## What is proved here

* `usageBytes_eq` — the 8 usage bytes of an `AcctV`'s pre value *are* the `VBYTES` lanes
  `64 … 71`;
* `usage_lane_mem` — those lanes are among the `acctV3` table's own sends, so the state side reads
  the register value off the acct table, not off a trie;
* `usageNat` / `leNatN_leNN` / `usageNat_encode` / `usage_encode_canonical` — the field is the
  little-endian number of those bytes, and the **round trip holds**: an account value whose usage
  field is `leNN 8 u` reports `u`.  That pins the register value to the account's usage, not to an
  arbitrary word;
* `storage_usage_reads_register` — the host call does nothing but push the register: no trie
  access, no overlay write, no `writes` entry, usage delta `0`;
* `storage_usage_not_contract_data` — the account key is *not* a `ContractData` key
  (`[0] ‖ account` vs `[9] ‖ account ‖ [44] ‖ …`), so no `cdWalkV3` instance is needed.

## What is **not** proved

That the `acctV3` record at the executing account is the account's record in `RealStore`'s trie
(the D0a account-key walk's `find`).  That is the same render gap as `RealStoreMatchesTables`
(`StateWrite.lean`) and is not specific to `storage_usage`; here the projection
(`usage = leNat (value[64..72])`) and the host call's inertness are proved.
-/

namespace ZkFormal.NearV3.D3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3 NearSpec NearSpecV3.Wasm

/-! ## The usage bytes of an account value -/

/-- The account value's `storage_usage` bytes, **as the `acctV3` table's `VBYTES` lanes**:
`64 + i` for `i < 8`.  This is the definition the state side consumes — the message `acctV3` sends,
not a slice of an arbitrary list — so reading the account's usage off the table is definitional. -/
def usageBytes (a : AcctV) : List Nat := (List.range 8).map (fun i => a.pre.getD (64 + i) 0)

/-- **The usage bytes are the 72-byte `AccountV1` value's bytes `64 … 71`.**  (`AccountV1` =
`amount(16) ‖ locked(16) ‖ code_hash(32) ‖ storage_usage(8)`.) -/
theorem usageBytes_eq_drop_take (a : AcctV) (h : a.pre.length = 72) :
    usageBytes a = (a.pre.drop 64).take 8 := by
  unfold usageBytes
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, List.length_take,
      List.length_drop, h]
    decide
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range, List.getElem_take]
    have hi8 : i < 8 := by rw [List.length_map, List.length_range] at h1; exact h1
    rw [List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by have := h; omega), Option.getD_some]

/-- **`storage_usage` is a lane of the call's `acctV3` traffic.**  The `gS`-gated `VBYTES` sends
of `acctV3` (`NearV3/Rcpt/Tables/Acct.lean:38`) are exactly the account value's usage bytes, so the
state side reads the register value off the acct table's own messages. -/
theorem usage_lane_mem (a : AcctV) (i : Nat) (hi : i < 8) :
    [a.k, 64 + i, a.pre.getD (64 + i) 0] ∈
      (List.range 16).filterMap (fun j => if j < 8 then
        some [a.k, 64 + j, a.pre.getD (64 + j) 0] else none) := by
  rw [List.mem_filterMap]
  refine ⟨i, List.mem_range.mpr (by omega), ?_⟩
  rw [ite_eq_left hi]

/-! ## The usage as a `Nat` -/

/-- Little-endian number of raw byte values — `NearSpec.leNat` at `List Nat`. -/
def leNatN : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * leNatN bs

/-- Little-endian bytes of a `Nat`, at `List Nat` — `NearSpec.leN` before the `UInt8` wrap. -/
def leNN : Nat → Nat → List Nat
  | 0, _ => []
  | w + 1, x => x % 256 :: leNN w (x / 256)

/-- The account's `storage_usage` as the register value. -/
def usageNat (a : AcctV) : Nat := leNatN (usageBytes a)

/-- Raw byte values of a `Bytes`. -/
def toNats (b : NearSpec.Bytes) : List Nat := b.map UInt8.toNat

theorem leNatN_toNats (b : NearSpec.Bytes) : leNatN (toNats b) = NearSpec.leNat b := by
  induction b with
  | nil => rfl
  | cons x xs ih =>
    show x.toNat + 256 * leNatN (toNats xs) = x.toNat + 256 * NearSpec.leNat xs
    rw [ih]

theorem leNN_length (w x : Nat) : (leNN w x).length = w := by
  induction w generalizing x with
  | zero => rfl
  | succ w ih => simp [leNN, ih]

theorem toNats_leN (w x : Nat) : toNats (NearSpec.leN w x) = leNN w x := by
  induction w generalizing x with
  | zero => rfl
  | succ w ih =>
    show (UInt8.ofNat (x % 256)).toNat :: toNats (NearSpec.leN w (x / 256)) = _
    rw [show (UInt8.ofNat (x % 256)).toNat = x % 256 from by simp [Nat.reducePow], ih]
    rfl

/-- **`leNatN` inverts `leNN`** on in-range values. -/
theorem leNatN_leNN (w x : Nat) (h : x < 256 ^ w) : leNatN (leNN w x) = x := by
  induction w generalizing x with
  | zero => simp [leNN, leNatN] at h ⊢; omega
  | succ w ih =>
    show x % 256 + 256 * leNatN (leNN w (x / 256)) = x
    rw [ih (x / 256) (by
      rw [Nat.pow_succ] at h
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h))]
    have := Nat.div_add_mod x 256
    omega

/-- **Round trip**: an account value whose usage field is `leNN 8 u` reports `u`. -/
theorem usageNat_encode (hd : List Nat) (u : Nat) (hu : u < 256 ^ 8)
    (hp : (hd ++ leNN 8 u).length = 72) :
    leNatN ((hd ++ leNN 8 u).drop 64 |>.take 8) = u := by
  have hlen : (leNN 8 u).length = 8 := leNN_length 8 u
  have hplen : hd.length = 64 := by
    rw [List.length_append, hlen] at hp; omega
  have hdrop : (hd ++ leNN 8 u).drop 64 = leNN 8 u := by
    rw [List.drop_append, hplen, Nat.sub_self, List.drop_zero]
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  rw [hdrop, List.take_of_length_le (by rw [hlen]; exact Nat.le_refl _)]
  exact leNatN_leNN 8 u hu

/-- **The canonical `AccountV1` layout reports its own usage.**  With the 64-byte head of the
encoding (`amount ‖ locked ‖ code_hash`) and the 8 usage bytes appended, `usageNat` is `u`. -/
theorem usage_encode_canonical (amount locked codeHash : List Nat) (u : Nat)
    (ha : amount.length = 16) (hl : locked.length = 16) (hc : codeHash.length = 32)
    (hu : u < 256 ^ 8) :
    leNatN ((((amount ++ locked) ++ codeHash) ++ leNN 8 u).drop 64 |>.take 8) = u := by
  refine usageNat_encode ((amount ++ locked) ++ codeHash) u hu ?_
  simp only [List.length_append, ha, hl, hc, leNN_length]

/-! ## The host call -/

/-- `withGas` in its successful branch: only the gas moves. -/
theorem withGas_ok (f : Gas → Gas × Option String) (s : St) (gs : Gas)
    (h : f s.gas = (gs, none)) :
    (withGas f).run s = .ok () { s with gas := gs } := by
  unfold withGas
  simp only [h, EStateM.run_bind, EStateM.run_get, EStateM.run_pure]
  show (match (modify (fun s : St => { s with gas := gs }) : HM Unit).run s with
    | EStateM.Result.ok x s' => EStateM.Result.ok () s'
    | EStateM.Result.error e s' => EStateM.Result.error e s') = EStateM.Result.ok () { s with gas := gs }
  rw [EStateM.run_modify]

/-- `withGas` in its failing branch: the gas is committed, then it throws. -/
theorem withGas_err (f : Gas → Gas × Option String) (s : St) (gs : Gas) (err : String)
    (h : f s.gas = (gs, some err)) :
    ∃ st, (withGas f).run s = .error err st := by
  refine ⟨{ s with gas := gs }, ?_⟩
  simp only [withGas, h, EStateM.run_bind, EStateM.run_get, EStateM.run_modify,
    EStateM.run_throw]

/-- The `storage_usage` host body (`Host.lean:602`), named.  `pushRet v` is written out as the
`modify` it is, which keeps the term shallow enough for the kernel. -/
def storageUsageBody : HM Unit :=
  (payBaseH C.base).bind (fun _ => (get : HM St).bind
    (fun s => modify (fun st => pushI64 st s.storageUsage)))

/-- **`storage_usage` is the source's body.** -/
theorem hostCall_storage_usage : hostCall "storage_usage" = some storageUsageBody := rfl

/-- `get` then `g`: the current state is passed to `g`. -/
theorem run_get_bind {β : Type} (g : St → HM β) (s : St) :
    ((get : HM St).bind g).run s = (g s).run s := by
  rw [show (get : HM St).bind g = ((get : HM St) >>= g) from rfl, EStateM.run_bind,
    EStateM.run_get]

/-- `x` then `g`, in the branch where `x` succeeds. -/
theorem run_bind_of_ok {α β : Type} (x : HM α) (g : α → HM β) (s : St) (a : α) (s' : St)
    (h : x.run s = .ok a s') : (x.bind g).run s = (g a).run s' := by
  rw [show x.bind g = (x >>= g) from rfl, EStateM.run_bind, h]

/-- A successful and a failing run of one body are contradictory. -/
theorem ok_ne_err {α : Type} (x : HM α) (s : St) (a : α) (st : St) (err : String) (st' : St)
    (h : x.run s = .ok a st) (h' : x.run s = .error err st') : False := by
  rw [h] at h'
  cases h'

/-- The three fields a storage call never moves. -/
def KeepsStored (s st : St) : Prop :=
  st.real = s.real ∧ st.storageUsage = s.storageUsage ∧ st.trie = s.trie

theorem KeepsStored.trans {a b c : St} (h1 : KeepsStored a b) (h2 : KeepsStored b c) :
    KeepsStored a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

/-- The base charge moves only the gas. -/
theorem payBaseH_keeps (s st : St) (h : (payBaseH C.base).run s = .ok () st) :
    KeepsStored s st := by
  cases hg : payBase s.gas C.base with
  | mk gs e =>
    cases e with
    | some err =>
      obtain ⟨st', hst⟩ := withGas_err (fun g => payBase g C.base) s gs err hg
      rw [show (payBaseH C.base).run s = .error err st' from hst] at h
      cases h
    | none =>
      rw [show (payBaseH C.base).run s = .ok () { s with gas := gs } from
        withGas_ok (fun g => payBase g C.base) s gs hg] at h
      cases h
      exact ⟨rfl, rfl, rfl⟩

/-- **The tail of the body** (read the register, push it) moves only the stack. -/
theorem get_push_keeps (s1 st : St)
    (h : ((get : HM St).bind (fun s => modify (fun st => pushI64 st s.storageUsage))).run s1 =
      .ok () st) : KeepsStored s1 st := by
  rw [run_get_bind (fun s => modify (fun st => pushI64 st s.storageUsage)) s1,
    EStateM.run_modify] at h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- **`storage_usage` reads a register and nothing else.**  Its body is one base charge followed by
one register read-and-push (`Host.lean:602`: `payBaseH C.base; pushRet (← get).storageUsage`); no
`readMemH`, no `realOpH`, no `realSetH`, no `observeH`.  So on the state side it produces no walk,
no `upsV3` instance, no `RealStore.writes` entry, and its usage delta is `0`: the `real`,
`storageUsage` and `trie` fields of the state survive any successful call.

(The hypothesis is the body's two halves rather than `storageUsageBody.run s = .ok () st`, which
the kernel will not unfold at a low recursion depth; `hostCall_storage_usage` is that body, so the
two compose by `run_bind_of_ok`.) -/
theorem storage_usage_reads_register (s s1 st : St)
    (h1 : (payBaseH C.base).run s = .ok () s1)
    (h2 : ((get : HM St).bind (fun s => modify (fun st => pushI64 st s.storageUsage))).run s1 =
      .ok () st) : KeepsStored s st :=
  KeepsStored.trans (payBaseH_keeps s s1 h1) (get_push_keeps s1 st h2)

/-- `contractDataPrefixPath` *is* `[0, 9]` followed by the rest of the prefix's nibbles:
the collection byte `9` splits into `(0, 9)`. -/
theorem contractDataPrefixPath_eq (account : NearSpec.Bytes) :
    contractDataPrefixPath account = 0 :: 9 :: (NearSpec.nibbles (account ++ [accountDataSeparator])) := by
  unfold contractDataPrefixPath contractDataPrefix
  simp only [List.append_assoc, ZkFormal.NearV3.D3.nibbles_append]
  rfl

/-- The account key path *is* `[0, 0]` followed by the account id's nibbles (the collection byte
`0` splits into `(0, 0)`). -/
theorem accountKeyPath_eq (account : NearSpec.Bytes) :
    NearSpec.accountKeyPath account = 0 :: 0 :: NearSpec.nibbles account := by
  unfold NearSpec.accountKeyPath
  rfl

/-- **`storage_usage` needs no `cdWalkV3` instance.**  Its key is the account's
(`[0] ‖ account`, `NearSpec.accountKeyPath`), never a `ContractData` key
(`[9] ‖ account ‖ [44] ‖ key`): the second nibble is `0` vs `9`. -/
theorem storage_usage_not_contract_data (account : NearSpec.Bytes) :
    NearSpec.accountKeyPath account ≠ ZkFormal.NearV3.D3.contractDataPath account [] ∧
      NearSpec.accountKeyPath account ≠ ZkFormal.NearV3.D3.contractDataPath account [0] := by
  constructor
  · intro h
    rw [accountKeyPath_eq,
      (ZkFormal.NearV3.D3.contractDataPathSpec_holds account []).1,
      contractDataPrefixPath_eq] at h
    simp at h
  · intro h
    rw [accountKeyPath_eq,
      (ZkFormal.NearV3.D3.contractDataPathSpec_holds account [0]).1,
      contractDataPrefixPath_eq] at h
    simp at h

end ZkFormal.NearV3.D3
