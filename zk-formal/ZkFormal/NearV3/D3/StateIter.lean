import NearSpecV3.Wasm.Host

/-!
# `ZkFormal.NearV3.D3.StateIter` — `storage_iter_*` is *out of domain*, not out of reach

The D3α host interface (`spec/lean/v3/NearSpecV3/Wasm/Host.lean:795-801`) does **not** model
iteration.  The three iterator host functions are

```
| "storage_iter_prefix" => some do let _ ← popArgs 2; hErr "Deprecated { method_name: … }"
| "storage_iter_range"  => some do let _ ← popArgs 4; hErr "Deprecated { method_name: … }"
| "storage_iter_next"   => some do let _ ← popArgs 3; hErr "Deprecated { method_name: … }"
```

i.e. they **always abort** with `HostError(Deprecated …)` after popping their arguments.  So the
question this lane was asked — "does prefix/range iteration need a new ordered table?" — has a
semantic answer, not an engineering one: under D3α there is nothing to prove about iteration,
because no run of a `storage_iter_*` call can reach a state change.  (In nearcore the functions
exist but are deprecated; `Exec.callHost` turns the abort into a Wasm `abort`, not into an
`unmodeled` outcome, because the error does not start with `"unmodeled"`.)

## What is proved

* `popArgs_ok` — `popArgs n` always returns `ok`: the vector it builds has exactly `n` entries, so
  the arity test always takes the `pure` branch.  (In the spec the "`unmodeled host-call arity`"
  branch is dead.)
* `popArgs_preserves` — `popArgs` touches only `stack`.  Every other field of `St` — `real`
  (the trie-backed store: overlay, `writes`, roots), `storageUsage`, `registers`, `trie`,
  `actions`, pages, gas — is unchanged.  So a `storage_iter_*` abort cannot move storage.
* `iter_prefix_aborts`, `iter_range_aborts`, `iter_next_aborts` — each host call runs to
  `.error (HostError(Deprecated …))`, on **every** state, with only `stack` moved.

## What is **not** claimed, and what the smallest sound slice would be

A *real* prefix iterator (`IntoIterator<Item = (Vec<u8>, Vec<u8>)>` over
`TrieKey::ContractData` in lexicographic key order) needs, on top of everything this lane already
has:

1. an **ordered walk**.  `cdWalkV3` follows one path, decided by `CDKEYNIB`.  Returning the *next*
   key in lexicographic order is a different operation (nearcore's `TrieIterator` descends and then
   backtracks over siblings), so the `EDGE` provider would have to expose **sibling order** as well:
   a new `ORD (N, i, N_child, isNext)` message and a new table family `ordV3`; or, equivalently, a
   sorted-key witness table `srtV3` with rows `(τ, j, key_j, key_{j+1})` checked for lexicographic
   increase.
2. a **cursor**.  `storage_iter_next(iterator_id, key_register, value_register)` returns successive
   entries of one iterator, so the state proof must carry a cursor register file across calls, plus
   a `NEXT` chain linking the `j`-th and `(j+1)`-th entries.
3. a **range predicate** the AIR can check cheaply.  `isPrefix(prefix, key)` on nibbles is easy
   (`contractDataPrefixPath` is constant for the call), but `lo ≤ key ≤ hi` lexicographic over full
   keys needs a first-difference witness over the nibbles the AIR sees — a new column block, not a
   reuse.

The smallest sound slice, if the rung is later widened, is therefore:

```
prefix-only, single call, bounded result count N:
  srtV3 over the account's contract-data keys (sorted witness) + a PREFIX row block checking
  isPrefix(prefixPath, key_j) on every returned key + one ORDER chain over the j's.
range / next are out of even that slice (they need the cursor).
```

That is a **new table family** of roughly the same weight as the whole `cdWalkV3` + `upsV3` state
half, and it has no consumer in the current D3α specification.  It is reported as out of reach
*for this lane*, not as a missing lemma.
-/

namespace ZkFormal.NearV3.D3

open NearSpecV3.Wasm

/-! ## `popArgs` plumbing -/

/-- One iteration of `popArgs`'s `for` loop: pop, write the state back, append the value. -/
def popStep (out : Array Nat) : HM (ForInStep (Array Nat)) := do
  let st : St ← get
  set (popN st).snd
  pure (ForInStep.yield (out.push (popN st).fst))

/-- One `popStep` succeeds, grows the accumulator by one, and returns the popped state. -/
theorem popStep_run (out : Array Nat) (s : St) :
    (popStep out).run s = .ok (ForInStep.yield (out.push (popN s).fst)) ((popN s).snd) := by
  unfold popStep
  rw [EStateM.run_bind, EStateM.run_get]
  simp only [EStateM.run_bind, EStateM.run_set]
  exact EStateM.run_pure _ _

/-- `popN` only shrinks the stack. -/
theorem popN_snd_real (s : St) : (popN s).snd.real = s.real := by
  unfold popN popV
  cases s.stack.back? with
  | none => rfl
  | some v => cases v <;> rfl

theorem popN_snd_usage (s : St) : (popN s).snd.storageUsage = s.storageUsage := by
  unfold popN popV
  cases s.stack.back? with
  | none => rfl
  | some v => cases v <;> rfl

theorem popN_snd_registers (s : St) : (popN s).snd.registers = s.registers := by
  unfold popN popV
  cases s.stack.back? with
  | none => rfl
  | some v => cases v <;> rfl

theorem popN_snd_trie (s : St) : (popN s).snd.trie = s.trie := by
  unfold popN popV
  cases s.stack.back? with
  | none => rfl
  | some v => cases v <;> rfl

theorem popN_snd_actions (s : St) : (popN s).snd.actions = s.actions := by
  unfold popN popV
  cases s.stack.back? with
  | none => rfl
  | some v => cases v <;> rfl

/-- A `forIn` loop of `popStep`s over any list succeeds and grows the accumulator by its length. -/
theorem forIn_len {α : Type} (f : α → Array Nat → HM (ForInStep (Array Nat)))
    (hf : ∀ (a : α) (b : Array Nat) (s : St),
      ∃ b' s', (f a b).run s = .ok (ForInStep.yield b') s' ∧ b'.size = b.size + 1) :
    ∀ (l : List α) (b : Array Nat) (s : St),
      ∃ b' s', (forIn l b f).run s = .ok b' s' ∧ b'.size = b.size + l.length
  | [], b, s => ⟨b, s, by simp, by simp⟩
  | a :: as, b, s => by
    rw [List.forIn_cons, EStateM.run_bind]
    obtain ⟨b1, s1, h1, hs1⟩ := hf a b s
    rw [h1]
    simp only
    obtain ⟨b2, s2, h2, hs2⟩ := forIn_len f hf as b1 s1
    exact ⟨b2, s2, h2, by rw [hs2, hs1]; simp; omega⟩

/-- The loop of `popStep`s over any list leaves every stored field alone. -/
theorem loop_preserves : ∀ (l : List Nat) (b : Array Nat) (s : St) (b' : Array Nat) (s' : St),
    (forIn l b (fun _ out => popStep out)).run s = .ok b' s' →
    s'.real = s.real ∧ s'.storageUsage = s.storageUsage ∧ s'.registers = s.registers ∧
      s'.trie = s.trie ∧ s'.actions = s.actions
  | [], b, s, b', s', h => by
    simp only [List.forIn_nil, EStateM.run_pure, EStateM.Result.ok.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | x :: xs, b, s, b', s', h => by
    rw [List.forIn_cons, EStateM.run_bind, popStep_run] at h
    simp only at h
    obtain ⟨hreal, husage, hreg, htrie, hact⟩ := loop_preserves xs _ (popN s).snd _ _ h
    exact ⟨hreal.trans (popN_snd_real s), husage.trans (popN_snd_usage s),
      hreg.trans (popN_snd_registers s), htrie.trans (popN_snd_trie s),
      hact.trans (popN_snd_actions s)⟩

/-- Runs `x` then `g`, when `x` succeeds — `EStateM.run_bind` in the branch we use. -/
theorem run_bind_of_ok {α β : Type} (x : HM α) (g : α → HM β) (s : St) (a : α) (s' : St)
    (h : x.run s = .ok a s') : (x.bind g).run s = (g a).run s' := by
  rw [show x.bind g = (x >>= g) from rfl, EStateM.run_bind, h]

/-- The arity test at the end of `popArgs` (never the error branch, see `popArgs_ok`). -/
def vecCheck (n : Nat) (out : Array Nat) : HM (Vector Nat n) :=
  if h : out.reverse.size = n then pure (Vector.mk out.reverse h)
  else throw "unmodeled host-call arity"

/-- The `popArgs` body, spelled with `popStep` and `vecCheck` (definitionally the source). -/
theorem popArgs_eq (n : Nat) :
    popArgs n = (forIn (List.range' 0 n) #[] (fun _ out => popStep out)).bind (vecCheck n) := by
  unfold popArgs vecCheck
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rfl

/-- **`popArgs n` always returns `ok`.** -/
theorem popArgs_ok (n : Nat) (s : St) : ∃ v s', (popArgs n).run s = .ok v s' := by
  obtain ⟨out', s', h, hsz⟩ := forIn_len (fun (_ : Nat) out => popStep out)
    (fun _ b s => ⟨_, _, popStep_run b s, by simp⟩) (List.range' 0 n) #[] s
  have hrev : out'.reverse.size = n := by simpa using hsz
  refine ⟨Vector.mk out'.reverse hrev, s', ?_⟩
  rw [popArgs_eq, run_bind_of_ok _ _ _ _ _ h]
  unfold vecCheck
  rw [dite_eq_left hrev, EStateM.run_pure]

/-- **`popArgs n` changes nothing but the stack**, on every argument count and every state. -/
theorem popArgs_preserves (n : Nat) (s : St) :
    ∃ v s', (popArgs n).run s = .ok v s' ∧ s'.real = s.real ∧
      s'.storageUsage = s.storageUsage ∧ s'.registers = s.registers ∧ s'.trie = s.trie ∧
      s'.actions = s.actions := by
  obtain ⟨out', s', h, hsz⟩ := forIn_len (fun (_ : Nat) out => popStep out)
    (fun _ b s => ⟨_, _, popStep_run b s, by simp⟩) (List.range' 0 n) #[] s
  have hrev : out'.reverse.size = n := by simpa using hsz
  obtain ⟨hreal, husage, hreg, htrie, hact⟩ := loop_preserves _ _ _ _ _ h
  refine ⟨Vector.mk out'.reverse hrev, s', ?_, hreal, husage, hreg, htrie, hact⟩
  rw [popArgs_eq, run_bind_of_ok _ _ _ _ _ h]
  unfold vecCheck
  rw [dite_eq_left hrev, EStateM.run_pure]

/-! ## The three iterator host functions -/

/-- A `popArgs`-then-abort body: it always aborts, and only the stack moved. -/
theorem pops_then_abort (n : Nat) (e : String) (s : St) :
    ∃ s', ((do let _ ← popArgs n; hErr e) : HM Unit).run s = .error s!"HostError({e})" s' ∧
      s'.real = s.real ∧ s'.storageUsage = s.storageUsage ∧ s'.registers = s.registers ∧
      s'.trie = s.trie ∧ s'.actions = s.actions := by
  obtain ⟨v, s', h, hreal, husage, hreg, htrie, hact⟩ := popArgs_preserves n s
  refine ⟨s', ?_, hreal, husage, hreg, htrie, hact⟩
  rw [show ((do let _ ← popArgs n; hErr e) : HM Unit) = (popArgs n).bind (fun _ => hErr e)
    from rfl, run_bind_of_ok _ _ _ _ _ h]
  rfl

/-- The `storage_iter_prefix` host body. -/
def iterPrefixBody : HM Unit := do
  let _ ← popArgs 2
  hErr "Deprecated { method_name: \"storage_iter_prefix\" }"

/-- The `storage_iter_range` host body. -/
def iterRangeBody : HM Unit := do
  let _ ← popArgs 4
  hErr "Deprecated { method_name: \"storage_iter_range\" }"

/-- The `storage_iter_next` host body. -/
def iterNextBody : HM Unit := do
  let _ ← popArgs 3
  hErr "Deprecated { method_name: \"storage_iter_next\" }"

theorem hostCall_iter_prefix : hostCall "storage_iter_prefix" = some iterPrefixBody := rfl
theorem hostCall_iter_range : hostCall "storage_iter_range" = some iterRangeBody := rfl
theorem hostCall_iter_next : hostCall "storage_iter_next" = some iterNextBody := rfl

theorem iterPrefixBody_eq :
    iterPrefixBody = (popArgs 2).bind (fun _ =>
      hErr "Deprecated { method_name: \"storage_iter_prefix\" }") := rfl
theorem iterRangeBody_eq :
    iterRangeBody = (popArgs 4).bind (fun _ =>
      hErr "Deprecated { method_name: \"storage_iter_range\" }") := rfl
theorem iterNextBody_eq :
    iterNextBody = (popArgs 3).bind (fun _ =>
      hErr "Deprecated { method_name: \"storage_iter_next\" }") := rfl

/-- **`storage_iter_prefix` always aborts**, and moves nothing but the stack. -/
theorem iter_prefix_aborts (s : St) :
    ∃ s', iterPrefixBody.run s =
      .error "HostError(Deprecated { method_name: \"storage_iter_prefix\" })" s' ∧
      s'.real = s.real ∧ s'.storageUsage = s.storageUsage := by
  obtain ⟨s', h, hr, hu, -, -, -⟩ := pops_then_abort 2 _ s
  exact ⟨s', iterPrefixBody_eq ▸ h, hr, hu⟩

/-- **`storage_iter_range` always aborts**, and moves nothing but the stack. -/
theorem iter_range_aborts (s : St) :
    ∃ s', iterRangeBody.run s =
      .error "HostError(Deprecated { method_name: \"storage_iter_range\" })" s' ∧
      s'.real = s.real ∧ s'.storageUsage = s.storageUsage := by
  obtain ⟨s', h, hr, hu, -, -, -⟩ := pops_then_abort 4 _ s
  exact ⟨s', iterRangeBody_eq ▸ h, hr, hu⟩

/-- **`storage_iter_next` always aborts**, and moves nothing but the stack. -/
theorem iter_next_aborts (s : St) :
    ∃ s', iterNextBody.run s =
      .error "HostError(Deprecated { method_name: \"storage_iter_next\" })" s' ∧
      s'.real = s.real ∧ s'.storageUsage = s.storageUsage := by
  obtain ⟨s', h, hr, hu, -, -, -⟩ := pops_then_abort 3 _ s
  exact ⟨s', iterNextBody_eq ▸ h, hr, hu⟩

end ZkFormal.NearV3.D3
