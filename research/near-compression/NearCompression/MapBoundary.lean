import NearCompression.Boundary
import Std.Data.HashMap.Lemmas

/-!
Map entries are serializable without exposing hash-table bucket layout. The
round trip is observational equivalence, not structural equality. This module
proves that the actual trie accounting/recorder operations respect that
relation. Whole-machine simulation and byte encoding remain separate work.
-/
namespace NearCompression
open NearSpecV3.Wasm

/-- ByteArray equality delegates to its byte array; this supplies the missing
Std instance locally without changing the interpreter's equality operation. -/
theorem byte_array_beq_eq (a b : ByteArray) (h : (a == b) = true) : a = b := by
  apply ByteArray.ext
  exact eq_of_beq (show (a.data == b.data) = true from h)

local instance : LawfulBEq ByteArray where
  eq_of_beq := byte_array_beq_eq _ _
  rfl := by intro a; change (a.data == a.data) = true; exact BEq.rfl

/-- Rebuild only the logical entries. Order need not match physical buckets. -/
def rebuildMap {V : Type} (m : Std.HashMap ByteArray V) : Std.HashMap ByteArray V :=
  Std.HashMap.ofList m.toList

theorem rebuild_map_equiv {V : Type} (m : Std.HashMap ByteArray V) :
    (rebuildMap m).Equiv m := by
  apply Std.HashMap.Equiv.of_forall_getElem?_eq
  intro k
  cases he : m[k]? with
  | none =>
    apply Std.HashMap.getElem?_ofList_of_contains_eq_false
    rw [Std.HashMap.map_fst_toList_eq_keys, Std.HashMap.contains_keys,
      Std.HashMap.contains_eq_isSome_getElem?, he]
    rfl
  | some v =>
    exact Std.HashMap.getElem?_ofList_of_mem (by simp)
      m.distinct_keys_toList (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr he)

/-- Accounting observations include both counters, even where protocol gas
prices happen to be equal. -/
def AcctEquivalent (a b : TTN.Acct) : Prop :=
  a.cache.Equiv b.cache ∧ a.db = b.db ∧ a.mem = b.mem

def RecorderEquivalent (a b : TTN.Recorder) : Prop :=
  a.set.Equiv b.set ∧ a.size = b.size

def normalizeAcct (a : TTN.Acct) : TTN.Acct := { a with cache := rebuildMap a.cache }
def normalizeRecorder (r : TTN.Recorder) : TTN.Recorder := { r with set := rebuildMap r.set }

theorem normalize_acct_equiv (a : TTN.Acct) : AcctEquivalent (normalizeAcct a) a :=
  ⟨rebuild_map_equiv _, rfl, rfl⟩

theorem normalize_recorder_equiv (r : TTN.Recorder) : RecorderEquivalent (normalizeRecorder r) r :=
  ⟨rebuild_map_equiv _, rfl⟩

theorem acct_touch_equiv (a b : TTN.Acct) (h : AcctEquivalent a b) (key : ByteArray) :
    AcctEquivalent (a.touch key) (b.touch key) := by
  obtain ⟨hc, hd, hm⟩ := h
  have he := hc.contains_eq (k := key)
  unfold TTN.Acct.touch
  rw [he]
  split
  · exact ⟨hc, hd, congrArg (· + 1) hm⟩
  · exact ⟨hc.insert key (), congrArg (· + 1) hd, hm⟩

theorem acct_touch_all_equiv (a b : TTN.Acct) (h : AcctEquivalent a b)
    (keys : List ByteArray) : AcctEquivalent (a.touchAll keys) (b.touchAll keys) := by
  induction keys generalizing a b with
  | nil => exact h
  | cons key keys ih => exact ih _ _ (acct_touch_equiv a b h key)

theorem recorder_record_equiv (a b : TTN.Recorder) (h : RecorderEquivalent a b)
    (key : ByteArray) (len : Nat) : RecorderEquivalent (a.record key len) (b.record key len) := by
  obtain ⟨hs, hz⟩ := h
  have he := hs.contains_eq (k := key)
  unfold TTN.Recorder.record
  rw [he]
  split
  · exact ⟨hs, hz⟩
  · exact ⟨hs.insert key (), congrArg (· + len) hz⟩

theorem recorder_record_nodes_equiv (a b : TTN.Recorder) (h : RecorderEquivalent a b)
    (store : TTN.Store) (keys : List ByteArray) :
    RecorderEquivalent (a.recordNodes store keys) (b.recordNodes store keys) := by
  induction keys generalizing a b with
  | nil => exact h
  | cons key keys ih => exact ih _ _ (recorder_record_equiv a b h key _)

/-- Rebuilding cache buckets cannot alter success/failure, gas or charge order. -/
theorem accounting_commit_equiv (gs : Gas) (a b c d : TTN.Acct)
    (hab : AcctEquivalent a b) (hcd : AcctEquivalent c d) :
    TTN.commit gs a c = TTN.commit gs b d := by
  simp only [TTN.commit, hab.2.1, hab.2.2, hcd.2.1, hcd.2.2]

/-- Change only map representation; all committed and accounting fields stay. -/
def normalizeReal (r : TTN.RealStore) : TTN.RealStore :=
  { r with
    overlay := rebuildMap r.overlay
    acct := normalizeAcct r.acct
    recd := normalizeRecorder r.recd }

def OutEquivalent (a b : TTN.Out) : Prop :=
  a.gs = b.gs ∧ AcctEquivalent a.acct b.acct ∧ RecorderEquivalent a.recd b.recd ∧
    a.old = b.old ∧ a.err = b.err

theorem normalized_overlay_lookup (r : TTN.RealStore) (key : ByteArray) :
    (normalizeReal r).overlay.get? key = r.overlay.get? key :=
  (rebuild_map_equiv r.overlay).getElem?_eq

theorem normalized_over_limit (r : TTN.RealStore) :
    TTN.overLimit (normalizeReal r) = TTN.overLimit r := rfl

theorem normalized_deref (r : TTN.RealStore) (key : ByteArray) :
    TTN.deref (normalizeReal r) key = TTN.deref r key := rfl

/-- The actual storage_has_key implementation preserves outputs and recorder
accounting after map reconstruction, on both success and storage errors. -/
theorem normalized_storage_has_key (r : TTN.RealStore) (key : ByteArray) (gs : Gas) :
    OutEquivalent (TTN.storageHasKey (normalizeReal r) key gs)
      (TTN.storageHasKey r key gs) := by
  have ha := normalize_acct_equiv r.acct
  have hr := normalize_recorder_equiv r.recd
  have hn := recorder_record_nodes_equiv _ _ hr r.store
  have he : (rebuildMap r.overlay).get? key = r.overlay.get? key :=
    (rebuild_map_equiv r.overlay).getElem?_eq
  simp only [TTN.storageHasKey, normalizeReal, he]
  cases ho : r.overlay.get? key with
  | some old => simp only; exact ⟨rfl, ha, hr, rfl, rfl⟩
  | none =>
    simp only
    cases hl : TTN.lookup r.store r.root key with
    | error e => simp only; exact ⟨rfl, ha, hr, rfl, rfl⟩
    | ok l => simp only; exact ⟨rfl, ha, hn _, rfl, rfl⟩

/-- Storage-read normalization preserves the actual gas-failure paths as well
as successful reads, including the large-value surcharge and recording order. -/
theorem normalized_storage_read (r : TTN.RealStore) (key : ByteArray) (gs : Gas) :
    OutEquivalent (TTN.storageRead (normalizeReal r) key gs)
      (TTN.storageRead r key gs) := by
  have ha := normalize_acct_equiv r.acct
  have hr := normalize_recorder_equiv r.recd
  have ht := acct_touch_equiv _ _ ha
  have hn := recorder_record_nodes_equiv _ _ hr r.store
  have hv := fun keys k len => recorder_record_equiv _ _ (hn keys) k len
  have he : (rebuildMap r.overlay).get? key = r.overlay.get? key :=
    (rebuild_map_equiv r.overlay).getElem?_eq
  simp only [TTN.storageRead, normalizeReal, he, TTN.deref]
  unfold OutEquivalent
  repeat' (split <;> (try simp_all only []))
  all_goals grind only [OutEquivalent]

/-- Covers both storage_write and storage_remove's External accounting path,
including cached paths and failures before counters are committed. -/
theorem normalized_write_like (cost : Cost) (r : TTN.RealStore) (key : ByteArray) (gs : Gas) :
    OutEquivalent (TTN.writeLike cost (normalizeReal r) key gs)
      (TTN.writeLike cost r key gs) := by
  have ha := normalize_acct_equiv r.acct
  have hr := normalize_recorder_equiv r.recd
  have ht := acct_touch_all_equiv _ _ ha
  have htv := fun keys k => acct_touch_equiv _ _ (ht keys) k
  have hn := recorder_record_nodes_equiv _ _ hr r.store
  have hv := fun keys k len => recorder_record_equiv _ _ (hn keys) k len
  have hc := fun gas keys => accounting_commit_equiv gas _ _ _ _ ha (ht keys)
  have hcv := fun gas keys k => accounting_commit_equiv gas _ _ _ _ ha (htv keys k)
  have he : (rebuildMap r.overlay).get? key = r.overlay.get? key :=
    (rebuild_map_equiv r.overlay).getElem?_eq
  simp only [TTN.writeLike, normalizeReal, he, TTN.deref, hc, hcv]
  unfold OutEquivalent
  repeat' (split <;> (try simp_all only []))
  all_goals grind only [OutEquivalent]

end NearCompression
