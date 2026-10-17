import NearCompression.StorageCalls

/-! Complete mutating storage calls. All charge, update and failure ordering
is checked by correspondence with the actual hostCall dispatch definition. -/
namespace NearCompression
open NearSpecV3.Wasm

def modifyStorageUsage (f : Nat → Nat) : HM Unit :=
  modify fun s => { s with storageUsage := f s.storageUsage }

theorem host_sim_storage_usage (f : Nat → Nat) :
    HostSim (modifyStorageUsage f) (modifyStorageUsage f) := by
  intro s t hs
  exact ⟨rfl, ⟨congrArg (fun s : St => { s with storageUsage := f s.storageUsage }) hs.core, hs.real⟩⟩

def recordStorageRemoval : HM Unit :=
  modify fun s => { s with real := s.real.map TTN.removeRecord }

theorem host_sim_record_removal : HostSim recordStorageRemoval recordStorageRemoval := by
  intro s t hs
  refine ⟨rfl, ⟨hs.core, ?_⟩⟩
  have hr := hs.real
  change OptionalRealEquivalent (s.real.map TTN.removeRecord) (t.real.map TTN.removeRecord)
  cases ha : s.real <;> cases hb : t.real <;>
    simp only [ha, hb, OptionalRealEquivalent] at hr
  · trivial
  · exact real_equiv_remove_record _ _ hr

def storageRemoveResult (key : ByteArray) (reg : Nat) : Option ByteArray → HM Unit
  | some value => do
    modifyStorageUsage (fun n => n - (value.size + key.size + numExtraBytesRecord))
    storageReadResult reg (some value)
  | none => pushRet 0

theorem host_sim_remove_result (key : ByteArray) (reg : Nat) (value : Option ByteArray) :
    HostSim (storageRemoveResult key reg value) (storageRemoveResult key reg value) := by
  cases value with
  | none => exact host_sim_push_ret 0 true
  | some bytes =>
    unfold storageRemoveResult
    have hout : HostSim (storageReadResult reg (some bytes)) (storageReadResult reg (some bytes)) := by
      with_reducible exact host_sim_read_result reg (some bytes)
    let f := fun n => n - (bytes.size + key.size + numExtraBytesRecord)
    with_reducible exact host_sim_bind (modifyStorageUsage f) (modifyStorageUsage f) (fun _ => storageReadResult reg (some bytes)) (fun _ => storageReadResult reg (some bytes)) (host_sim_storage_usage f) (fun _ => hout)

/-- Setting related states before an arbitrary simulated continuation. -/
theorem host_set_then_equiv {A : Type} (s t u v : St) (hu : StateEquivalent u v)
    (x y : HM A) (h : HostSim x y) :
    HostResultEquivalent ((set u >>= fun _ => x).run s) ((set v >>= fun _ => y).run t) :=
  h u v hu

def storageRemoveFinish (key : ByteArray) (reg : Nat) : HM Unit := do
  let s ← get
  match s.real with
  | some r =>
    let v ← realOpH r TTN.storageRemove key
    realSetH r key none
    recordStorageRemoval
    observeH
    storageRemoveResult key reg v
  | none =>
    match trieGet s key with
    | some v =>
      set { s with trie := s.trie.filter (·.1 != key),
                   storageUsage := s.storageUsage - (v.size + key.size + numExtraBytesRecord) }
      storageReadResult reg (some v)
    | none => pushRet 0

theorem host_sim_remove_finish (key : ByteArray) (reg : Nat) :
    HostSim (storageRemoveFinish key reg) (storageRemoveFinish key reg) := by
  intro s t hs
  unfold storageRemoveFinish
  rw [host_get_bind_run, host_get_bind_run]
  have hr := hs.real
  cases ha : s.real <;> cases hb : t.real <;>
    simp only [ha, hb, OptionalRealEquivalent] at hr
  · have he : trieGet s key = trieGet t key := by
      have hh := congrArg (fun s => trieGet s key) hs.core
      exact hh
    simp only
    rw [he]
    split
    · rename_i value found
      have hset : StateEquivalent
          { s with trie := s.trie.filter (·.1 != key), storageUsage := s.storageUsage - (value.size + key.size + numExtraBytesRecord) }
          { t with trie := t.trie.filter (·.1 != key), storageUsage := t.storageUsage - (value.size + key.size + numExtraBytesRecord) } := by
        constructor
        · exact congrArg (fun s : St => { s with
            trie := s.trie.filter (·.1 != key)
            storageUsage := s.storageUsage - (value.size + key.size + numExtraBytesRecord) }) hs.core
        · exact hs.real
      have hh : HostSim (storageReadResult reg (some value)) (storageReadResult reg (some value)) := by
        with_reducible exact host_sim_read_result reg (some value)
      simp only [ha, hb] at hset
      with_reducible exact host_set_then_equiv s t _ _ hset (storageReadResult reg (some value)) (storageReadResult reg (some value)) hh
    · exact host_sim_push_ret 0 true s t hs
  · rename_i a b
    simp only
    apply host_bind_equiv
    · exact storage_write_host_equiv s t hs a b hr key C.storageRemoveRetValueByte
    · intro value u v huv
      apply host_bind_equiv
      · exact real_set_host_equiv u v huv a b hr.pfx key none
      · intro _ u' v' hs'
        apply host_bind_equiv
        · exact host_sim_record_removal u' v' hs'
        · intro _ u'' v'' hs''
          apply host_bind_equiv
          · exact observe_host_equiv u'' v'' hs''
          · intro _ u''' v''' hs'''
            have hh : HostSim (storageRemoveResult key reg value) (storageRemoveResult key reg value) := by
              with_reducible exact host_sim_remove_result key reg value
            unfold HostSim at hh
            with_reducible exact hh u''' v''' hs'''

def storageRemoveCode (base removeBase keyByte : Cost) : HM Unit := do
  let a ← popArgs 3
  payBaseH base
  payBaseH removeBase
  let k ← memOrRegH a[1] a[0]
  if k.size > maxLengthStorageKey then
    hErr s!"KeyLengthExceeded \{ length: {k.size}, limit: {maxLengthStorageKey} }"
  payPerH keyByte k.size
  storageRemoveFinish k a[2]

theorem host_sim_remove_code (base removeBase keyByte : Cost) :
    HostSim (storageRemoveCode base removeBase keyByte) (storageRemoveCode base removeBase keyByte) := by
  unfold storageRemoveCode
  with_reducible apply host_sim_bind
  · with_reducible exact host_sim_pop_args 3
  intro args
  with_reducible apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  with_reducible apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  with_reducible apply host_sim_bind
  · with_reducible exact host_sim_mem_or_reg _ _
  intro key
  dsimp only
  split
  · with_reducible apply host_sim_bind
    · exact host_sim_error _
    intro _
    with_reducible apply host_sim_bind
    · unfold payPerH
      exact host_sim_with_gas _
    intro _
    exact host_sim_remove_finish key args[2]
  · with_reducible apply host_sim_bind
    · unfold payPerH
      exact host_sim_with_gas _
    intro _
    exact host_sim_remove_finish key args[2]

theorem actual_storage_remove_code : hostCall "storage_remove" =
    some (storageRemoveCode C.base C.storageRemoveBase C.storageRemoveKeyByte) := by rfl

theorem actual_storage_remove_sim (call : HM Unit)
    (hcall : hostCall "storage_remove" = some call) : HostSim call call := by
  rw [actual_storage_remove_code] at hcall
  cases Option.some.inj hcall
  with_reducible exact host_sim_remove_code C.base C.storageRemoveBase C.storageRemoveKeyByte

def storageWriteResult (key value : ByteArray) (reg : Nat) : Option ByteArray → HM Unit
  | some old => do
    modifyStorageUsage (fun n => n - old.size + value.size)
    storageReadResult reg (some old)
  | none => do
    modifyStorageUsage (fun n => n + value.size + key.size + numExtraBytesRecord)
    pushRet 0

theorem host_sim_write_result (key value : ByteArray) (reg : Nat) (old : Option ByteArray) :
    HostSim (storageWriteResult key value reg old) (storageWriteResult key value reg old) := by
  cases old with
  | none =>
    unfold storageWriteResult
    with_reducible apply host_sim_bind
    · exact host_sim_storage_usage _
    intro _
    exact host_sim_push_ret 0 true
  | some old =>
    unfold storageWriteResult
    have hout : HostSim (storageReadResult reg (some old)) (storageReadResult reg (some old)) := by
      with_reducible exact host_sim_read_result reg (some old)
    let f := fun n => n - old.size + value.size
    with_reducible exact host_sim_bind (modifyStorageUsage f) (modifyStorageUsage f) (fun _ => storageReadResult reg (some old)) (fun _ => storageReadResult reg (some old)) (host_sim_storage_usage f) (fun _ => hout)

/-- Store update and old-value result, before storage-usage/register changes. -/
def storageWriteExternal (s : St) (key value : ByteArray) : HM (Option ByteArray) := do
  match s.real with
  | some r =>
    let old ← realOpH r TTN.storageWrite key
    realSetH r key (some value)
    observeH
    pure old
  | none =>
    let old := trieGet s key
    let trie := match s.trie.findIdx? (·.1 == key) with
      | some i => s.trie.set! i (key, value)
      | none => s.trie.push (key, value)
    set { s with trie }
    pure old

theorem storage_write_external_equiv (s t : St) (hs : StateEquivalent s t) (key value : ByteArray) :
    HostResultEquivalent ((storageWriteExternal s key value).run s)
      ((storageWriteExternal t key value).run t) := by
  have hr := hs.real
  have ht : s.trie = t.trie := by
    have hh := congrArg St.trie hs.core
    exact hh
  have hv : trieGet s key = trieGet t key := by
    have hh := congrArg (fun s => trieGet s key) hs.core
    exact hh
  unfold storageWriteExternal
  cases ha : s.real <;> cases hb : t.real <;>
    simp only [ha, hb, OptionalRealEquivalent] at hr
  · simp only [ht, hv]
    split
    · rename_i i found
      exact ⟨rfl, ⟨congrArg (fun s : St => { s with trie := t.trie.set! i (key, value) }) hs.core, trivial⟩⟩
    · exact ⟨rfl, ⟨congrArg (fun s : St => { s with trie := t.trie.push (key, value) }) hs.core, trivial⟩⟩
  · rename_i a b
    simp only
    apply host_bind_equiv
    · exact storage_write_host_equiv s t hs a b hr key C.storageWriteEvictedByte
    · intro old u v huv
      apply host_bind_equiv
      · exact real_set_host_equiv u v huv a b hr.pfx key (some value)
      · intro _ u' v' hs'
        apply host_bind_equiv
        · exact observe_host_equiv u' v' hs'
        · intro _ u'' v'' hs''
          exact ⟨rfl, hs''⟩

def storageWriteFinish (key value : ByteArray) (reg : Nat) : HM Unit := do
  let s ← get
  match s.real with
  | some r =>
    let old ← realOpH r TTN.storageWrite key
    realSetH r key (some value)
    observeH
    let old ← pure old
    storageWriteResult key value reg old
  | none =>
    let old := trieGet s key
    let trie := match s.trie.findIdx? (·.1 == key) with
      | some i => s.trie.set! i (key, value)
      | none => s.trie.push (key, value)
    set { s with trie }
    let old ← pure old
    storageWriteResult key value reg old

theorem host_sim_write_finish (key value : ByteArray) (reg : Nat) :
    HostSim (storageWriteFinish key value reg) (storageWriteFinish key value reg) := by
  intro s t hs
  unfold storageWriteFinish
  rw [host_get_bind_run, host_get_bind_run]
  have hr := hs.real
  have ht : s.trie = t.trie := by
    have hh := congrArg St.trie hs.core
    exact hh
  have hv : trieGet s key = trieGet t key := by
    have hh := congrArg (fun s => trieGet s key) hs.core
    exact hh
  cases ha : s.real <;> cases hb : t.real <;>
    simp only [ha, hb, OptionalRealEquivalent] at hr
  · simp only [ht, hv, pure_bind]
    let updated := match t.trie.findIdx? (·.1 == key) with
      | some i => t.trie.set! i (key, value)
      | none => t.trie.push (key, value)
    have hset : StateEquivalent { s with trie := updated, real := none }
        { t with trie := updated, real := none } :=
      ⟨congrArg (fun s : St => { s with trie := updated }) hs.core, trivial⟩
    have hh : HostSim (storageWriteResult key value reg (trieGet t key))
        (storageWriteResult key value reg (trieGet t key)) := by
      with_reducible exact host_sim_write_result key value reg (trieGet t key)
    with_reducible exact host_set_then_equiv s t _ _ hset (storageWriteResult key value reg (trieGet t key)) (storageWriteResult key value reg (trieGet t key)) hh
  · rename_i a b
    simp only [pure_bind]
    apply host_bind_equiv
    · exact storage_write_host_equiv s t hs a b hr key C.storageWriteEvictedByte
    · intro old u v huv
      apply host_bind_equiv
      · exact real_set_host_equiv u v huv a b hr.pfx key (some value)
      · intro _ u' v' hs'
        apply host_bind_equiv
        · exact observe_host_equiv u' v' hs'
        · intro _ u'' v'' hs''
          have hh : HostSim (storageWriteResult key value reg old) (storageWriteResult key value reg old) := by
            with_reducible exact host_sim_write_result key value reg old
          unfold HostSim at hh
          with_reducible exact hh u'' v'' hs''

def storageWriteChargedFinish (keyByte valueByte : Cost) (key value : ByteArray) (reg : Nat) : HM Unit := do
  payPerH keyByte key.size
  payPerH valueByte value.size
  storageWriteFinish key value reg

theorem host_sim_write_charged_finish (keyByte valueByte : Cost) (key value : ByteArray) (reg : Nat) :
    HostSim (storageWriteChargedFinish keyByte valueByte key value reg)
      (storageWriteChargedFinish keyByte valueByte key value reg) := by
  unfold storageWriteChargedFinish
  with_reducible apply host_sim_bind
  · unfold payPerH
    exact host_sim_with_gas _
  intro _
  with_reducible apply host_sim_bind
  · unfold payPerH
    exact host_sim_with_gas _
  intro _
  exact host_sim_write_finish key value reg

def storageWriteValueCode (keyByte valueByte : Cost) (key : ByteArray) (args : Vector Nat 5) : HM Unit := do
  let value ← memOrRegH args[3] args[2]
  if value.size > maxLengthStorageValue then
    hErr s!"ValueLengthExceeded \{ length: {value.size}, limit: {maxLengthStorageValue} }"
  storageWriteChargedFinish keyByte valueByte key value args[4]

theorem host_sim_write_value_code (keyByte valueByte : Cost) (key : ByteArray) (args : Vector Nat 5) :
    HostSim (storageWriteValueCode keyByte valueByte key args) (storageWriteValueCode keyByte valueByte key args) := by
  unfold storageWriteValueCode
  with_reducible apply host_sim_bind
  · with_reducible exact host_sim_mem_or_reg _ _
  intro value
  dsimp only
  split
  · with_reducible apply host_sim_bind
    · exact host_sim_error _
    intro _
    exact host_sim_write_charged_finish keyByte valueByte key value args[4]
  · exact host_sim_write_charged_finish keyByte valueByte key value args[4]

def storageWriteCode (base writeBase keyByte valueByte : Cost) : HM Unit := do
  let args ← popArgs 5
  payBaseH base
  payBaseH writeBase
  let key ← memOrRegH args[1] args[0]
  if key.size > maxLengthStorageKey then
    hErr s!"KeyLengthExceeded \{ length: {key.size}, limit: {maxLengthStorageKey} }"
  storageWriteValueCode keyByte valueByte key args

theorem host_sim_write_code (base writeBase keyByte valueByte : Cost) :
    HostSim (storageWriteCode base writeBase keyByte valueByte) (storageWriteCode base writeBase keyByte valueByte) := by
  unfold storageWriteCode
  with_reducible apply host_sim_bind
  · with_reducible exact host_sim_pop_args 5
  intro args
  with_reducible apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  with_reducible apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  with_reducible apply host_sim_bind
  · with_reducible exact host_sim_mem_or_reg _ _
  intro key
  dsimp only
  split
  · with_reducible apply host_sim_bind
    · exact host_sim_error _
    intro _
    exact host_sim_write_value_code keyByte valueByte key args
  · exact host_sim_write_value_code keyByte valueByte key args

theorem actual_storage_write_code : hostCall "storage_write" =
    some (storageWriteCode C.base C.storageWriteBase C.storageWriteKeyByte C.storageWriteValueByte) := by rfl


theorem actual_storage_write_sim (call : HM Unit)
    (hcall : hostCall "storage_write" = some call) : HostSim call call := by
  rw [actual_storage_write_code] at hcall
  cases Option.some.inj hcall
  with_reducible exact host_sim_write_code C.base C.storageWriteBase C.storageWriteKeyByte C.storageWriteValueByte

end NearCompression
