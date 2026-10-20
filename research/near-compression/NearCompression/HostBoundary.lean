import NearCompression.MapBoundary

/-! Host-state installation for observational map serialization. All non-map
fields remain exact, and errors retain the state reached by the real host code.
This is not yet a whole-machine simulation. -/
namespace NearCompression
open NearSpecV3.Wasm

local instance : LawfulBEq ByteArray where
  eq_of_beq := byte_array_beq_eq _ _
  rfl := by intro a; change (a.data == a.data) = true; exact BEq.rfl

structure RealEquivalent (a b : TTN.RealStore) : Prop where
  store : a.store = b.store
  root : a.root = b.root
  overlay : a.overlay.Equiv b.overlay
  acct : AcctEquivalent a.acct b.acct
  pfx : a.pfx = b.pfx
  recd : RecorderEquivalent a.recd b.recd
  recBefore : a.recBefore = b.recBefore
  writes : a.writes = b.writes

def OptionalRealEquivalent : Option TTN.RealStore → Option TTN.RealStore → Prop
  | none, none => True
  | some a, some b => RealEquivalent a b
  | _, _ => False

structure StateEquivalent (s t : St) : Prop where
  core : { s with real := none } = { t with real := none }
  real : OptionalRealEquivalent s.real t.real

/-- Return values/errors and termination status stay exact. -/
def HostResultEquivalent {A : Type} : EStateM.Result String St A → EStateM.Result String St A → Prop
  | .ok a s, .ok b t => a = b ∧ StateEquivalent s t
  | .error a s, .error b t => a = b ∧ StateEquivalent s t
  | _, _ => False

theorem normalized_real_equiv (r : TTN.RealStore) : RealEquivalent (normalizeReal r) r :=
  ⟨rfl, rfl, rebuild_map_equiv _, normalize_acct_equiv _, rfl,
    normalize_recorder_equiv _, rfl, rfl⟩

theorem state_equiv_gas (s t : St) (h : StateEquivalent s t) : s.gas = t.gas := by
  have hg := congrArg St.gas h.core
  exact hg

theorem real_equiv_install (a b : TTN.RealStore) (h : RealEquivalent a b)
    (x y : TTN.Out) (ho : OutEquivalent x y) :
    RealEquivalent { a with acct := x.acct, recd := x.recd }
      { b with acct := y.acct, recd := y.recd } :=
  ⟨h.store, h.root, h.overlay, ho.2.1, h.pfx, ho.2.2.1, h.recBefore, h.writes⟩

theorem state_equiv_install (s t : St) (h : StateEquivalent s t)
    (a b : TTN.RealStore) (hr : RealEquivalent a b) (gas : Gas) :
    StateEquivalent { s with gas, real := some a } { t with gas, real := some b } := by
  constructor
  · exact congrArg (fun s : St => { s with gas }) h.core
  · exact hr

/-- Definitional execution of the production-spec helper, including updated
state on errors. This avoids a separate, possibly inaccurate host model. -/
theorem real_op_host_run (r : TTN.RealStore)
    (f : TTN.RealStore → ByteArray → Gas → TTN.Out) (key : ByteArray) (s : St) :
    (realOpH r f key).run s =
      let o := f r (r.pfx ++ key) s.gas
      let t := { s with gas := o.gs, real := some { r with acct := o.acct, recd := o.recd } }
      match o.err with
      | some e => .error e t
      | none => .ok o.old t := by
  let o := f r (r.pfx ++ key) s.gas
  let t := { s with gas := o.gs, real := some { r with acct := o.acct, recd := o.recd } }
  change (match o.err with
    | some e => EStateM.throw e
    | none => EStateM.pure o.old) t =
    (match o.err with | some e => .error e t | none => .ok o.old t)
  cases o.err <;> rfl

/-- Any related External outputs install related continuation states. The
premise must be established for the chosen actual storage operation. -/
theorem real_op_host_equiv (s t : St) (hs : StateEquivalent s t)
    (a b : TTN.RealStore) (hr : RealEquivalent a b)
    (f : TTN.RealStore → ByteArray → Gas → TTN.Out) (key : ByteArray)
    (ho : OutEquivalent (f a (a.pfx ++ key) s.gas) (f b (b.pfx ++ key) t.gas)) :
    HostResultEquivalent ((realOpH a f key).run s) ((realOpH b f key).run t) := by
  rw [real_op_host_run, real_op_host_run]
  dsimp only
  have hi := state_equiv_install s t hs _ _ (real_equiv_install a b hr _ _ ho)
    (f b (b.pfx ++ key) t.gas).gs
  rw [ho.1, ho.2.2.2.2]
  cases (f b (b.pfx ++ key) t.gas).err with
  | none => exact ⟨ho.2.2.2.1, hi⟩
  | some e => exact ⟨rfl, hi⟩

/-- Instantiation for actual storage_read after map reconstruction. -/
theorem normalized_read_host (s t : St) (hs : StateEquivalent s t)
    (r : TTN.RealStore) (key : ByteArray) :
    HostResultEquivalent ((realOpH (normalizeReal r) TTN.storageRead key).run s)
      ((realOpH r TTN.storageRead key).run t) := by
  apply real_op_host_equiv s t hs _ _ (normalized_real_equiv r)
  rw [state_equiv_gas s t hs]
  exact normalized_storage_read r (r.pfx ++ key) t.gas

theorem normalized_write_host (s t : St) (hs : StateEquivalent s t)
    (r : TTN.RealStore) (key : ByteArray) (cost : Cost) :
    HostResultEquivalent ((realOpH (normalizeReal r) (TTN.writeLike cost) key).run s)
      ((realOpH r (TTN.writeLike cost) key).run t) := by
  apply real_op_host_equiv s t hs _ _ (normalized_real_equiv r)
  rw [state_equiv_gas s t hs]
  exact normalized_write_like cost r (r.pfx ++ key) t.gas

theorem normalized_has_key_host (s t : St) (hs : StateEquivalent s t)
    (r : TTN.RealStore) (key : ByteArray) :
    HostResultEquivalent ((realOpH (normalizeReal r) TTN.storageHasKey key).run s)
      ((realOpH r TTN.storageHasKey key).run t) := by
  apply real_op_host_equiv s t hs _ _ (normalized_real_equiv r)
  rw [state_equiv_gas s t hs]
  exact normalized_storage_has_key r (r.pfx ++ key) t.gas

theorem real_equiv_overlay_insert (a b : TTN.RealStore) (h : RealEquivalent a b)
    (key : ByteArray) (value : Option ByteArray) :
    RealEquivalent
      { a with overlay := a.overlay.insert key value, writes := a.writes.push (key, value) }
      { b with overlay := b.overlay.insert key value, writes := b.writes.push (key, value) } :=
  ⟨h.store, h.root, h.overlay.insert key value, h.acct, h.pfx, h.recd,
    h.recBefore, congrArg (fun xs => xs.push (key, value)) h.writes⟩

/-- Actual host overlay writes preserve the ordered write log as well as
logical map entries. This covers deletion markers (value = none). -/
theorem real_put_host_equiv (s t : St) (hs : StateEquivalent s t)
    (key : ByteArray) (value : Option ByteArray) :
    HostResultEquivalent ((realPutH key value).run s) ((realPutH key value).run t) := by
  let update := fun s : St => match s.real with
    | some r => { s with real := some { r with
        overlay := r.overlay.insert key value
        writes := r.writes.push (key, value) } }
    | none => s
  change () = () ∧ StateEquivalent (update s) (update t)
  refine ⟨rfl, ?_⟩
  have hr := hs.real
  cases ha : s.real <;> cases hb : t.real <;>
    simp only [ha, hb, OptionalRealEquivalent] at hr
  · simpa only [update, ha, hb] using hs
  · simp only [update, ha, hb]
    constructor
    · exact hs.core
    · exact real_equiv_overlay_insert _ _ hr key value

/-- Sequential host composition preserves errors and the state reached before
an error; a continuation is invoked only on successful results. -/
theorem host_bind_equiv {A B : Type} (x y : HM A) (f g : A → HM B)
    (s t : St) (h : HostResultEquivalent (x.run s) (y.run t))
    (next : ∀ a u v, StateEquivalent u v →
      HostResultEquivalent ((f a).run u) ((g a).run v)) :
    HostResultEquivalent ((x >>= f).run s) ((y >>= g).run t) := by
  rw [NearSpecV3.Logged.W.HM_run_bind, NearSpecV3.Logged.W.HM_run_bind]
  cases hx : x.run s <;> cases hy : y.run t <;>
    simp only [hx, hy, HostResultEquivalent] at h
  · obtain ⟨rfl, hs⟩ := h
    exact next _ _ _ hs
  · exact h

def normalizeStateMaps (s : St) : St := { s with real := s.real.map normalizeReal }

theorem normalized_state_equiv (s : St) : StateEquivalent (normalizeStateMaps s) s := by
  constructor
  · rfl
  · change OptionalRealEquivalent (s.real.map normalizeReal) s.real
    cases s.real with
    | none => trivial
    | some r => exact normalized_real_equiv r

/-- Prefix-qualified writes are the same realPutH operation on a full key. -/
theorem real_set_host_equiv (s t : St) (hs : StateEquivalent s t)
    (a b : TTN.RealStore) (hp : a.pfx = b.pfx) (key : ByteArray) (value : Option ByteArray) :
    HostResultEquivalent ((realSetH a key value).run s) ((realSetH b key value).run t) := by
  change HostResultEquivalent ((realPutH (a.pfx ++ key) value).run s)
    ((realPutH (b.pfx ++ key) value).run t)
  rw [hp]
  exact real_put_host_equiv s t hs _ value

/-- End-to-end host-helper specialization with concrete normalized input;
no state-equivalence premise is left for the caller to establish. -/
theorem normalized_read_host_from_state (s : St) (r : TTN.RealStore) (key : ByteArray) :
    HostResultEquivalent
      ((realOpH (normalizeReal r) TTN.storageRead key).run (normalizeStateMaps s))
      ((realOpH r TTN.storageRead key).run s) :=
  normalized_read_host _ _ (normalized_state_equiv s) r key

end NearCompression
