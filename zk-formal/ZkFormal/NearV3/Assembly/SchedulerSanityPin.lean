import ZkFormal.NearV3.Assembly.SchedulerSanityJobs
import ZkFormal.NearV3.Assembly.ImplicitTrace
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountWriteRun
import ZkFormal.NearV3.Spec.TrieOps

/-!
# Pinning the scheduler upsert witnesses to the native trace's scheduler calls

`CallPin k m steps us`: the witnesses `us` are, in order, the native trace's scheduler calls —
(context, state read) of the main call (`m.ctx k`, `m.pre`) and of every implicit call (its block
context, its pre-trie).  Sanity inputs (`sanF`, `CallPin.sanity`) and new state values (`valF`,
`CallPin.values`) are functions of the call.  `sized_find_other`: the account replay does not change any
other key, so the rebased main witness (on `oldPost`) reads the state of `m.pre` (`schedRead_rebased`).
-/
namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

/-- The scheduler's read of its state. -/
def schedRead (pre : PTrie) : Except String (Option Bytes) := readKey pre keyBwState "bandwidth scheduler state"

/-- The sanity input of a call, from its context and state read. -/
def sanF (q : ApplyCtx × Except String (Option Bytes)) : Option Bytes :=
  match q.2 with
  | .error _ => none
  | .ok prev => (schedPub q.1).bind fun pub => schedulerSanityInput pub prev

def sanOf (ctx : ApplyCtx) (pre : PTrie) : Option Bytes := sanF (ctx, schedRead pre)

theorem sanity_sanOf (u : SchedulerUpsertWitness) : schedulerWitnessSanity u = sanOf u.ctx u.pre := rfl

/-- The new state value of a call, from its context and state read. -/
def valF (q : ApplyCtx × Except String (Option Bytes)) : Option Bytes :=
  match q.2 with
  | .error _ => none
  | .ok prev => (schedPub q.1).bind fun pub => (Scheduler.runCore pub prev).map fun o => (schedOut o).state

theorem value_valF {u : SchedulerUpsertWitness} (hv : u.Valid) : valF (u.ctx, schedRead u.pre) = some u.value := by
  obtain ⟨so, hs, hval⟩ := hv.2
  obtain ⟨prev, p, o, hr, hp, hc, ho, -⟩ := schedStep_complete hs
  simp only [valF, schedRead, hr, hp, hc, Option.bind_some, Option.map_some, ho, hval]

/-- The block context of an implicit (missing-chunk) call. -/
def implicitCtx (k : WalkD0) (e : ImplicitStepV3) : ApplyCtx :=
  blockCtx k.L k.H.shardId k.slotB2.gasLimit e.block e.block.hdr.nextGasPrice

/-- The scheduler calls of the native trace: (context, state read), main then implicit. -/
def callList (k : WalkD0) (m : MainExecutionV3) (steps : List ImplicitStepV3) :
    List (ApplyCtx × Except String (Option Bytes)) :=
  (m.ctx k, schedRead m.pre) :: steps.map fun e => (implicitCtx k e, schedRead e.pre)

/-- The witnesses `us` are, in order, the native trace's scheduler calls. -/
def CallPin (k : WalkD0) (m : MainExecutionV3) (steps : List ImplicitStepV3)
    (us : List SchedulerUpsertWitness) : Prop :=
  us.map (fun u => (u.ctx, schedRead u.pre)) = callList k m steps

theorem CallPin.sanity {k : WalkD0} {m : MainExecutionV3} {steps : List ImplicitStepV3}
    {us : List SchedulerUpsertWitness} (h : CallPin k m steps us) :
    us.map schedulerWitnessSanity = (callList k m steps).map sanF := by
  rw [← h, List.map_map]; rfl

theorem CallPin.values {k : WalkD0} {m : MainExecutionV3} {steps : List ImplicitStepV3}
    {us : List SchedulerUpsertWitness} (h : CallPin k m steps us) (hv : ∀ u ∈ us, u.Valid) :
    us.map (fun u => some u.value) = (callList k m steps).map valF := by
  rw [← h, List.map_map]
  apply List.map_congr_left
  intro u hu
  exact (value_valF (hv u hu)).symm

theorem sized_find_other {t out : PTrie} {writes : List (List Nat × Bytes)}
    (h : Rcpt.Candidates.SizedAccountRun t writes out) (key : List Nat)
    (hk : ∀ kv ∈ writes, key ≠ kv.1) : out.find key = t.find key := by
  induction h with
  | nil => rfl
  | cons _ _ _ write _ ih =>
    rw [ih (fun kv hkv => hk kv (List.mem_cons_of_mem _ hkv)),
      ZkFormal.NearV3.PTrie.find_set_ne _ _ _ _ _ write (hk _ List.mem_cons_self)]

theorem schedRead_rebased {pre oldPost : PTrie} {writes : List (List Nat × Bytes)}
    (h : Rcpt.Candidates.SizedAccountRun pre writes oldPost)
    (hk : ∀ kv ∈ writes, keyBwState ≠ kv.1) : schedRead oldPost = schedRead pre := by
  unfold schedRead readKey
  rw [sized_find_other h keyBwState hk]

end ZkFormal.NearV3.Assembly
