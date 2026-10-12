import ZkFormal.NearV3.Assembly.SchedulerSanityJobs
import ZkFormal.NearV3.Assembly.ImplicitTrace
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountWriteRun
import ZkFormal.NearV3.Spec.TrieOps

/-!
# Pinning the scheduler upsert witnesses' sanity inputs to the native trace

`sanOf ctx pre`: the scheduler sanity input of a call with context `ctx` on pre-trie `pre`
(`schedulerWitnessSanity u = sanOf u.ctx u.pre`).  `SanPin k m steps us`: the witnesses `us` have, in
order, the sanity inputs of the main call (`m.ctx k`, `m.pre`) and of every implicit call (its block
context, its pre-trie).  `sized_find_other`: the account replay does not change any other key, so the
rebased main witness (on `oldPost`) has the sanity input of `m.pre` (`sanOf_rebased`).
-/
namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

def sanOf (ctx : ApplyCtx) (pre : PTrie) : Option Bytes :=
  match readKey pre keyBwState "bandwidth scheduler state" with
  | .error _ => none
  | .ok prev => (schedPub ctx).bind fun pub => schedulerSanityInput pub prev

theorem sanity_sanOf (u : SchedulerUpsertWitness) : schedulerWitnessSanity u = sanOf u.ctx u.pre := rfl

/-- The block context of an implicit (missing-chunk) call. -/
def implicitCtx (k : WalkD0) (e : ImplicitStepV3) : ApplyCtx :=
  blockCtx k.L k.H.shardId k.slotB2.gasLimit e.block e.block.hdr.nextGasPrice

def sanList (k : WalkD0) (m : MainExecutionV3) (steps : List ImplicitStepV3) : List (Option Bytes) :=
  sanOf (m.ctx k) m.pre :: steps.map fun e => sanOf (implicitCtx k e) e.pre

def SanPin (k : WalkD0) (m : MainExecutionV3) (steps : List ImplicitStepV3)
    (us : List SchedulerUpsertWitness) : Prop :=
  us.map schedulerWitnessSanity = sanList k m steps

theorem sized_find_other {t out : PTrie} {writes : List (List Nat × Bytes)}
    (h : Rcpt.Candidates.SizedAccountRun t writes out) (key : List Nat)
    (hk : ∀ kv ∈ writes, key ≠ kv.1) : out.find key = t.find key := by
  induction h with
  | nil => rfl
  | cons _ _ _ write _ ih =>
    rw [ih (fun kv hkv => hk kv (List.mem_cons_of_mem _ hkv)),
      ZkFormal.NearV3.PTrie.find_set_ne _ _ _ _ _ write (hk _ List.mem_cons_self)]

theorem sanOf_rebased {ctx : ApplyCtx} {pre oldPost : PTrie} {writes : List (List Nat × Bytes)}
    (h : Rcpt.Candidates.SizedAccountRun pre writes oldPost)
    (hk : ∀ kv ∈ writes, keyBwState ≠ kv.1) : sanOf ctx oldPost = sanOf ctx pre := by
  unfold sanOf readKey
  rw [sized_find_other h keyBwState hk]

end ZkFormal.NearV3.Assembly
