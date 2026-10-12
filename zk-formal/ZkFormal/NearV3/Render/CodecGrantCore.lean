import ZkFormal.NearV3.Assembly.SchedulerPriorCore
import ZkFormal.NearV3.Candidates.ProcNativeMainCodecWitness
import ZkFormal.NearV3.Candidates.ProcNativeNonmainCodecLocal
import ZkFormal.NearV3.Assembly.SchedulerSanityPin

/-!
# `PriorCore` with the per-block distribution witness

The block constructors behind `accepted_prior_core` choose the grant array `gd` of each
`NativeBlock` from the native process prefix and `distributeEv`, but the exported statements forget
that link.  `GrantWit b` records it; `accepted_prior_core_grants` re-runs the same construction
(same native witnesses, existing statements untouched) and exports `PriorCore p B bs ∧ ∀ b ∈ bs,
GrantWit b`.
-/
namespace ZkFormal.NearV3.Render.CdcGrant
open NearSpec NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Candidates ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.CodecDigest
open Render.UpsGen Rcpt.Candidates.NodePostUpdate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- The block's grants are the native distribution of its own process prefix. -/
def GrantWit (b : NativeBlock) : Prop :=
  ∃ cv st rs ev sord rord,
    ProcActualPrefix.runPrefix (ProcPreparedSequence.input b.pub b.old) = .ok (cv, st, rs, ev) ∧
    distributeEv b.pub.ids.length b.pub.allowed st.sb st.rb
      (linkPass b.pub.ids.length b.pub.params b.pub.allowed
        (ProcActualInput.allowances b.pub.ids b.old)).cntS
      (linkPass b.pub.ids.length b.pub.params b.pub.allowed
        (ProcActualInput.allowances b.pub.ids b.old)).cntR = .ok (b.grants, sord, rord)

theorem main_block {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (ctx : ApplyCtx) (sp : SchedPub)
    (hsp : sp∈p.sched) (hpub : schedPub ctx=some sp)
    (pre : PTrie) (receipts : List Receipt) (out : MainOut)
    (hchunk : applyNewChunk prims ctx pre receipts=.ok out) (vid : Nat) :
    ∃ b : NativeBlock,
      schedulerUpsertWitness ctx pre=.ok b.witness ∧
      b.witness.pre=pre ∧ b.witness.ctx=ctx ∧ b.pub=sp ∧ b.vid=vid ∧
      b.forwarded=fwdLinks ctx out.outgoing ∧ b.Valid ∧
      ActualRun.run (ProcPreparedSequence.input b.pub b.old) 0=.ok b.run ∧
      b.run.tau=0 ∧ b.run.n≤64 ∧
      (∀ (time : Nat) (pub : List Fp), TableLocal ProcPriorCodecActual.table
        (SchedHeight.trace b.output.rows codecPad) time pub) ∧ GrantWit b := by
  obtain ⟨old,prev,cv,st,rs,ev,R,gd,sord,rord,result,hread,hdecode,hprefix,hr,hgd,hgen⟩ :=
    ProcNativeMainCodecWitness.native_main hp ctx sp hsp hpub pre receipts out hchunk vid
  have hs := prepD0_sched hp sp hsp
  have ha := (ProcActualPublic.schedPub_fields ctx sp hpub).1
  have hfields := ProcActualRunProjection.run_fields (ProcPreparedSequence.input sp prev) 0 R hr
  have ht : R.tau<ZkFormal.Algebra.P := by rw [hfields.1]; decide +kernel
  obtain ⟨_,_,_,hsched,_,_⟩ := Qv.applyNewChunk_queue_reads hchunk
  obtain ⟨u,hu,hpre,hvalid⟩ := schedStep_upsert_witness hsched
  have hctx := schedulerUpsertWitness_ctx hu
  have hn : R.n≤64 := by
    rw [hfields.2.1]
    exact hs.n64
  let b : NativeBlock := ⟨u,sp,old,prev,R,vid,gd,fwdLinks ctx out.outgoing,result⟩
  have hb : b.Valid := by
    refine ⟨hvalid,?_,?_,hdecode,hgen⟩
    · change readKey u.pre keyBwState _=.ok old
      rw [hpre]; exact hread
    · change schedPub u.ctx=some sp
      rw [hctx]; exact hpub
  exact ⟨b,hu,hpre,hctx,rfl,rfl,rfl,hb,hr,hfields.1,hn,
    fun time pub => ProcCodecNativeLocal.table sp hs ha prev 0 cv rs st ev R gd sord rord hprefix hr hgd
      old.isSome vid (fwdLinks ctx out.outgoing) result hgen ht time pub,
    cv,st,rs,ev,sord,rord,hprefix,hgd⟩

theorem missing_block {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (sp : SchedPub) (tau : Nat)
    (hindex : p.sched[tau]?=some sp) (ht : tau≠0)
    (ctx : ApplyCtx) (hpub : schedPub ctx=some sp)
    (pre post : PTrie) (hchunk : applyMissingChunk prims ctx pre=.ok post) (vid : Nat) :
    ∃ b : NativeBlock,
      schedulerUpsertWitness ctx pre=.ok b.witness ∧
      b.witness.pre=pre ∧ b.witness.ctx=ctx ∧ b.pub=sp ∧ b.vid=vid ∧
      b.forwarded=[] ∧ b.Valid ∧
      ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau=.ok b.run ∧
      b.run.tau=tau ∧ b.run.n≤64 ∧
      (∀ (time : Nat) (pub : List Fp), TableLocal ProcPriorCodecActual.table
        (SchedHeight.trace b.output.rows codecPad) time pub) ∧ GrantWit b := by
  have hh := hchunk
  unfold applyMissingChunk at hh
  obtain ⟨_,_,hh⟩ := ReexecV3D0.bind_ok' hh
  obtain ⟨⟨mid,so⟩,hsched,_⟩ := ReexecV3D0.bind_ok' hh
  obtain ⟨old,sp',nativeOut,hread,hpub',hcore,_,_⟩ := schedStep_complete hsched
  have he := Option.some.inj (hpub'.symm.trans hpub)
  subst sp'
  obtain ⟨prev,cv,st,rs,ev,R,gd,sord,rord,result,hdecode,hprefix,hr,hgd,hgen,hlocal⟩ :=
    ProcNativeNonmainCodecLocal.native_nonmain hp sp tau hindex ht ctx hpub old nativeOut hcore vid []
  obtain ⟨u,hu,hpre,hvalid⟩ := schedStep_upsert_witness hsched
  have hctx := schedulerUpsertWitness_ctx hu
  have hfields := ProcActualRunProjection.run_fields (ProcPreparedSequence.input sp prev) tau R hr
  have hn : R.n≤64 := by
    rw [hfields.2.1]
    exact (prepD0_sched hp sp (List.mem_iff_getElem?.mpr ⟨tau,hindex⟩)).n64
  let b : NativeBlock := ⟨u,sp,old,prev,R,vid,gd,[],result⟩
  have hb : b.Valid := by
    refine ⟨hvalid,?_,?_,hdecode,hgen⟩
    · change readKey u.pre keyBwState _=.ok old
      rw [hpre]; exact hread
    · change schedPub u.ctx=some sp
      rw [hctx]; exact hpub
  exact ⟨b,hu,hpre,hctx,rfl,rfl,rfl,hb,hr,hfields.1,hn,hlocal,cv,st,rs,ev,sord,rord,hprefix,hgd⟩

theorem implicit_blocks {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) {k : WalkD0} {root : Bytes}
    {pairs : List (Blk×Transition)} {steps : List ImplicitStepV3} {last : Bytes}
    (hv : ImplicitTraceValid k root pairs steps last) (tau : Nat) (ht : 0<tau)
    (vids : Nat→Nat)
    (hi : ∀i e,steps[i]?=some e→∃sp,p.sched[tau+i]?=some sp ∧ schedPub (implicitContext k e)=some sp) :
    ∃bs : List NativeBlock,bs.length=steps.length ∧
      ∀i e b,steps[i]?=some e→bs[i]?=some b→MissingBlockAt k vids (tau+i) e b ∧
        PreparedRun p (tau+i) b ∧ GrantWit b := by
  induction hv generalizing tau with
  | nil => exact ⟨[],rfl,by intro i e b he; simp at he⟩
  | cons root block witness rest steps post last hrun hpost htail ih =>
    let e : ImplicitStepV3 := ⟨block,witness,root,partialTrie witness.values root [keyDelayedIdx,keyBwState],post⟩
    obtain ⟨sp,hindex,hpub⟩ := hi 0 e rfl
    simp only [Nat.add_zero] at hindex
    obtain ⟨b,hb,hpre,hctx,hsp,hvid,hf,hvalid,hr,htau,hn,hlocal,hg⟩ :=
      missing_block hp sp tau hindex (by omega) (implicitContext k e) hpub e.pre post hrun (vids tau)
    obtain ⟨bs,hlen,hbs⟩ := ih (tau+1) (by omega) (by
      intro i x hx
      obtain ⟨sp,hs,hc⟩ := hi (i+1) x hx
      exact ⟨sp,by simpa only [Nat.add_assoc,Nat.add_comm 1 i] using hs,hc⟩)
    refine ⟨b::bs,by simp [hlen],?_⟩
    intro i x y hx hy
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hx hy
      subst x; subst y
      exact ⟨⟨hb,hpre,hctx,hvid,hf,hvalid,htau,hn,hlocal⟩,by
        simpa only [Nat.add_zero] using (show PreparedRun p tau b from ⟨by rw [hsp];exact hindex,hr⟩),hg⟩
    | succ i =>
      simpa only [Nat.add_assoc,Nat.add_comm 1 i] using hbs i x y hx hy

theorem ordered_blocks {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    (hw : walkD0 cb=.ok k) (hm : m.NativeValid k w)
    {steps : List ImplicitStepV3} {last : Bytes}
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hlen : steps.length=k.implicitBlks.length) (vids : Nat→Nat) :
    ∃main : NativeBlock,∃tail : List NativeBlock,
      tail.length=steps.length ∧
      schedulerUpsertWitness (m.ctx k) m.pre=.ok main.witness ∧
      main.witness.pre=m.pre ∧
      (∀i e b,steps[i]?=some e→tail[i]?=some b→MissingBlockAt k vids (1+i) e b) ∧
      ∀(i : Nat) (b : NativeBlock),(main::tail)[i]?=some b→PreparedRun p i b ∧ b.Valid ∧ b.run.n≤64 ∧
        b.run.tau=i ∧ b.vid=vids i ∧
        (∀time pub,TableLocal ProcPriorCodecActual.table (SchedHeight.trace b.output.rows codecPad) time pub) ∧
        GrantWit b := by
  obtain ⟨sp,hsp,hpub⟩ := prepD0_context_index hp hw hm 0 (m.ctx k) rfl
  obtain ⟨b,hb,hpre,hctx,hpub',hvid,hf,hvalid,hr,htau,hn,hlocal,hg⟩ :=
    main_block hp (m.ctx k) sp (List.mem_iff_getElem?.mpr ⟨0,hsp⟩) hpub
      m.pre (appliedReceipts k w) m.result hm.run (vids 0)
  obtain ⟨bs,hbs,hAt⟩ := implicit_blocks hp hv 1 (by decide) vids (implicit_prepared_index hp hw hm hv hlen)
  refine ⟨b,bs,hbs,hb,hpre,(fun i e x he hx=>(hAt i e x he hx).1),?_⟩
  intro i x hx
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero,Option.some.injEq] at hx
    subst x
    exact ⟨⟨by rw [hpub'];exact hsp,hr⟩,hvalid,hn,htau,hvid,hlocal,hg⟩
  | succ i =>
    simp only [List.getElem?_cons_succ] at hx
    have hi : i<steps.length := by
      have hh := (List.getElem?_eq_some_iff.mp hx).1
      omega
    let e := steps[i]
    have he : steps[i]?=some e := List.getElem?_eq_getElem hi
    have hpair := hAt i e x he hx
    have hh := hpair.1
    exact ⟨by simpa only [Nat.add_comm 1 i] using hpair.2.1,hh.2.2.2.2.2.1,hh.2.2.2.2.2.2.2.1,
      by simpa [Nat.add_comm] using hh.2.2.2.2.2.2.1,
      by simpa [Nat.add_comm] using hh.2.2.2.1,hh.2.2.2.2.2.2.2.2,hpair.2.2⟩

theorem implicit_pair_list (k : WalkD0) (vids : Nat→Nat)
    (steps : List ImplicitStepV3) (bs : List NativeBlock) (hlen:bs.length=steps.length)
    (hb:∀i e b,steps[i]?=some e→bs[i]?=some b→MissingBlockAt k vids (1+i) e b) :
    bs.map (fun b=>(b.witness.ctx,b.witness.pre))=steps.map (fun e=>(implicitCtx k e,e.pre)) := by
  apply List.ext_getElem (by simp [hlen])
  intro i hi hj
  simp only [List.length_map] at hi hj
  have hh:=hb i steps[i] bs[i] (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hi)
  simp only [List.getElem_map, hh.2.1, hh.2.2.1]
  rfl

theorem allocated_blocks {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    (hw : walkD0 cb=.ok k) (hm : m.NativeValid k w)
    {steps : List ImplicitStepV3} {last : Bytes}
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hlen : steps.length=k.implicitBlks.length) :
    ∃bs : List NativeBlock,bs.length=steps.length+1 ∧
      bs.map (fun b=>b.witness.pre)=m.pre::steps.map ImplicitStepV3.pre ∧
      bs.map (fun b=>(b.witness.ctx,b.witness.pre))=(m.ctx k,m.pre)::steps.map (fun e=>(implicitCtx k e,e.pre)) ∧
      ∀(i : Nat)(b : NativeBlock),bs[i]?=some b→PreparedRun p i b ∧ b.Valid ∧ b.run.n≤64 ∧ b.run.tau=i ∧
        b.vid=priorValueId ((bs.map (fun b=>b.witness.pre)).take i) b.witness.pre ∧
        (∀time pub,TableLocal ProcPriorCodecActual.table (SchedHeight.trace b.output.rows codecPad) time pub) ∧
        GrantWit b := by
  let trees:=m.pre::steps.map ImplicitStepV3.pre
  obtain ⟨main,tail,htail,hmw,hpre,hAt,hb⟩:=ordered_blocks hp hw hm hv hlen (nativePriorIds trees)
  have he:(main::tail).map (fun b=>b.witness.pre)=trees := by
    simp only [List.map_cons,hpre,implicit_pre_list k (nativePriorIds trees) steps tail htail hAt,trees]
  have hc:(main::tail).map (fun b=>(b.witness.ctx,b.witness.pre))=
      (m.ctx k,m.pre)::steps.map (fun e=>(implicitCtx k e,e.pre)) := by
    simp only [List.map_cons,hpre,schedulerUpsertWitness_ctx hmw,
      implicit_pair_list k (nativePriorIds trees) steps tail htail hAt]
  refine ⟨main::tail,by simp [htail],he,hc,?_⟩
  intro i b hi
  have hpair:=hb i b hi
  have hh:=hpair.2
  have ht:trees[i]?=some b.witness.pre := by
    rw [←he,List.getElem?_map,hi]
    rfl
  refine ⟨hpair.1,hh.1,hh.2.1,hh.2.2.1,?_,hh.2.2.2.2.1,hh.2.2.2.2.2⟩
  rw [he,hh.2.2.2.1]
  simp [nativePriorIds,ht]

/-- `accepted_prior_core` with the distribution witness of every block. -/
theorem accepted_prior_core_grants {B : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w)
    (h:checkD0a B cb wb=.ok ()) (hB:B≤2000000) :
    ∃bs,PriorCore p B bs ∧ ∀ b ∈ bs, GrantWit b := by
  obtain ⟨m,steps,last,hm,_,hv,hlen,hcount,_,_⟩:=checkD0a_native_trace hk hw h
  obtain ⟨bs,hs,hpre,-,hb⟩:=allocated_blocks hp hk hm hv hlen
  have hlen':bs.length≤32 := by omega
  have hvalid:∀b∈bs,b.Valid ∧ b.run.n≤64 ∧
      TableLocal ProcPriorCodecActual.table (SchedHeight.trace b.output.rows codecPad) 0 [] := by
    intro b hmem
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hmem
    have hh:=(hb i b hi).2
    exact ⟨hh.1,hh.2.1,hh.2.2.2.2.1 0 []⟩
  have horder:∀(i : Nat)(b : NativeBlock),bs[i]?=some b→b.run.tau=i := fun i b hi=>(hb i b hi).2.2.2.1
  have hbytes:=checkD0a_preBytes hk hw h hm hv
  have hcharge:=ProcRawNativeBudget.total_bound bs (fun b hm=>(hvalid b hm).1)
  rw [hpre] at hcharge
  have hraw:(ProcRawConcatGeometry.rows bs).length≤B+1184 := by omega
  have hforest:preBytes (bs.map (fun b=>b.witness.pre))≤B := by
    rw [hpre]
    exact hbytes
  have hindex:∀(i : Nat)(b : NativeBlock),bs[i]?=some b→PreparedRun p i b ∧ b.run.tau=i ∧
      b.vid=priorValueId ((bs.map (fun b=>b.witness.pre)).take i) b.witness.pre :=
    fun i b hi=>⟨(hb i b hi).1,(hb i b hi).2.2.2.1,(hb i b hi).2.2.2.2.1⟩
  have hbr:∀b∈bs,b.Valid ∧ b.pub∈p.sched ∧
      ∃tauV,ActualRun.run (ProcPreparedSequence.input b.pub b.old) tauV=.ok b.run := by
    intro b hm
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hm
    have hr:=(hindex i b hi).1
    exact ⟨(hvalid b hm).1,List.mem_iff_getElem?.mpr ⟨i,hr.1⟩,i,hr.2⟩
  have hn:∀b∈bs,b.pub.ids.length≤64:=fun b hm=>(prepD0_sched hp b.pub (hbr b hm).2.1).n64
  have hcapraw:(ProcRawConcatGeometry.rows bs).length≤2001184:=by omega
  refine ⟨bs,{
    length:=hlen',forest:=hforest,valid:=fun b hm=>⟨(hvalid b hm).1,(hvalid b hm).2.1⟩,indexed:=hindex,
    raw_bound:=hraw,
    overlay_bound:=(ProcPriorOverlayBudget.capacity bs hn hlen' hcapraw).1,
    codec_local:=fun t pub=>ProcCodecNativeConcatLocal.indexed_table bs (by omega) hvalid horder t pub,
    raw_local:=fun t pub=>ProcRawNativeLocal.table bs (fun b hm=>(hvalid b hm).1) horder (by omega) _ _ _ _ _ _ _,
    record_local:=fun t pub=>ProcRecordConcatLocal.native (fun b=>b.pub.ids) bs (fun b hm=>(hvalid b hm).1)
      horder (by omega) t pub,
    memory_local:=fun t pub=>ProcPriorNativeMemory.native_gated_local bs hn hlen' horder hcapraw t 67 68 69 pub,
    presence:=ProcNativePresenceBalance.balance bs (fun b hm=>⟨(hvalid b hm).1,(hvalid b hm).2.1⟩) hlen' (by omega),
    raw_record:=ProcRecordSelectedTraffic.balance (fun b=>b.pub.ids) bs (fun b hm=>(hvalid b hm).1) (by omega),
    memory_read:=ProcPriorNativeMemory.codec_balance hp bs hlen' hbr hcapraw,
    memory_write:=ProcPriorNativeMemory.record_balance bs hn hlen' hcapraw,
    id_data:=fun req=>ProcNativeIdBalance.balance req (fun b=>b.pub.ids) bs (by omega)
      (Nat.le_of_lt (ProcNativeIdBalance.native_capacity _ bs hn hlen' hcapraw)) },?_⟩
  intro b hm
  obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hm
  exact (hb i b hi).2.2.2.2.2.2

/-- `accepted_prior_core_grants` on a GIVEN native trace `(m, steps)`, with the blocks' calls
(context, pre-trie) = the trace's calls. -/
theorem prior_core_on {B : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w)
    (h:checkD0a B cb wb=.ok ()) (hB:B≤2000000)
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hlen : steps.length=k.implicitBlks.length) (hcount : steps.length≤31) :
    ∃bs,PriorCore p B bs ∧ (∀ b ∈ bs, GrantWit b) ∧
      bs.map (fun b=>(b.witness.ctx,b.witness.pre))=(m.ctx k,m.pre)::steps.map (fun e=>(implicitCtx k e,e.pre)) := by
  obtain ⟨bs,hs,hpre,hctx,hb⟩:=allocated_blocks hp hk hm hv hlen
  have hlen':bs.length≤32 := by omega
  have hvalid:∀b∈bs,b.Valid ∧ b.run.n≤64 ∧
      TableLocal ProcPriorCodecActual.table (SchedHeight.trace b.output.rows codecPad) 0 [] := by
    intro b hmem
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hmem
    have hh:=(hb i b hi).2
    exact ⟨hh.1,hh.2.1,hh.2.2.2.2.1 0 []⟩
  have horder:∀(i : Nat)(b : NativeBlock),bs[i]?=some b→b.run.tau=i := fun i b hi=>(hb i b hi).2.2.2.1
  have hbytes:=checkD0a_preBytes hk hw h hm hv
  have hcharge:=ProcRawNativeBudget.total_bound bs (fun b hm=>(hvalid b hm).1)
  rw [hpre] at hcharge
  have hraw:(ProcRawConcatGeometry.rows bs).length≤B+1184 := by omega
  have hforest:preBytes (bs.map (fun b=>b.witness.pre))≤B := by
    rw [hpre]
    exact hbytes
  have hindex:∀(i : Nat)(b : NativeBlock),bs[i]?=some b→PreparedRun p i b ∧ b.run.tau=i ∧
      b.vid=priorValueId ((bs.map (fun b=>b.witness.pre)).take i) b.witness.pre :=
    fun i b hi=>⟨(hb i b hi).1,(hb i b hi).2.2.2.1,(hb i b hi).2.2.2.2.1⟩
  have hbr:∀b∈bs,b.Valid ∧ b.pub∈p.sched ∧
      ∃tauV,ActualRun.run (ProcPreparedSequence.input b.pub b.old) tauV=.ok b.run := by
    intro b hm
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hm
    have hr:=(hindex i b hi).1
    exact ⟨(hvalid b hm).1,List.mem_iff_getElem?.mpr ⟨i,hr.1⟩,i,hr.2⟩
  have hn:∀b∈bs,b.pub.ids.length≤64:=fun b hm=>(prepD0_sched hp b.pub (hbr b hm).2.1).n64
  have hcapraw:(ProcRawConcatGeometry.rows bs).length≤2001184:=by omega
  refine ⟨bs,{
    length:=hlen',forest:=hforest,valid:=fun b hm=>⟨(hvalid b hm).1,(hvalid b hm).2.1⟩,indexed:=hindex,
    raw_bound:=hraw,
    overlay_bound:=(ProcPriorOverlayBudget.capacity bs hn hlen' hcapraw).1,
    codec_local:=fun t pub=>ProcCodecNativeConcatLocal.indexed_table bs (by omega) hvalid horder t pub,
    raw_local:=fun t pub=>ProcRawNativeLocal.table bs (fun b hm=>(hvalid b hm).1) horder (by omega) _ _ _ _ _ _ _,
    record_local:=fun t pub=>ProcRecordConcatLocal.native (fun b=>b.pub.ids) bs (fun b hm=>(hvalid b hm).1)
      horder (by omega) t pub,
    memory_local:=fun t pub=>ProcPriorNativeMemory.native_gated_local bs hn hlen' horder hcapraw t 67 68 69 pub,
    presence:=ProcNativePresenceBalance.balance bs (fun b hm=>⟨(hvalid b hm).1,(hvalid b hm).2.1⟩) hlen' (by omega),
    raw_record:=ProcRecordSelectedTraffic.balance (fun b=>b.pub.ids) bs (fun b hm=>(hvalid b hm).1) (by omega),
    memory_read:=ProcPriorNativeMemory.codec_balance hp bs hlen' hbr hcapraw,
    memory_write:=ProcPriorNativeMemory.record_balance bs hn hlen' hcapraw,
    id_data:=fun req=>ProcNativeIdBalance.balance req (fun b=>b.pub.ids) bs (by omega)
      (Nat.le_of_lt (ProcNativeIdBalance.native_capacity _ bs hn hlen' hcapraw)) },?_,hctx⟩
  intro b hm
  obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hm
  exact (hb i b hi).2.2.2.2.2.2

end ZkFormal.NearV3.Render.CdcGrant
