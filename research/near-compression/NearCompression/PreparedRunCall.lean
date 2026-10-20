import NearCompression.PreparedPublicOutput

set_option maxHeartbeats 20000

namespace NearCompression
open NearSpecV3.Wasm ZkFormal.Algebra ZkFormal.Air ZkFormal.V2

structure PreparedRunCallSetup where
  program : Prepared
  host : St
  methodIndex : Nat

/-- Executable successful setup path of real runCall: prepare, both loading
charges, link, resolve, instantiate, and context installation. Start functions
are rejected in this straight-line slice. No supplied PFunc substitutes for
actual preparation. -/
def preparedRunCallSetupCore (ctx : CallCtx) (empty : Bool) (prep : PrepResult) (bytes : Gas × Option String)
    (base : Gas → Gas × Option String) (linker : Prepared → LinkResult)
    (resolver : Prepared → Resolve) (instantiateFn : Prepared → Gas → Except String St) : Option PreparedRunCallSetup :=
  if empty then none else
  match prep with
  | .ok p =>
    if p.m.imports.any (fun i=>curveHosts.contains i.name) then none else
    match bytes with
    | (gs,none) =>
      match base gs with
      | (gs,none) =>
        match linker p with
        | .ok =>
          match resolver p with
          | .ok fi =>
            match instantiateFn p gs with
            | .ok host =>
              match p.m.start with
              | none => some ⟨p, { host with
                  ctx := ctx
                  balance := ctx.accountBalance + ctx.attachedDeposit
                  storageUsage := ctx.storageUsage
                  real := none }, fi⟩
              | _ => none
            | _ => none
          | _ => none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

def preparedRunCallSetup (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (blockLevel : Bool := true) : Option PreparedRunCallSetup :=
  preparedRunCallSetupCore ctx method.isEmpty (prepare cfg code blockLevel)
    (payPer (Gas.init ctx.prepaidGas) C.contractLoadingBytes code.size)
    (fun gs=>payBase gs C.contractLoadingBase) link (fun p=>resolve p method) (instantiate cfg)

/-- Outer interpreter reduction with symbolic results of each setup computation. -/
theorem prepared_run_call_path (cfg : NearCfg) (code : ByteArray) (method : String)
    (ctx : CallCtx) (blockLevel full : Bool) (p : Prepared) (loaded gas : Gas)
    (fi : Nat) (host : St) (fuel : Nat) (final : St) (error : Option String)
    (methodNonempty : ¬method.isEmpty=true)
    (preparation : prepare cfg code blockLevel=.ok p)
    (noCurves : ¬(p.m.imports.any (fun i=>curveHosts.contains i.name))=true)
    (byteLoading : payPer (Gas.init ctx.prepaidGas) C.contractLoadingBytes code.size=(loaded,none))
    (baseLoading : payBase loaded C.contractLoadingBase=(gas,none))
    (linked : link p=.ok) (resolved : resolve p method=.ok fi)
    (instantiated : instantiate cfg p gas=.ok host) (noStart : p.m.start=none)
    (body : callEntry cfg p fuel { host with
      ctx := ctx
      balance := ctx.accountBalance+ctx.attachedDeposit
      storageUsage := ctx.storageUsage
      real := none } fi=.ok (final,error)) :
    runCall cfg code method ctx fuel blockLevel full none=.done final error := by
  simp only [runCall, methodNonempty, preparation, noCurves,
    byteLoading, baseLoading, linked, resolved, instantiated, noStart,
    Bool.false_eq_true, ite_false, Option.isNone, Bool.and_false, body]

/-- Provenance extracted from the executable setup checker. -/
theorem prepared_run_call_setup_core_provenance (ctx : CallCtx) (empty : Bool) (prep : PrepResult) (bytes : Gas × Option String)
    (base : Gas → Gas × Option String) (linker : Prepared → LinkResult)
    (resolver : Prepared → Resolve) (instantiateFn : Prepared → Gas → Except String St) (setup : PreparedRunCallSetup)
    (accepted : preparedRunCallSetupCore ctx empty prep bytes base linker resolver instantiateFn=some setup) :
    ∃ (p : Prepared) (loaded gas : Gas) (fi : Nat) (host : St),
      (¬empty=true) ∧ prep=.ok p ∧
      (¬(p.m.imports.any (fun i=>curveHosts.contains i.name))=true) ∧
      bytes=(loaded,none) ∧
      base loaded=(gas,none) ∧ linker p=.ok ∧
      resolver p=.ok fi ∧ instantiateFn p gas=.ok host ∧ p.m.start=none ∧
      setup=⟨p,{ host with
        ctx := ctx
        balance := ctx.accountBalance+ctx.attachedDeposit
        storageUsage := ctx.storageUsage
        real := none },fi⟩ := by
  unfold preparedRunCallSetupCore at accepted
  split at accepted
  · cases accepted
  · rename_i methodNonempty
    generalize preparation : prep = prepared at accepted
    cases prepared with
    | ok p =>
      simp only at accepted
      split at accepted
      · cases accepted
      · rename_i noCurves
        generalize byteLoading : bytes = loaded at accepted
        rcases loaded with ⟨loaded, err⟩
        cases err with
        | some err => cases accepted
        | none =>
          simp only at accepted
          generalize baseLoading : base loaded = paid at accepted
          rcases paid with ⟨gas, err⟩
          cases err with
          | some err => cases accepted
          | none =>
            simp only at accepted
            generalize linked : linker p = linkedResult at accepted
            cases linkedResult with
            | linkError _ => cases accepted
            | invariant _ => cases accepted
            | ok =>
              simp only at accepted
              generalize resolved : resolver p = resolvedResult at accepted
              cases resolvedResult with
              | notFound => cases accepted
              | invalidSignature => cases accepted
              | invariant _ => cases accepted
              | ok fi =>
                simp only at accepted
                generalize instantiated : instantiateFn p gas = instantiatedResult at accepted
                cases instantiatedResult with
                | error _ => cases accepted
                | ok host =>
                  simp only at accepted
                  generalize noStart : p.m.start = start at accepted
                  cases start with
                  | some _ => cases accepted
                  | none =>
                    cases accepted
                    exact ⟨p,loaded,gas,fi,host,methodNonempty,rfl,noCurves,
                      rfl,baseLoading,linked,resolved,instantiated,noStart,rfl⟩
    | prepErr _ _ => cases accepted
    | compileErr _ _ => cases accepted
    | outOfDomain _ => cases accepted
    | unmodeled _ => cases accepted

theorem prepared_run_call_setup_sound (cfg : NearCfg) (code : ByteArray) (method : String)
    (ctx : CallCtx) (blockLevel full : Bool) (setup : PreparedRunCallSetup)
    (accepted : preparedRunCallSetup cfg code method ctx blockLevel=some setup)
    (fuel : Nat) (final : St) (error : Option String)
    (body : callEntry cfg setup.program fuel setup.host setup.methodIndex=.ok (final,error)) :
    runCall cfg code method ctx fuel blockLevel full none=.done final error := by
  obtain ⟨p,loaded,gas,fi,host,nonempty,prep,curves,bytes,base,linked,resolved,instantiated,start,eq⟩ :=
    prepared_run_call_setup_core_provenance ctx method.isEmpty (prepare cfg code blockLevel)
      (payPer (Gas.init ctx.prepaidGas) C.contractLoadingBytes code.size)
      (fun gs=>payBase gs C.contractLoadingBase) link (fun p=>resolve p method) (instantiate cfg) setup accepted
  subst setup
  exact prepared_run_call_path cfg code method ctx blockLevel full p loaded gas fi host fuel
    final error nonempty prep curves bytes base linked resolved instantiated start body

/-- Entry eligibility checked against the actual prepared function and loaded host. -/
def preparedRunCallEntryCheck (setup : PreparedRunCallSetup) (pf : PFunc) (pub : List Fp) : Bool :=
  preparedCodeTerminatedCheck pf pub && preparedPublicEntryCheck pub setup.host pf &&
  decide (pf.stackCharge≤setup.host.stackRem ∧ pf.prologueGas<u64Bound ∧
    pf.prologueGas≤setup.host.gas.remaining ∧ setup.host.gas.promises=0 ∧
    setup.host.gas.limit=setup.host.gas.prepaid ∧ setup.host.gas.burnt≤setup.host.gas.prepaid ∧
    setup.host.gas.prepaid≤maxGasBurnt)

structure PreparedRunCallEligible where
  setup : PreparedRunCallSetup
  func : PFunc

/-- Actual setup and resolved-function lookup, followed by explicit bounded-slice
eligibility checks. Successful checks do not assert AIR validity. -/
def preparedRunCallCheck (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (pub : List Fp) (blockLevel : Bool := true) : Option PreparedRunCallEligible := do
  let setup ← preparedRunCallSetup cfg code method ctx blockLevel
  let pf ← setup.program.funcs[setup.methodIndex-setup.program.m.imports.size]?
  if preparedRunCallEntryCheck setup pf pub then some ⟨setup,pf⟩ else none

theorem prepared_run_call_checked (cfg : NearCfg) (code : ByteArray) (method : String)
    (ctx : CallCtx) (pub : List Fp) (blockLevel : Bool) (eligible : PreparedRunCallEligible)
    (accepted : preparedRunCallCheck cfg code method ctx pub blockLevel=some eligible) :
    preparedRunCallSetup cfg code method ctx blockLevel=some eligible.setup ∧
    eligible.setup.program.funcs[eligible.setup.methodIndex-eligible.setup.program.m.imports.size]?=some eligible.func ∧
    preparedRunCallEntryCheck eligible.setup eligible.func pub=true := by
  unfold preparedRunCallCheck at accepted
  obtain ⟨setup,setupEq,rest⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨pf,fetch,rest⟩ := Option.bind_eq_some_iff.mp rest
  split at rest
  · rename_i checked
    cases rest
    exact ⟨setupEq,fetch,checked⟩
  · cases rest

/-- Full bounded AIR acceptance and executable real-code eligibility imply the
actual outer runCall result, including its authenticated published output.
Preparation/loading and CODE checking remain verifier-side computations. -/
theorem prepared_wasm_public_run_call (constraints : List Expr) (tr : Trace Fp) (pub : List Fp)
    (source : PreparedWasmSource (preparedBoundaryTable constraints))
    (holds : HoldsP (preparedBoundaryAir constraints) pub tr)
    (lastMember : preparedLastDonePython∈constraints)
    (firstPC : preparedFirstEqPython 0 1∈constraints)
    (firstSP : preparedFirstEqPython 16 1∈constraints)
    (firstActive : preparedFirstEqPython 25 0∈constraints)
    (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (blockLevel full : Bool) (eligible : PreparedRunCallEligible)
    (accepted : preparedRunCallCheck cfg code method ctx pub blockLevel=some eligible)
    (extra : Nat) :
    ∃ final error,
      runCall cfg code method ctx (eligible.func.code.size+extra) blockLevel full none=.done final error ∧
      PreparedPublishedOutput pub final error := by
  obtain ⟨setup,fetch,checks⟩ := prepared_run_call_checked cfg code method ctx pub blockLevel eligible accepted
  simp only [preparedRunCallEntryCheck,Bool.and_eq_true,decide_eq_true_eq] at checks
  obtain ⟨codeCheck,entryCheck⟩ := checks.1
  obtain ⟨stack,fee,enough,promises,limit,spent,prepaid⟩ := checks.2
  obtain ⟨n,final,error,_,_,body,published⟩ := prepared_wasm_public_call_entry constraints tr pub
    source holds lastMember firstPC firstSP firstActive cfg eligible.setup.program
    eligible.setup.methodIndex eligible.func eligible.setup.host codeCheck entryCheck fetch
    stack fee enough promises limit spent prepaid extra
  exact ⟨final,error,prepared_run_call_setup_sound cfg code method ctx blockLevel full eligible.setup
    setup (eligible.func.code.size+extra) final error body,published⟩

end NearCompression
