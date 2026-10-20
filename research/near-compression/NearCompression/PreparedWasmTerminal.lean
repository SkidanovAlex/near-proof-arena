import NearCompression.PreparedWasmStep

namespace NearCompression
open ZkFormal.Algebra ZkFormal.Air NearSpecV3.Wasm

/-- No-host gas context used by this prepared straight-line slice. It records
actual machine fields omitted by the AIR fast-gas column. -/
def PreparedWasmGasContext (s : St) : Prop :=
  s.gas.promises=0 ∧ s.gas.limit=s.gas.prepaid ∧ s.gas.burnt≤s.gas.prepaid ∧
  s.gas.g≤s.gas.prepaid-s.gas.burnt ∧ s.gas.prepaid≤maxGasBurnt

/-- Exact deferred-gas synchronization, proved using the actual burn function. -/
theorem prepared_wasm_sync (s : St) (context : PreparedWasmGasContext s) :
    sync s=.ok {s with gas:={s.gas with burnt:=s.gas.prepaid-s.gas.g}} := by
  rcases context with ⟨promises,limit,spent,remaining,prepaid⟩
  have bound : maxGasBurnt<u64Bound := by decide
  have total : s.gas.burnt+(s.gas.prepaid-s.gas.burnt-s.gas.g)=s.gas.prepaid-s.gas.g := by omega
  have noOverflow : s.gas.burnt+(s.gas.prepaid-s.gas.burnt-s.gas.g)<u64Bound := by omega
  have enough : s.gas.burnt+(s.gas.prepaid-s.gas.burnt-s.gas.g)≤s.gas.limit := by omega
  have rem : s.gas.remaining=s.gas.prepaid-s.gas.burnt := by simp only [Gas.remaining,Gas.used,promises,Nat.add_zero]
  simp only [sync,rem]
  split
  · rename_i zero
    have same : s.gas.prepaid-s.gas.g=s.gas.burnt := by omega
    simp only [same]
  · rw [total] at noOverflow enough
    simp only [burn,total,Nat.not_le.mpr noOverflow,ite_false,enough,ite_true]

/-- Successful charge preserves the no-host synchronization invariant. -/
theorem prepared_wasm_gas_context_charge (s : St) (context : PreparedWasmGasContext s)
    (amount : Nat) :
    PreparedWasmGasContext {s with gas:={s.gas with g:=s.gas.g-amount}} := by
  rcases context with ⟨a,b,c,d,e⟩
  exact ⟨a,b,c,by change s.gas.g-amount≤s.gas.prepaid-s.gas.burnt;omega,e⟩

/-- At an actual failed range-charge point, sync/burn occurs before any
instruction or operand is consumed. This exact branch also exposes overflow
and gas-limit errors rather than assuming every failure is GasExceeded. -/
theorem prepared_wasm_exhaustion (cfg : NearCfg) (p : Prepared) (s : St)
    (f : Frame) (fs : List Frame) (pf : PFunc) (ins : Instr) (amount : Nat)
    (frames : s.frames=f::fs) (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some ins) (metadata : PreparedWasmCharge pf f.pc amount)
    (bounded : amount<u64Bound) (exhausted : s.gas.g<amount)
    (context : PreparedWasmGasContext s) :
    step cfg p s =
      let synced := {s with gas:={s.gas with burnt:=s.gas.prepaid-s.gas.g}}
      match burn synced.gas amount with
      | (gs,some error) => .abort {synced with gas:=gs} error
      | (gs,none) => .unmodeled s!"finite_wasm_gas({amount}) did not fail ({gs.burnt})" := by
  rcases metadata with ⟨_,zero⟩ | ⟨k,fee,gas,linear,cost⟩
  · omega
  · simp only [step,frames,func,code,gas,charge,linear,cost,Nat.mul_zero,Nat.zero_add,
      Nat.not_le.mpr bounded,ite_false,exhausted,ite_true,prepared_wasm_sync s context]
    generalize burn {s.gas with burnt:=s.gas.prepaid-s.gas.g} amount = outcome
    rcases outcome with ⟨gs,error⟩
    cases error <;> rfl

/-- End of the final void function returns a real final state, restoring the
frame's stack budget. The row's terminal PC is a diagnostic snapshot, not an
extra live interpreter frame. -/
theorem prepared_wasm_end (cfg : NearCfg) (p : Prepared) (s : St)
    (f : Frame) (pf : PFunc) (amount : Nat)
    (frames : s.frames=[f]) (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some .end_) (labels : f.labels=[] ∨ ∃ lab,f.labels=[lab])
    (emptyStack : s.stack=#[]) (metadata : PreparedWasmCharge pf f.pc amount)
    (bounded : amount<u64Bound) (enough : amount≤s.gas.g) :
    step cfg p s=.fin {s with
      stack := #[]
      frames := []
      stackRem := s.stackRem+pf.stackCharge
      gas := {s.gas with g:=s.gas.g-amount}} := by
  rw [prepared_wasm_step_charge cfg p s f [] pf .end_ amount frames func code metadata bounded enough]
  rcases labels with labels | ⟨lab,labels⟩ <;>
    simp only [exec,labels,doReturn,frames,func,emptyStack,Array.size_empty,
      Array.extract_empty,Array.empty_append,List.isEmpty_nil,ite_true]

/-- Exact post-return synchronization, including the deferred burnt counter. -/
theorem prepared_wasm_end_sync (s : St) (pf : PFunc) (amount : Nat)
    (context : PreparedWasmGasContext s) :
    sync {s with
      stack := #[]
      frames := []
      stackRem := s.stackRem+pf.stackCharge
      gas := {s.gas with g:=s.gas.g-amount}} =
    .ok {s with
      stack := #[]
      frames := []
      stackRem := s.stackRem+pf.stackCharge
      gas := {s.gas with g:=s.gas.g-amount,burnt:=s.gas.prepaid-(s.gas.g-amount)}} := by
  exact prepared_wasm_sync _ (prepared_wasm_gas_context_charge s context amount)

/-- Exact failed-burn gas state; fast `g` is deliberately retained by the
interpreter even when burnt gas is clamped to prepaid gas. -/
def preparedWasmFailureGas (s : St) (amount : Nat) : Gas :=
  let gs := {s.gas with burnt:=s.gas.prepaid-s.gas.g}
  if gs.burnt+amount≥u64Bound then gs else {gs with burnt:=s.gas.prepaid,promises:=0}

def preparedWasmFailureError (s : St) (amount : Nat) : String :=
  if s.gas.prepaid-s.gas.g+amount≥u64Bound then errIntOverflow
  else if s.gas.prepaid-s.gas.g+amount>maxGasBurnt then errGasLimitExceeded else errGasExceeded

theorem prepared_wasm_failure_burn (s : St) (amount : Nat)
    (context : PreparedWasmGasContext s) (exhausted : s.gas.g<amount) :
    burn {s.gas with burnt:=s.gas.prepaid-s.gas.g} amount =
      (preparedWasmFailureGas s amount,some (preparedWasmFailureError s amount)) := by
  rcases context with ⟨promises,limit,spent,remaining,prepaid⟩
  have greater : s.gas.prepaid<s.gas.prepaid-s.gas.g+amount := by omega
  unfold burn preparedWasmFailureGas preparedWasmFailureError
  by_cases noOverflow : s.gas.prepaid-s.gas.g+amount≥u64Bound
  · simp only [noOverflow,ite_true]
  ·
    have lim : ¬s.gas.prepaid-s.gas.g+amount≤s.gas.limit := by omega
    simp only [noOverflow,lim,ite_false,processGasLimit,promises,Nat.add_zero,
      Nat.mod_eq_of_lt (Nat.lt_of_not_ge noOverflow),Nat.min_eq_left prepaid,
      Nat.min_eq_right (Nat.le_of_lt greater),Nat.min_eq_left (Nat.le_of_lt greater),Nat.sub_self]

/-- Gas failure is an actual trap, including the precise overflow/limit class;
the impossible successful-burn fallback is eliminated from this context. -/
theorem prepared_wasm_exhaustion_trap (cfg : NearCfg) (p : Prepared) (s : St)
    (f : Frame) (fs : List Frame) (pf : PFunc) (ins : Instr) (amount : Nat)
    (frames : s.frames=f::fs) (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some ins) (metadata : PreparedWasmCharge pf f.pc amount)
    (bounded : amount<u64Bound) (exhausted : s.gas.g<amount)
    (context : PreparedWasmGasContext s) :
    step cfg p s=.abort {s with gas:=preparedWasmFailureGas s amount}
      (preparedWasmFailureError s amount) := by
  rw [prepared_wasm_exhaustion cfg p s f fs pf ins amount frames func code metadata bounded exhausted context]
  simp only [prepared_wasm_failure_burn s amount context exhausted]

/-- The unconditional `callEntry` exit hook leaves the derived failure state
unchanged: no deferred charge remains after failure synchronization/burning. -/
theorem prepared_wasm_failure_sync (s : St) (amount : Nat)
    (context : PreparedWasmGasContext s) :
    sync {s with gas:=preparedWasmFailureGas s amount}=
      .ok {s with gas:=preparedWasmFailureGas s amount} := by
  have noDeferred : (preparedWasmFailureGas s amount).remaining-
      (preparedWasmFailureGas s amount).g=0 := by
    rcases context with ⟨promises,_,spent,remaining,_⟩
    unfold preparedWasmFailureGas
    dsimp only
    split <;> simp only [Gas.remaining,Gas.used,promises,Nat.add_zero] <;> omega
  simp only [sync,noDeferred,ite_true]

/-- Actual AIR terminal end row to actual final-frame return. The live stack
is proved empty from the source end-depth constraint and one-hot state binding. -/
theorem prepared_table_wasm_end (table : Table) (source : PreparedTerminalSource table)
    (prefixPart middle : List Expr) (dead : Nat → Nat → Expr)
    (transitionSource : table.constraints=preparedAddTransitionSource prefixPart middle dead)
    (endMember : preparedEndDepthPython∈table.constraints)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : ZkFormal.Near.TableLocal table tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 25=0)
    (publicBounds : ∀ pc,pc<16 → ∀ limb,limb<4 → (pub.getD (56+10*pc+(6+limb)) 0).toNat<65536)
    (publicEnd : ∀ pc,pc<16 → tr.cell t r pc=1 → ∀ tag,tag<4 → pub.getD (56+10*pc+tag) 0=if tag=3 then 1 else 0)
    (enoughGas : preparedFeeValue (tr.cell t r) pub≤preparedGasValue (tr.cell t r) pub)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (pc sp : Nat)
    (state : PreparedWasmState (tr.cell t r) pub s f [] pc sp)
    (func : p.funcs[f.fn]?=some pf) (code : pf.code[f.pc]?=some .end_)
    (labels : f.labels=[] ∨ ∃ lab,f.labels=[lab])
    (metadata : PreparedWasmCharge pf f.pc (preparedFeeValue (tr.cell t r) pub)) :
    tr.cell t (r+1) 25=1 ∧ tr.cell t (r+1) 26=0 ∧
    step cfg p s=.fin {s with
      stack := #[]
      frames := []
      stackRem := s.stackRem+pf.stackCharge
      gas := {s.gas with g:=preparedGasValue (tr.cell t (r+1)) pub}} := by
  have terminal:=prepared_table_end table source prefixPart middle dead transitionSource endMember
    tr t r pub localH nonlast active publicBounds publicEnd enoughGas
  have choices:=prepared_table_row_choices table source.gasMiddle source.gasTail source.gasSource
    tr t r pub localH (by omega) (tr.cell t (r+1))
  have feeBounds:=prepared_gas_public_fee_bounds (tr.cell t r) (tr.cell t (r+1)) pub 0 0 choices publicBounds
  have bounded : preparedFeeValue (tr.cell t r) pub<u64Bound := prepared_gas_word_bound _ feeBounds
  rcases state with ⟨hp,hs,pcs,sps,frames,fpc,stack,gas⟩
  have selected:=sps 0 (by decide)
  simp only [Nat.add_zero,terminal.1] at selected
  have empty : sp=0 := by
    by_cases zero : 0=sp
    · exact zero.symm
    · simp only [zero,ite_false] at selected
      exact False.elim ((by decide : (1:Fp)≠0) selected)
  have emptyStack : s.stack=#[] := by rw [stack,empty];rfl
  have actual:=prepared_wasm_end cfg p s f pf _ frames func code labels emptyStack metadata bounded
    (by rw [gas];exact enoughGas)
  refine ⟨terminal.2.1,terminal.2.2.1,?_⟩
  simpa only [gas,terminal.2.2.2.1] using actual

/-- Source-table gas exhaustion implies the precise actual trap and AIR
terminal status. The AIR frozen fast counter is not confused with burnt gas. -/
theorem prepared_table_wasm_exhaustion (table : Table) (source : PreparedTerminalSource table)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : ZkFormal.Near.TableLocal table tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 25=0)
    (publicBounds : ∀ pc,pc<16 → ∀ limb,limb<4 → (pub.getD (56+10*pc+(6+limb)) 0).toNat<65536)
    (exhausted : preparedGasValue (tr.cell t r) pub<preparedFeeValue (tr.cell t r) pub)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame) (pf : PFunc)
    (ins : Instr) (pc sp : Nat) (state : PreparedWasmState (tr.cell t r) pub s f fs pc sp)
    (func : p.funcs[f.fn]?=some pf) (code : pf.code[f.pc]?=some ins)
    (metadata : PreparedWasmCharge pf f.pc (preparedFeeValue (tr.cell t r) pub))
    (context : PreparedWasmGasContext s) :
    tr.cell t (r+1) 25=1 ∧ tr.cell t (r+1) 26=1 ∧
    preparedGasValue (tr.cell t (r+1)) pub=preparedGasValue (tr.cell t r) pub ∧
    step cfg p s=.abort {s with gas:=preparedWasmFailureGas s (preparedFeeValue (tr.cell t r) pub)}
      (preparedWasmFailureError s (preparedFeeValue (tr.cell t r) pub)) := by
  have terminal:=prepared_table_exhaustion table source tr t r pub localH nonlast active publicBounds exhausted
  have choices:=prepared_table_row_choices table source.gasMiddle source.gasTail source.gasSource
    tr t r pub localH (by omega) (tr.cell t (r+1))
  have feeBounds:=prepared_gas_public_fee_bounds (tr.cell t r) (tr.cell t (r+1)) pub 0 0 choices publicBounds
  have bounded : preparedFeeValue (tr.cell t r) pub<u64Bound := prepared_gas_word_bound _ feeBounds
  rcases state with ⟨_,_,_,_,frames,_,_,gas⟩
  exact ⟨terminal.2.2.1,terminal.2.2.2.1,terminal.2.2.2.2,
    prepared_wasm_exhaustion_trap cfg p s f fs pf ins _ frames func code metadata bounded
      (by rw [gas];exact exhausted) context⟩

end NearCompression
