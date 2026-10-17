import NearCompression.BoundaryWire

/-! Actual VM value and promise codecs. Reference/count bounds are explicit
codec obligations, not new restrictions on the state-transition challenge. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def valueWireWf : Val → Prop
  | .i32 _ | .i64 _ => True
  | .ref r => ∀ n, r = some n → n < 18446744073709551616

def encodeValueWire : Val → Bytes
  | .i32 v => u8 0 ++ u32 v.toNat
  | .i64 v => u8 1 ++ u64 v.toNat
  | .ref r => u8 2 ++ encOpt u64 r

def parseValueWire : NearSpecV3.P Val := fun bs => do
  let (tag, bs) ← pU8 "value tag" bs
  match tag with
  | 0 => let (v, bs) ← pU32 "i32" bs; pure (.i32 (UInt32.ofNat v), bs)
  | 1 => let (v, bs) ← pU64 "i64" bs; pure (.i64 (UInt64.ofNat v), bs)
  | 2 => let (r, bs) ← pOption "reference" (pU64 "index") bs; pure (.ref r, bs)
  | _ => throw "invalid value tag"

theorem value_wire_roundtrip (v : Val) (wf : valueWireWf v) (rest : Bytes) :
    parseValueWire (encodeValueWire v ++ rest) = .ok (v, rest) := by
  cases v with
  | i32 v =>
    simp only [encodeValueWire, List.append_assoc, parseValueWire]
    rw [pU8_ok _ _ _ (by decide)]
    simp only [bind, Except.bind]
    rw [pU32_ok _ _ _ v.toNat_lt]
    simp [bind, Except.bind, pure, Except.pure]
  | i64 v =>
    simp only [encodeValueWire, List.append_assoc, parseValueWire]
    rw [pU8_ok _ _ _ (by decide)]
    simp only [bind, Except.bind]
    rw [pU64_ok _ _ _ v.toNat_lt]
    simp [bind, Except.bind, pure, Except.pure]
  | ref r =>
    simp only [encodeValueWire, List.append_assoc, parseValueWire]
    rw [pU8_ok _ _ _ (by decide)]
    simp only [bind, Except.bind]
    rw [pOption_ok _ _ _ r rest (fun n hn tail => pU64_ok _ n tail (wf n hn))]
    rfl

def stackWireWf (vs : Array Val) : Prop :=
  vs.toList.length < 4294967296 ∧ ∀ v ∈ vs.toList, valueWireWf v

def encodeStackWire (vs : Array Val) : Bytes := encList encodeValueWire vs.toList

def parseStackWire : NearSpecV3.P (Array Val) := fun bs => do
  let (vs, bs) ← pVec "stack" parseValueWire bs
  pure (vs.toArray, bs)

theorem stack_wire_roundtrip (vs : Array Val) (wf : stackWireWf vs) (rest : Bytes) :
    parseStackWire (encodeStackWire vs ++ rest) = .ok (vs, rest) := by
  simp only [parseStackWire, encodeStackWire]
  rw [pVec_ok _ _ _ _ _ wf.1 (fun v hv tail => value_wire_roundtrip v (wf.2 v hv) tail)]
  simp [bind, Except.bind, pure, Except.pure]

def promiseWireWf : PromiseV → Prop
  | .receipt n => n < 18446744073709551616
  | .joint ns => ns.toList.length < 4294967296 ∧ ∀ n ∈ ns.toList, n < 18446744073709551616

def encodePromiseWire : PromiseV → Bytes
  | .receipt n => u8 0 ++ u64 n
  | .joint ns => u8 1 ++ encList u64 ns.toList

def parsePromiseWire : NearSpecV3.P PromiseV := fun bs => do
  let (tag, bs) ← pU8 "promise tag" bs
  match tag with
  | 0 => let (n, bs) ← pU64 "receipt" bs; pure (.receipt n, bs)
  | 1 => let (ns, bs) ← pVec "dependencies" (pU64 "receipt") bs; pure (.joint ns.toArray, bs)
  | _ => throw "invalid promise tag"

theorem promise_wire_roundtrip (v : PromiseV) (wf : promiseWireWf v) (rest : Bytes) :
    parsePromiseWire (encodePromiseWire v ++ rest) = .ok (v, rest) := by
  cases v with
  | receipt n =>
    simp only [encodePromiseWire, List.append_assoc, parsePromiseWire]
    rw [pU8_ok _ _ _ (by decide)]
    simp only [bind, Except.bind]
    rw [pU64_ok _ _ _ wf]
    rfl
  | joint ns =>
    simp only [encodePromiseWire, List.append_assoc, parsePromiseWire]
    rw [pU8_ok _ _ _ (by decide)]
    simp only [bind, Except.bind]
    rw [pVec_ok _ _ _ _ _ wf.1 (fun n hn tail => pU64_ok _ n tail (wf.2 n hn))]
    simp [bind, Except.bind, pure, Except.pure]

theorem value_wire_injective (a b : Val) (ha : valueWireWf a) (hb : valueWireWf b)
    (same : encodeValueWire a = encodeValueWire b) : a = b := by
  have h := congrArg (fun bs => parseValueWire (bs ++ [])) same
  rw [value_wire_roundtrip a ha [], value_wire_roundtrip b hb []] at h
  exact congrArg Prod.fst (Except.ok.inj h)

theorem promise_wire_injective (a b : PromiseV) (ha : promiseWireWf a) (hb : promiseWireWf b)
    (same : encodePromiseWire a = encodePromiseWire b) : a = b := by
  have h := congrArg (fun bs => parsePromiseWire (bs ++ [])) same
  rw [promise_wire_roundtrip a ha [], promise_wire_roundtrip b hb []] at h
  exact congrArg Prod.fst (Except.ok.inj h)

end NearCompression
