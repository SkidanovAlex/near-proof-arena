import NearCompression.ValueWire

/-! Control labels and frames with exact locals and ordered labels. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def encodeBoolWire (b : Bool) : Bytes := u8 (if b then 1 else 0)

theorem bool_wire_roundtrip (b : Bool) (rest : Bytes) :
    pBool "loop" (encodeBoolWire b ++ rest) = .ok (b, rest) := by
  cases b <;> simp only [encodeBoolWire, Bool.false_eq_true, ite_false, ite_true, pBool]
  all_goals rw [pU8_ok _ _ _ (by decide)]
  all_goals rfl

def labelWireWf (l : Label) : Prop :=
  l.target < 18446744073709551616 ∧ l.arity < 18446744073709551616 ∧
    l.height < 18446744073709551616

def encodeLabelWire (l : Label) : Bytes :=
  u64 l.target ++ u64 l.arity ++ u64 l.height ++ encodeBoolWire l.isLoop

def parseLabelWire : NearSpecV3.P Label := fun bs => do
  let (target, bs) ← pU64 "target" bs
  let (arity, bs) ← pU64 "arity" bs
  let (height, bs) ← pU64 "height" bs
  let (isLoop, bs) ← pBool "loop" bs
  pure (⟨target, arity, height, isLoop⟩, bs)

theorem label_wire_roundtrip (l : Label) (wf : labelWireWf l) (rest : Bytes) :
    parseLabelWire (encodeLabelWire l ++ rest) = .ok (l, rest) := by
  simp only [parseLabelWire, encodeLabelWire, List.append_assoc]
  rw [pU64_ok _ _ _ wf.1]
  simp only [bind, Except.bind]
  rw [pU64_ok _ _ _ wf.2.1]
  simp only [bind, Except.bind]
  rw [pU64_ok _ _ _ wf.2.2]
  simp only [bind, Except.bind]
  rw [bool_wire_roundtrip]
  rfl

def frameWireWf (f : Frame) : Prop :=
  f.fn < 18446744073709551616 ∧ f.pc < 18446744073709551616 ∧
  stackWireWf f.locals ∧ f.labels.length < 4294967296 ∧
  (∀ l ∈ f.labels, labelWireWf l) ∧ f.base < 18446744073709551616

def encodeFrameWire (f : Frame) : Bytes :=
  u64 f.fn ++ u64 f.pc ++ encodeStackWire f.locals ++
    encList encodeLabelWire f.labels ++ u64 f.base

def parseFrameWire : NearSpecV3.P Frame := fun bs => do
  let (fn, bs) ← pU64 "function" bs
  let (pc, bs) ← pU64 "pc" bs
  let (locals, bs) ← parseStackWire bs
  let (labels, bs) ← pVec "labels" parseLabelWire bs
  let (base, bs) ← pU64 "base" bs
  pure (⟨fn, pc, locals, labels, base⟩, bs)

theorem frame_wire_roundtrip (f : Frame) (wf : frameWireWf f) (rest : Bytes) :
    parseFrameWire (encodeFrameWire f ++ rest) = .ok (f, rest) := by
  obtain ⟨hfn, hpc, hlocals, hlen, hlabels, hbase⟩ := wf
  simp only [parseFrameWire, encodeFrameWire, List.append_assoc]
  rw [pU64_ok _ _ _ hfn]
  simp only [bind, Except.bind]
  rw [pU64_ok _ _ _ hpc]
  simp only [bind, Except.bind]
  rw [stack_wire_roundtrip _ hlocals]
  simp only [bind, Except.bind]
  rw [pVec_ok _ _ _ _ _ hlen (fun l hl tail => label_wire_roundtrip l (hlabels l hl) tail)]
  simp only [bind, Except.bind]
  rw [pU64_ok _ _ _ hbase]
  rfl

def framesWireWf (fs : List Frame) : Prop :=
  fs.length < 4294967296 ∧ ∀ f ∈ fs, frameWireWf f

def encodeFramesWire (fs : List Frame) : Bytes := encList encodeFrameWire fs

def parseFramesWire : NearSpecV3.P (List Frame) := pVec "frames" parseFrameWire

theorem frames_wire_roundtrip (fs : List Frame) (wf : framesWireWf fs) (rest : Bytes) :
    parseFramesWire (encodeFramesWire fs ++ rest) = .ok (fs, rest) :=
  pVec_ok _ _ _ _ _ wf.1 (fun f hf tail => frame_wire_roundtrip f (wf.2 f hf) tail)

theorem frame_wire_injective (a b : Frame) (ha : frameWireWf a) (hb : frameWireWf b)
    (same : encodeFrameWire a = encodeFrameWire b) : a = b := by
  have h := congrArg (fun bs => parseFrameWire (bs ++ [])) same
  rw [frame_wire_roundtrip a ha [], frame_wire_roundtrip b hb []] at h
  exact congrArg Prod.fst (Except.ok.inj h)

end NearCompression
