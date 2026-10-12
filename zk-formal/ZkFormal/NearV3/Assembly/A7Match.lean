import ZkFormal.NearV3.Assembly.A7Pre

/-!
# ZkFormal.NearV3.Assembly.A7Match — (E): the part-by-part match of the `upsV3` plan with `traceUpsert`

The open step of `A7RecordBound` is `A7Pre.UpsSegMatch` (segment level).  It splits into:

* **(E1) `UpsPartMatch`** (stated here, open): for every `upsV3` segment `s` of instance `τ` with its row layout
  `UpsLayout s L ps fls ws` and part plan `UpsPlan s ps ci ti di si kd sdx` (`ups_layout`, `ups_plan`), and the
  run `traceUpsert (Tpost r τ) [0,15] (sv τ) = some run` of the spec's upsert on the post record tree:
  `run` has exactly the plan's parts, bottom-up — part `k` has kind `UKind.all[kd k]`, output the plan's node
  `upsQ … k` (`ups_upsert` is the statement for the last part, `ups_up` for every upper part as an upsert),
  and, if its kind replaces its source (`TrieA7Repl.replK`), source `srcOf … k` (the record tree of the
  part's `sN`).
* **(E2)** (not yet stated): the A7 rows of a segment in terms of its plan — `a7S s = |sv τ| + Σ_k |nodeEnc (upsQ … k)|`
  (value-byte rows and node-part rows), the `RPL` sends are `[sN_k]` of the upper parts and `[N_D]` (the terminal
  record, the source of the terminal replacing part), the `RPLV` send is `[vid]` of the overwritten value when
  present.  With (E1) and `|ser n| = |nodeEnc (fullTree n)|` (`enc_fullTree`) this gives `UpsSegMatch`.
-/

namespace ZkFormal.NearV3.Assembly

namespace A7Match

open NearSpec NearSpecV3 Render.UpsGen ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3 ZkFormal.NearV3.UpsRows

/-- The parts of `run` are the plan's parts. -/
def PartMatch (R : List NodeRec3) (V' : List ValRec3) (s : UpsSeg) (ps : List (Nat × Nat))
    (ci ti si : Nat) (kd sdx : Nat → Nat) (val : NearSpec.Bytes) (run : TreeRun) : Prop :=
  run.parts.length = ps.length ∧
  ∀ k, k < ps.length → ∃ q : TreePart, run.parts[k]? = some q ∧
    q.kind = UKind.all.getD (kd k) .RDB ∧
    q.output = upsQ ci si ti (s.row 0 UpsV3.tX) val kd sdx (srcOf R V' s ps) k ∧
    (TrieA7Repl.replK q.kind = true → q.source = srcOf R V' s ps k)

/-- **(E1), open**: every segment's plan matches the spec's upsert run on the post record tree. -/
def UpsPartMatch (tr : Trace Fp) (r : V3Records) : Prop :=
  ∀ s ∈ r.ups, ∀ L ps fls ws ci ti di si kd sdx, UpsLayout s L ps fls ws → UpsPlan s ps ci ti di si kd sdx →
    ∀ run, traceUpsert (A7Native.Tpost r (UpsRows.upsE s).tau) UpsSpec.key
        (Link3.toB (Sched.svOf tr T_CODEC (UpsRows.upsE s).tau)) = some run →
      PartMatch (Rpost r.nodes r.values) (Vpost r.nodes r.values (fun i => Link3.toB (LinkVPost.pnOf r.accts i)))
        s ps ci ti si kd sdx (Link3.toB (Sched.svOf tr T_CODEC (UpsRows.upsE s).tau)) run

end A7Match

end ZkFormal.NearV3.Assembly
