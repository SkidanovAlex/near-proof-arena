# Hash-based recursion: formal research foundation

This isolated Lean 4.34.1 package starts the research requested on 2026-10-14:
an elliptic-curve-free proof system targeting 128-bit post-quantum security and
less than 300,000 transmitted proof bytes. It imports only `Std`, has no external
package dependencies, and does not modify production admission or the existing
classical ROM model.

**Status: checked logical/arithmetic foundations, coherent fixed-oracle semantics,
and finite event-measure lemmas; not a new secure proof system.** No complete
quantum adversary model, QROM reduction, collision bound, FRI/WHIR soundness
theorem, extractor, or compressed proof is supplied by this package.

## Reproduce

```sh
cd research/hash-recursion
python3 check.py
```

The script builds the package, checks that every public theorem is in
`Audit.lean`, inspects all 33 theorem dependency closures, and runs both audit and
oracle examples. It rejects dependencies outside `propext`, `Classical.choice`,
and `Quot.sound`. Proofs use kernel-checked tactics and `decide`, not
`native_decide`. No `sorry` or custom axioms are used. To run individual stages:
`lake build`, `lake env lean Audit.lean`, `lake env lean OracleChecks.lean`.

## What is proved

| Module | Result | Required interpretation |
|---|---|---|
| `Composition` | A perfectly sound existential wrapper can still accept outside the intended language | Logical counterexample; the toy inner verifier is not computationally sound |
| `Composition` | Perfect inner soundness composes; accepted false outer claims reduce pointwise to extraction failure or accepted false inner claims | The extraction/coupling hypothesis is explicit, not constructed; neither efficiency nor distributions follow from it |
| `Composition` | Resource-budget containment is transitive | Actual extracted quantum adversary costs must still be bounded |
| `Budget` | Rational error budgets add, reduction losses consume bits, and at most 2^s terms can share s slack bits | Cryptographic error inequalities and their probability union bound must be established separately |
| `Budget` | Exact exponent constraints for an assumed C*q^3/2^n template | No assertion that this template, coefficient, or query count bounds our protocol |
| `Wire` | Concatenation length equals summed section lengths; unshared Merkle-path costs and strict 300,000-byte boundaries | No soundness claim about query counts; all actual protocol framing and sections must be accounted for |
| `Oracle` | XOR hash queries are involutions, preserve linear combinations and additive pairings; density conjugation preserves trace and pure-state descriptions | Generic amplitudes and finite basis; a concrete complex Hilbert-space instance and Born-rule semantics remain to be connected |
| `Oracle` | Input dephasing destroys cross-input coherence even when trace is preserved | Shows why measuring/logging query inputs is a different operation, not an impossibility theorem for every quantum recording technique |
| `FiniteMeasure` | Event monotonicity, union bound, total-mass bound and conditional extraction-mass bound; oracle preserves input/workspace event mass | Nonnegative generic scalar weights; extracted-state distribution and coupling are still external obligations |

The useful design exclusion is exact: 216 independent depth-22 binary paths with
64-byte digests cost 304,128 bytes. Such a layout cannot meet the size target.
Shared multiproofs, caps, lower depth or fewer queries can change the conclusion.
At 128 paths the corresponding cost is 180,224 bytes, leaving strictly less than
119,776 bytes for everything else. This is a layout illustration, not a chosen
secure parameter set.

## Security contract still to select

Distinguish two objectives:

- **128-bit quantum attack cost:** define success probability, quantum query/gate
  cost, parallelism, depth, and memory conventions.
- **Failure at most 2^-128 for a bounded adversary:** fix hash/prover queries,
  time, adaptive claims and recursion depth, then prove this probability bound.

The second objective is stronger than a nominal 128-bit attack threshold when
the permitted query budget reaches that threshold. For example, the *assumed*,
coefficient-one cubic template at q=2^128 uses all of a 2^-128 failure budget with
512-bit outputs. At 384 bits it does not meet that probability bound. Conversely,
at q=2^64 and n=384 the template is 2^-192. These checked calculations do not
instantiate a quantum collision theorem or a concrete SHA construction.

## Next formal milestones

1. Extend the now-checked fixed-oracle operation to a complete finite quantum
   experiment: complex amplitudes, normalized positive states, adversary gates,
   measurements, uniformly random functions and an accepted-false-statement
   event. Connect Born probabilities to `FiniteMeasure` and then to the rational
   upper bounds in `Budget`; the probabilities themselves need not be rational.
   Reusing a classical lazy oracle transcript is not a valid replacement.
2. Pin the exact interactive polynomial protocol and prove its applicable
   soundness notion. Compare the existing unique-decoding algebra with a
   WHIR-based candidate; do not replace proven bounds with conjectured ones.
3. Formalize an applicable quantum Fiat–Shamir reduction with explicit constants,
   rounds and query budgets. Do not assume a single quadratic loss covers an
   arbitrary multi-round protocol.
4. Construct the quantum extraction/composition reduction. Prove the coupling
   and resource hypotheses needed by `extraction_event_inclusion`, or replace
   that interface with the distributional reduction actually obtained. Track
   the extracted adversary's costs and statement binding, including v3 hint
   preprocessing. QROM soundness alone is not knowledge extraction.
5. Instantiate commitment/hash assumptions, calculate the full security budget,
   then connect a concrete serializer to the wire model. Only then claim a
   security/size parameter set; an actual proof benchmark follows.

The scheme may be new while using established hash primitives. SHA-256 domain
separation or a wider concatenated digest is not assumed to realize an ideal
wide quantum random oracle. The chain's existing SHA-256 roots and Ed25519
authentication remain separate from the proof system's security scope.

## Coherent-oracle validation

`OracleChecks.lean` uses a complete four-element basis for one input and one
response qubit. Querying the identity function on the density matrix of
`|+> tensor |0>` gives the Bell-state density matrix: diagonal entries 1/2 on
`00` and `11`, zero on `01` and `10`, and off-diagonal entries 1/2 between
`00` and `11`. Input dephasing removes those off-diagonal entries. Both matrices
have trace one, and a second coherent query restores the original matrix.
All these checks are exact, with rational entries; generic library amplitudes
are not restricted to rational values. Positivity and full measurement semantics
are not formalized by these examples.

## Research basis

- [On Soundness Notions for Interactive Oracle Proofs](https://eprint.iacr.org/2023/1256)
  supplies QROM soundness results under specified hypotheses and distinguishes
  soundness from knowledge soundness. It is not a checked dependency here.
- [Measure-and-Reprogram 2.0](https://eprint.iacr.org/2020/282) studies quantum
  Fiat–Shamir reductions, including multi-round losses.
- [Concrete Security of Non-interactive FRI](https://eprint.iacr.org/2024/1161)
  documents substantial differences between proven and conjectured parameters.
- [WHIR](https://eprint.iacr.org/2024/1586) motivates evaluating a smaller-query
  polynomial commitment layer; its reported 100-bit example does not certify
  this project's quantum target.
- [Quantum collision query complexity](https://arxiv.org/abs/1312.1027) motivates
  studying cubic-query bounds. Asymptotic complexity is not an exact concrete
  upper bound with coefficient one.
- [How to Record Quantum Queries](https://eprint.iacr.org/2018/276) motivates
  treating coherent access explicitly. Its compressed-oracle technique is not
  implemented or proved here; naive input measurement is not that technique.

See also `../../docs/research/recursive-compression.md` for the earlier execution
measurements and unresolved concrete-hash composition obligations.
