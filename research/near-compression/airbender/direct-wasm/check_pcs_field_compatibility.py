#!/usr/bin/env python3
"""Source-pinned adapter feasibility audit; not a PCS soundness proof."""
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "results/swirl-security-review/pcs-field-compatibility"
SOURCES = [
    (Path('/tmp/nearproof-binius64'), '4428e759dd27956bd5b9ae5025d67eb8ccc1accf',
     'crates/iop/src/channel/mod.rs', ['IOPVerifierChannel<F: Field>', 'verify_oracle_relation']),
    (Path('/tmp/nearproof-binius64'), '4428e759dd27956bd5b9ae5025d67eb8ccc1accf',
     'crates/iop/src/fri/fold.rs', ['NTT: AdditiveNTT', 'v += u;', 'u += v * t;']),
    (Path('/home/illia/.cargo/git/checkouts/stark-backend-708f1155344bec0c/d667af5'),
     'd667af5929d0ea9e5194adf639d6bddeb8c10f9a',
     'crates/stark-backend/src/verifier/whir.rs',
     ['binary_k_fold<F: TwoAdicField', 'F::two_adic_generator(k)', 't_inv.halve()']),
]


def mul(a, b):
    """GF(16), polynomial basis modulo X^4+X+1."""
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a & 16:
            a ^= 19
    return r


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    sources = []
    for i, (repo, pin, rel, needles) in enumerate(SOURCES):
        head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
        assert head == pin, (head, pin)
        data = (repo / rel).read_bytes()
        # These specific files must match upstream, even though other checkout files are patched.
        original = subprocess.check_output(['git', 'show', f'{pin}:{rel}'], cwd=repo)
        assert data == original, rel
        source = data.decode()
        assert all(n in source for n in needles), rel
        (OUT / f'source-{i}.rs.txt').write_bytes(data)
        sources.append(dict(commit=pin, path=rel, sha256=hashlib.sha256(data).hexdigest(),
                            anchors=needles))

    # Exhaustive finite-field sanity checks, not a general WHIR impossibility claim.
    assert all(any(mul(a, b) == 1 for b in range(1, 16)) for a in range(1, 16))
    additive_cases = 0
    for a in range(16):
        for b in range(16):
            for t in range(16):
                # Encode a linear polynomial at the distinct points t and t+1.
                u, v = a ^ mul(b, t), a ^ mul(b, t ^ 1)
                recovered_b = v ^ u
                recovered_a = u ^ mul(recovered_b, t)
                assert (recovered_a, recovered_b) == (a, b)
                additive_cases += 1
    assert all((x ^ x) == 0 for x in range(16))
    assert all(mul(0, x) != 1 for x in range(16))  # no inverse of two=zero
    assert [x for x in range(16) if mul(x, x) == 1] == [1]
    report = dict(
        sources=sources, additive_pair_cases=additive_cases,
        binary_characteristic_two=True, invertible_two=False,
        distinct_multiplicative_order_two_element=False,
        decision='Do not implement an unchanged SWIRL-WHIR backend swap into Binius.',
        scope='Inspected implementations only; does not rule out additive-domain WHIR designs.',
        obligations=[
            'Preserve oracle padding, arbitrary linear relations, commitment chronology and batching.',
            'Supply characteristic-two encoding, folding, domain transitions and OOD reductions.',
            'Prove proximity and adaptive composition bounds for the actual new construction.',
            'Implement prover/verifier and measure complete proof plus public inputs.',
            'Account for field, hash, Fiat-Shamir/QROM and recursive composition errors.',
            'A smaller PCS does not remove the measured prime-field arithmetic lowering cost.',
        ],
    )
    (OUT / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
