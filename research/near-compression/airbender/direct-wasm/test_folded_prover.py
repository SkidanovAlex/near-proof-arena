#!/usr/bin/env python3
"""Exact transcript parity against exhaustive prover plus existing real PCS."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import time
import folded_prover as fast
import heterogeneous_bus_whir as reference
from verify_whir_toy import ext


def main():
    out = Path(__file__).resolve().parents[2] / 'results'
    spec = json.loads((out/'heterogeneous-bus-spec.json').read_text())
    proof = json.loads((out/'heterogeneous-bus-proof.json').read_text())
    roots = json.loads((out/'heterogeneous-bus-statement.json').read_text())['roots']
    source = [json.loads((out/f'heterogeneous-bus-source-{i}.json').read_text())['rows'] for i in range(2)]
    coordinates = [json.loads((out/f'heterogeneous-bus-aux-{i}.json').read_text())['rows'] for i in range(2)]
    auxiliary = [[[tuple(row[j:j+4]) for j in range(0, len(row), 4)] for row in rows] for rows in coordinates]
    finals = [[ext(v) for v in fs] for fs in proof['finals']]
    generated, handoffs = fast.prove(spec, roots, source, proof['aux_roots'], auxiliary, finals)
    for ti, part in enumerate(generated['tables']):
        part['openings'] = proof['tables'][ti]['openings']
        for branch in range(2):
            expected = json.loads((out/f'heterogeneous-bus-handoff-{ti}-{branch}.json').read_text())
            assert handoffs[ti][branch] == expected
    assert generated == proof
    assert reference.verify(generated, spec, roots)
    timings = []
    for n in (3, 4, 5):
        s = deepcopy(spec)
        s['log_rows'] = [n, n]
        count = 2**n
        s['public'] = [count, 0, 0, 0] + list(range(10, 10+count))
        s['air']['maxPub'] = len(s['public'])
        for table in s['air']['tables']:
            table['maxLog'] = n
        rows = [[[10+i, int(i < count//2)] for i in range(count)] for _ in range(2)]
        # Placeholder commitments ONLY for prover-algorithm parity, not PCS acceptance.
        r = [[ti+1]*8 for ti in range(2)]
        ar = [[ti+3]*8 for ti in range(2)]
        _, _, alpha, gamma = reference.begin(s, r)
        aux = [reference.aux.generate(t, rs, s['public'], alpha, gamma)
               for t, rs in zip(s['air']['tables'], rows)]
        args = (s, r, rows, ar, [a['aux_rows'] for a in aux], [a['finals'] for a in aux])
        start = time.perf_counter()
        expected = reference.prove(*args)
        baseline = time.perf_counter()-start
        start = time.perf_counter()
        actual = fast.prove(*args)
        optimized = time.perf_counter()-start
        assert actual == expected
        timings.append({'rows_per_table': count, 'reference_seconds': baseline,
                        'folded_seconds': optimized, 'speedup': baseline/optimized,
                        'proof_and_handoff_identical': True})
    src = Path(__file__).resolve().parent/'folded_prover.py'
    report = {'status': 'PASS', 'real_heterogeneous_proof_identical': True,
              'existing_four_whir_openings_verified': True, 'verifier_modified': False,
              'benchmarks': timings, 'sha256': hashlib.sha256(src.read_bytes()).hexdigest(),
              'limitations': ['Tiny Python benchmarks; no full D1 or1Pgas throughput claim.',
                             'Extra benchmark cases compare prover algorithms with placeholder roots; only saved8/16rowcase has actualPCS verification.',
                             'Runtime parity plus algebra lemmas are not full implementation refinement.']}
    (out/'folded-prover-verified.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
