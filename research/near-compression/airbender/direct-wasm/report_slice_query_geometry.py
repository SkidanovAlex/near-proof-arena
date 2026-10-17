#!/usr/bin/env python3
"""Exact codec geometry on retained commitments, not regenerated Q>8 proofs.
Query prefixes use the diagnostic transcript; this does not define a new profile.
"""
import argparse
import hashlib
import json
from pathlib import Path
import pq384_global_bus_codec as wire
import pq384_global_codec as pcs


def geometry(args, opening, terminal, queries):
    original = pcs.gc.QUERIES
    try:
        pcs.gc.QUERIES = queries
        stages = pcs.header(args, terminal, opening['rounds'], opening['terminal'])
        _, fixed, _ = pcs.limits(args, terminal)
        rows = []
        for stage, (_, _, count, indices, words) in enumerate(stages):
            leaves = len(set(indices)) * 4 * words
            # Independent count: each occupied parent needs two children;
            # subtract children already supplied at that level.
            occupied = set(indices)
            missing = 0
            for _ in range(count.bit_length()-1):
                parents = {i//2 for i in occupied}
                missing += 2*len(parents)-len(occupied)
                occupied = parents
            assert missing == len(pcs.mp.boundary(count, indices))
            siblings = missing * 48
            rows.append({'stage': stage, 'tree_leaves': count, 'distinct_opened_leaves': len(set(indices)),
                         'leaf_bytes': leaves, 'sibling_bytes': siblings})
        return {'queries': queries, 'fixed_bytes': fixed, 'stages': rows,
                'bytes': fixed+sum(r['leaf_bytes']+r['sibling_bytes'] for r in rows)}
    finally:
        pcs.gc.QUERIES = original


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--fixture', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    statement = json.loads((a.fixture/'statement.json').read_text())
    proof = json.loads((a.fixture/'proof.json').read_text())
    data = (a.fixture/'proof.bin').read_bytes()
    spec = statement['spec']
    roots = [bytes.fromhex(v) for v in statement['roots']]
    # Verify the retained real artifact before using its geometry.
    assert wire.verify_shared(data, spec, roots)
    assert wire.encode(proof, spec, roots) == data
    st, transcript, alpha, gamma = wire.bus.begin(spec, roots)
    aux_roots = [bytes.fromhex(v) for v in proof['aux_roots']]
    wire.bus.initialize_aux(transcript, spec, aux_roots, proof['finals'])
    branches = []
    for ti, part in enumerate(proof['tables']):
        argslist = wire.bus.verify_table_reduction(part, spec, st, transcript, alpha, gamma,
                                                  ti, proof['finals'][ti], [roots[ti], aux_roots[ti]])
        for branch, (opening, args) in enumerate(zip(part['openings'], argslist)):
            cases = [geometry(args, opening, spec['terminal_degree'], q) for q in (8, 128, 165, 239, 309, 463)]
            assert cases[0]['bytes'] == len(pcs.encode(opening, terminal_degree=spec['terminal_degree'], **args))
            branches.append({'table': ti, 'branch': branch, 'width': args['width'],
                             'packing': args['packing'], 'cases': cases})
    non_pcs = len(data)-sum(b['cases'][0]['bytes'] for b in branches)
    transport = sum((a.fixture/name).stat().st_size for name in ('statement.json', 'request.json'))
    cases = []
    for index, q in enumerate((8, 128, 165, 239, 309, 463)):
        size = non_pcs+sum(b['cases'][index]['bytes'] for b in branches)
        cases.append({'queries_per_branch': q, 'projected_proof_bytes': size,
                      'current_statement_and_request_bytes': transport,
                      'projected_current_transport_bytes': size+transport,
                      'leaf_bytes': sum(sum(s['leaf_bytes'] for s in b['cases'][index]['stages']) for b in branches),
                      'sibling_bytes': sum(sum(s['sibling_bytes'] for s in b['cases'][index]['stages']) for b in branches)})
    report = {'status': 'VERIFIED_Q8_BASELINE_AND_COUNTERFACTUAL_CODEC_GEOMETRY',
              'proof_sha256': hashlib.sha256(data).hexdigest(), 'non_pcs_bytes': non_pcs,
              'cases': cases, 'branches': branches,
              'qualifications': ['Only Q8 is an actual verified proof; other rows count exact leaf/path geometry for longer query prefixes on retained commitments.',
                                 'All rows retain Ext4 fields, Q8 transcript domain separation and current packing. No secure new protocol profile is defined.',
                                 '309 comes from a conditional ideal-interactive unique-decoding calculation; other counts are sensitivity probes, not certified security choices.',
                                 'Ext8 migration and any transcript-domain change can change both commitments and query geometry.',
                                 'Current statement/request serialization is retained; compact replacement and full NEAR scaling are unproved.']}
    a.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'non_pcs_bytes': non_pcs, 'cases': cases}, indent=2))


if __name__ == '__main__':
    main()
