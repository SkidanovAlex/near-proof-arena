"""Authenticate every actual shared Merkle DAG once and measure reference work.

This isolates Merkle authentication, not the whole verifier. The unchanged
full verifier is also run. No circuit implementation or gate claim is made.
"""
import argparse
import json
from pathlib import Path
import pq384_global_bus as bus
import pq384_global_codec as pcs
from pq384_primitives import field_words
from profile_pq384_verifier import measure


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('directory', type=Path)
    ap.add_argument('output', type=Path)
    args = ap.parse_args()
    proof = json.loads((args.directory / 'proof.json').read_text())
    statement = json.loads((args.directory / 'statement.json').read_text())
    spec = statement['spec']
    roots = [bytes.fromhex(v) for v in statement['roots']]
    assert bus.verify(proof, spec, roots)
    st, transcript, alpha, gamma = bus.begin(spec, roots)
    aux_roots = [bytes.fromhex(v) for v in proof['aux_roots']]
    bus.initialize_aux(transcript, spec, aux_roots, proof['finals'])
    jobs = []
    for ti, part in enumerate(proof['tables']):
        branches = bus.verify_table_reduction(part, spec, st, transcript,
            alpha, gamma, ti, proof['finals'][ti], [roots[ti], aux_roots[ti]])
        for opening, branch in zip(part['openings'], branches):
            stages = pcs.header(branch, spec['terminal_degree'],
                                opening['rounds'], opening['terminal'])
            for j, (root, context, count, indices, words) in enumerate(stages):
                queries = [chain[0]['source'] if j == 0 else chain[j-1]['next']
                           for chain in opening['queries']]
                leaves = [field_words(q['leaf']) for q in queries]
                paths = [[bytes.fromhex(v) for v in q['path']] for q in queries]
                shared = pcs.mp.compress(root, context, count, indices, leaves, paths)
                jobs.append((root, context, count, indices, shared, leaves, paths))

    def authenticate():
        for root, context, count, indices, shared, leaves, paths in jobs:
            assert pcs.mp.expand(root, context, count, indices, shared) == (leaves, paths)
        return True

    work = measure(authenticate)
    report = dict(status='PASS', stages=len(jobs),
        shared_merkle_authentication=work,
        scope='All actual shared-stage proofs authenticate once and expand exactly to full-verifier paths; full original verifier also passes.',
        limits=[
            'Excludes AIR, shift, transcript, terminal disclosure and fold relation verification.',
            'Not yet integrated as a verifier replacing expanded path checks.',
            'Exact reference hash work, not circuit gate counts or a recursive proof.',
            'Diagnostic Q8/Ext4 parameters unchanged.'])
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
