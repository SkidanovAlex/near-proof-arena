#!/usr/bin/env python3
"""Finish the scheduled diagnostic proof from prepared real D1 commitments.

The independent verifier receives only proof, expected AIR/public spec and roots.
This is not a secure production profile or a 1 Pgas performance benchmark.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

import native_folded
import scheduled_bus_whir as protocol
from verify_whir_toy import ext


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('prepared', type=Path)
    ap.add_argument('opening_binary', type=Path)
    ap.add_argument('output', type=Path)
    ap.add_argument('--native-v2', action='store_true', help='use native matrix operations in shift reduction')
    args = ap.parse_args()
    if args.native_v2:
        import native_folded_v2 as backend
    else:
        backend = native_folded
    source = args.prepared.resolve(); out = args.output.resolve()
    out.mkdir(exist_ok=False)
    started = time.monotonic()
    def read(name): return json.loads((source/name).read_text())
    def save(name, value):
        path = out/name
        path.write_text(json.dumps(value, separators=(',', ':'))+'\n')
        return path
    spec = read('spec.json'); inputs = read('prover-input.json')
    protocol.validate(spec)
    roots, aux_roots = inputs['roots'], inputs['aux_roots']
    rows, aux_rows = [], []
    for ti in range(len(spec['air']['tables'])):
        rows.append(read(f'source-{ti:02}-rows.json')['rows'])
        coordinates = read(f'aux-{ti:02}-rows.json')['rows']
        aux_rows.append([[tuple(row[i:i+4]) for i in range(0,len(row),4)] for row in coordinates])
    finals = [[ext(v) for v in row] for row in inputs['finals']]
    def checkpoint(ti, proof, handoffs):
        save('partial-proof.json', proof)
        save('partial-handoffs.json', handoffs)
        print(f'constraint and cyclic-shift proof table {ti} complete; {time.monotonic()-started:.2f}s', flush=True)
    proof, handoffs = backend.prove(spec, roots, rows, aux_roots, aux_rows, finals,
                                        protocol_impl=protocol, checkpoint=checkpoint)
    constraint_seconds = time.monotonic()-started
    del rows, aux_rows
    opening_bytes = 0
    for ti, table in enumerate(proof['tables']):
        openings = []
        for branch, name in enumerate(('source', 'aux')):
            handoff = save(f'handoff-{ti:02}-{branch}.json', handoffs[ti][branch])
            path = out/f'opening-{ti:02}-{branch}.json'
            subprocess.run([str(args.opening_binary.resolve()), str(source/f'{name}-{ti:02}-rows.json'),
                            str(path), str(handoff)], check=True, stdout=subprocess.DEVNULL)
            opening = json.loads(path.read_text())
            opening_bytes += opening['bincode_bytes']
            openings.append(opening)
        table['openings'] = openings
        print(f'PCS openings table {ti} complete', flush=True)
    path = save('proof.json', proof)
    verify_started = time.monotonic()
    if protocol.verify(proof, spec, roots) is not True:
        raise ValueError('independent proof verification failed')
    verification_seconds = time.monotonic()-verify_started
    save('verified.json', {
        'status': 'PASS', 'tables': len(proof['tables']),
        'constraint_and_shift_seconds': constraint_seconds,
        'total_seconds': time.monotonic()-started, 'verification_seconds': verification_seconds,
        'complete_proof_json_bytes': path.stat().st_size,
        'opening_payload_bytes_not_complete_proof': opening_bytes,
        'proof_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
        'verifier_external_witness_used': False, 'security_bits_claimed': None,
        'limitations': ['Diagnostic BLAKE2s/BabyBearExt4 profile, not 128-bit post-quantum security.',
                       'Two-row tables disclose their full rows inside the proof; not zero knowledge.',
                       'One small D1 fixture, not full NEAR or a 1 Pgas benchmark.',
                       'No recursive compression or complete Lean verifier refinement.']})
    print('PASS: complete diagnostic D1 proof independently verified', flush=True)


if __name__ == '__main__':
    main()
