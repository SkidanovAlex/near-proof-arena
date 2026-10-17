"""Configured seed-profile verifier preserving the fixed committed-input statement.

Expanded diagnostic proof, not a recursive proof or secure parameter profile.
The mandatory expected input receipt is supplied by the caller, never the proof.
"""
import argparse
import hashlib
import json
from pathlib import Path

import pq384_seed_gkr_bus as bus
from packed_claim_handoff import packing_context
from pq384_primitives import require
from verify_sha384_direct import PROFILE, canonical, check_public


def verify(proof, statement, expected):
    require(type(expected) is dict and set(expected) == {
        'profile', 'declared_length', 'air_sha384', 'input_root', 'input_context_hex'},
        'required external input receipt')
    require(expected['profile'] == PROFILE and type(expected['declared_length']) is int
            and expected['declared_length'] == 376, 'restricted committed-input context')
    spec = statement['spec']
    roots = [bytes.fromhex(r) for r in statement['roots']]
    require(len(roots) == 3 and len(spec['air']['tables']) == 3, 'committed-input table layout')
    require(spec['air']['numPub'] == 88, 'committed-input public layout')
    check_public(spec['public'])
    require(spec['air']['tables'][2]['width'] == 8 * expected['declared_length']
            and spec['log_rows'][2] == 1, 'declared input shape')
    require(hashlib.sha384(canonical(spec['air'])).hexdigest() == expected['air_sha384'],
            'trusted canonical AIR/framing/padding binding')
    root = bytes.fromhex(expected['input_root'])
    require(len(root) == 48 and roots[2] == root, 'externally fixed input root')
    context = packing_context(spec['log_rows'][2], spec['air']['tables'][2]['width'],
                              spec['source_packings'][2])
    require(context.hex() == expected['input_context_hex'], 'externally fixed input context')
    # Configuration is derived only after matching the caller-fixed AIR digest.
    # Setup hashing remains counted; no prover-supplied configuration is accepted.
    config = bus.configure(spec['air'])
    return bus.verify(proof, spec, roots, config)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('proof', type=Path)
    ap.add_argument('statement', type=Path)
    ap.add_argument('expected_input', type=Path)
    args = ap.parse_args()
    verify(*(json.loads(p.read_text()) for p in
             (args.proof, args.statement, args.expected_input)))
    print('PASS: configured seed SHA384 component with mandatory trusted input receipt')


if __name__ == '__main__':
    main()
