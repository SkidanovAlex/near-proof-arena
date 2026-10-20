#!/usr/bin/env python3
"""Independently verify a scheduled D1 diagnostic proof without a witness.

The expected AIR/public specification and original source roots are separate
inputs. This verifier does not establish a cryptographic security level.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import scheduled_bus_whir as protocol


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('proof', type=Path)
    ap.add_argument('expected_spec', type=Path)
    ap.add_argument('expected_statement', type=Path)
    ap.add_argument('--report', type=Path)
    ap.add_argument('--binary', action='store_true', help='decode canonical shared-vector V2 container')
    args = ap.parse_args()
    data = args.proof.read_bytes()
    if args.binary:
        from scheduled_proof_codec_shared import decode
        proof = decode(data)
    else:
        proof = json.loads(data)
    spec = json.loads(args.expected_spec.read_text())
    statement = json.loads(args.expected_statement.read_text())
    started = time.monotonic()
    if protocol.verify(proof, spec, statement['roots']) is not True:
        raise ValueError('proof verification failed')
    result = {'status': 'PASS', 'tables': len(spec['air']['tables']),
              'verification_seconds': time.monotonic()-started,
              'complete_proof_bytes': len(data),
              'encoding': 'shared-vector-v2' if args.binary else 'json',
              'proof_sha256': hashlib.sha256(data).hexdigest(),
              'external_witness_read': False, 'security_bits_claimed': None,
              'scope': 'Independent diagnostic verification; not a security or full NEAR coverage certificate.'}
    if args.report: args.report.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
