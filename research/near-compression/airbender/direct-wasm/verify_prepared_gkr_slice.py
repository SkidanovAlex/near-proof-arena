"""Literal Wasm eligibility plus compact GKR/weighted PCS diagnostic.

Uses the same request and locally reconstructed AIR checks as the direct slice.
Codec selection is fixed by this entrypoint, never a proof/statement field.
Acceptance-to-HoldsP, joint extraction and quantum soundness remain unproved.
"""
import argparse
import json
from pathlib import Path
from types import SimpleNamespace
import pq384_compact_gkr_bus_codec as codec
from verify_prepared_slice import verify as verify_literal


def verify(wire, statement, request, *, input_log=None):
    selected = codec.bus.profile(input_log)
    configured = SimpleNamespace(bus=codec.bus,
        decode=lambda wire, spec, roots: codec.decode(wire, spec, roots, input_log=input_log))
    result = verify_literal(wire, statement, request, proof_codec=configured)
    return dict(result, profile=selected)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('proof', 'statement', 'request'):
        parser.add_argument(name, type=Path)
    parser.add_argument("--input-log", type=int, help="trusted caller cap for fixed-input profile")
    args = parser.parse_args()
    print(json.dumps(verify(args.proof.read_bytes(), json.loads(args.statement.read_text()),
                            json.loads(args.request.read_text()), input_log=args.input_log)))
