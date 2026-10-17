"""Pinned literal Wasm slice frontend. Q8/Ext4 diagnostic, not PQ certified.

Caller supplies the intended Wasm bytes/method/prepaid gas. Preparation runs in
Lean; execution does not. AIR is reconstructed locally, not trusted from the
proof statement. Roots are prover commitments, bound by the proof transcript.
The remaining acceptance-to-HoldsP reduction is not proved by this wrapper.
"""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

import prepared_code_table_air as literal
import pq384_global_bus_codec as codec

PACKAGE = Path(__file__).resolve().parents[2]


def verify(wire, statement, request, *, proof_codec=codec):
    if set(request) != {'wasm_bytes', 'method', 'prepaid'}:
        raise ValueError('request fields')
    if (not isinstance(request['wasm_bytes'], list) or
        not all(type(x) is int and 0 <= x < 256 for x in request['wasm_bytes']) or
        type(request['method']) is not str or type(request['prepaid']) is not int or
        request['prepaid'] < 0):
        raise ValueError('request types')
    if set(statement) != {'spec', 'roots'}:
        raise ValueError('statement fields')
    spec = statement['spec']
    proof_codec.bus.validate(spec)
    public = spec['public']
    count, remainder = divmod(len(public) - literal.CODEPUB, literal.RECORD)
    if count <= 0 or remainder or spec['air'] != literal.air(count):
        raise ValueError('expected literal execution/CODE AIR')
    with tempfile.TemporaryDirectory(prefix='near-slice-check-') as tmp:
        inp = Path(tmp) / 'input.json'
        inp.write_text(json.dumps(dict(request=request, public=public)))
        checked = subprocess.run(['lake', 'env', 'lean', '--run', 'PreparedSliceCheck.lean', str(inp)],
                                 cwd=PACKAGE, capture_output=True, text=True, check=True)
        eligibility = json.loads(checked.stdout)
    if eligibility != dict(status='PASS', code_length=count):
        raise ValueError('prepared code length mismatch')
    roots = [bytes.fromhex(r) for r in statement['roots']]
    proof_codec.decode(wire, spec, roots)
    return dict(status='PASS', security='Q8/Ext4 diagnostic; soundness not certified',
                code_length=count, execution_fuel=1 << spec['log_rows'][0],
                published_exit=public[39:66])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('proof', type=Path)
    parser.add_argument('statement', type=Path)
    parser.add_argument('request', type=Path)
    args = parser.parse_args()
    print(json.dumps(verify(args.proof.read_bytes(), json.loads(args.statement.read_text()),
                            json.loads(args.request.read_text()))))


if __name__ == '__main__':
    main()
