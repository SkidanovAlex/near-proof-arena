"""Transport roundtrip, caller binding, malformed framing and proof integrity."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import struct
import subprocess
import sys
import prepared_gkr_envelope as envelope


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--fixture', type=Path, required=True)
    args = ap.parse_args()
    fixture = args.fixture
    proof = (fixture/'proof.bin').read_bytes()
    statement = json.loads((fixture/'statement.json').read_text())
    request = json.loads((fixture/'request.json').read_text())
    wire = envelope.encode(proof, statement, request)
    assert envelope.decode(wire) == (proof, statement, request)
    output = fixture/'envelope.bin'
    output.write_bytes(wire)
    fresh = subprocess.run([sys.executable, str(Path(envelope.__file__)), str(output),
                            str(fixture/'request.json')], check=True, capture_output=True, text=True)
    assert json.loads(fresh.stdout)['status'] == 'PASS'
    rejected = []
    def reject(name, data, expected=request):
        try:
            envelope.verify(data, expected)
        except (ValueError, UnicodeError, subprocess.CalledProcessError):
            rejected.append(name)
        else:
            raise AssertionError(name+' accepted')
    reject('truncation', wire[:-1])
    reject('trailing byte', wire+b'\0')
    reject('wrong envelope profile', b'X'+wire[1:])
    bad = bytearray(wire); struct.pack_into('<I', bad, len(envelope.MAGIC), 0xffffffff)
    reject('oversized public length', bytes(bad))
    bad = bytearray(wire); struct.pack_into('<I', bad, len(envelope.MAGIC)+4, envelope.P)
    reject('noncanonical public field', bytes(bad))
    shape_offset = len(envelope.MAGIC)+4+4*len(statement['spec']['public'])
    bad = bytearray(wire); struct.pack_into('<I', bad, shape_offset+2, 0)
    reject('zero source packing', bytes(bad))
    root_offset = shape_offset+2+16+1
    bad = bytearray(wire); bad[root_offset] ^= 1
    reject('substituted source root', bytes(bad))
    method_offset = root_offset+96+4+len(request['wasm_bytes'])+4
    bad = bytearray(wire); bad[method_offset] = 255
    reject('invalid method UTF8', bytes(bad))
    proof_length_offset = method_offset+len(request['method'].encode('utf-8'))+8
    bad = bytearray(wire); struct.pack_into('<Q', bad, proof_length_offset, (1 << 64)-1)
    reject('oversized proof length', bytes(bad))
    for key, value in (('method', 'different'), ('prepaid', request['prepaid']-1),
                       ('wasm_bytes', request['wasm_bytes']+[0])):
        changed = copy.deepcopy(request); changed[key] = value
        reject('caller '+key+' mismatch', wire, changed)
    bad = bytearray(wire); bad[-1] ^= 1
    reject('corrupt embedded proof', bytes(bad))
    # Valid field encoding but changed published output: must fail cryptographic binding.
    bad = bytearray(wire)
    pos = len(envelope.MAGIC)+4+4*43
    struct.pack_into('<I', bad, pos, statement['spec']['public'][43]^1)
    reject('altered published output', bytes(bad))
    report = {'status':'PASS', 'proof_bytes':len(proof), 'envelope_bytes':len(wire),
              'envelope_overhead_bytes':len(wire)-len(proof),
              'prior_transport_bytes':sum((fixture/n).stat().st_size for n in ('proof.bin','statement.json','request.json')),
              'envelope_plus_separately_supplied_expected_request_json_bytes':len(wire)+(fixture/'request.json').stat().st_size,
              'exact_statement_request_proof_roundtrip':True, 'fresh_verifier':json.loads(fresh.stdout),
              'rejections':rejected, 'sha256':hashlib.sha256(wire).hexdigest(),
              'limits':['Q8/Ext4 diagnostic; transport-only change.',
                        'All inputs are carried; AIR is reconstructed. Caller request must be externally pinned.',
                        'No acceptance-to-HoldsP, quantum-security or full-NEAR certification.']}
    (fixture/'envelope-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
