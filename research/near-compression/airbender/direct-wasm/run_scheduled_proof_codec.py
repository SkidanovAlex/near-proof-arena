#!/usr/bin/env python3
"""Roundtrip complete scheduled-bus proofs, verify decoded proofs, report bytes."""
import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import struct
import scheduled_proof_codec as codec
from scheduled_bus_whir import verify


def decomposition(proof):
    empty = {'aux_roots': [], 'finals': [], 'tables': []}
    baseline = len(codec.encode(empty))
    def size(value):
        return len(codec.encode({**empty, 'tables': [value]})) - baseline
    tables = []
    for ti, part in enumerate(proof['tables']):
        record = {'table': ti, 'encoded_bytes': size(part),
                  'constraint_rounds_bytes': size(part['constraint_rounds']),
                  'shift_reduction_bytes': size(part['shift_reduction']),
                  'openings_bytes': size(part['openings'])}
        record['table_object_overhead_bytes'] = record['encoded_bytes'] - sum(
            record[k] for k in ('constraint_rounds_bytes', 'shift_reduction_bytes', 'openings_bytes'))
        tables.append(record)
    roots = size(proof['aux_roots']); finals = size(proof['finals'])
    total = len(codec.encode(proof))
    return {'complete_binary_bytes': total, 'aux_roots_bytes': roots, 'finals_bytes': finals,
            'outer_container_overhead_bytes': total-roots-finals-sum(t['encoded_bytes'] for t in tables),
            'tables': tables}


def malformed_tests(proof, blob):
    rejected = 0
    def reject(call):
        nonlocal rejected
        try: call()
        except ValueError: rejected += 1
        else: raise AssertionError('malformed codec input accepted')
    cuts = sorted(set(range(min(64, len(blob)))) | set(range(0, len(blob), max(1,len(blob)//128))) | {len(blob)-1})
    for i in cuts: reject(lambda i=i: codec.decode(blob[:i]))
    reject(lambda: codec.decode(blob+b'\x00'))
    reject(lambda: codec.decode(b'BADMAGIC'+blob[8:]))
    reject(lambda: codec.decode(codec.MAGIC+b'\xff'))
    reject(lambda: codec.decode(codec.MAGIC+b'\x0a'+struct.pack('<I',0)))
    reject(lambda: codec.decode(codec.MAGIC+b'\x06'+struct.pack('<I',2**32-1)))
    reject(lambda: codec.decode(codec.MAGIC+b'\x07'+struct.pack('<I',2**32-1)))
    reject(lambda: codec.decode(codec.MAGIC+b'\x09'+struct.pack('<4I',codec.P,0,0,0)))
    reject(lambda: codec.decode(codec.MAGIC+b'\x04'+struct.pack('<Q',1)))
    reject(lambda: codec.decode(codec.MAGIC+b'\x08'+struct.pack('<I',0)))
    # At the envelope, duplicated/descending key IDs and an unknown key ID.
    reject(lambda: codec.decode(codec.MAGIC+b'\x07'+struct.pack('<I',2)+b'\x01\x00\x01\x00'))
    reject(lambda: codec.decode(codec.MAGIC+b'\x07'+struct.pack('<I',1)+b'\xff\x00'))
    bad = deepcopy(proof); bad['extra'] = 0; reject(lambda: codec.encode(bad))
    bad = deepcopy(proof); bad['finals'] = [-1]; reject(lambda: codec.encode(bad))
    bad = deepcopy(proof); bad['finals'] = [2**64]; reject(lambda: codec.encode(bad))
    bad = deepcopy(proof); bad['finals'] = [{'c0':{'c0':codec.P,'c1':0},'c1':{'c0':0,'c1':0}}]
    reject(lambda: codec.encode(bad))
    # A generic list of u32s has an alternate packed canonical representation.
    k = codec.KEY_IDS
    alternate = (codec.MAGIC+b'\x07'+struct.pack('<I',3)+bytes([k['aux_roots']])+b'\x06'+struct.pack('<I',1)+b'\x03'+struct.pack('<I',0)
                 +bytes([k['finals']])+b'\x06'+struct.pack('<I',0)+bytes([k['tables']])+b'\x06'+struct.pack('<I',0))
    reject(lambda: codec.decode(alternate))
    if codec.MAGIC[6] == 2:
        sample = {'aux_roots': [[1, 2], [1, 2]], 'finals': [], 'tables': []}
        b = codec.encode(sample)
        assert codec.decode(b) == sample
        at = b.index(b'\x0a' + struct.pack('<I', 0))
        reject(lambda: codec.decode(b[:at] + b'\x0a' + struct.pack('<I', 1) + b[at+5:]))
        reject(lambda: codec.decode(b[:at] + b'\x08' + struct.pack('<3I', 2, 1, 2) + b[at+5:]))
        reject(lambda: codec.decode(b[:at+4]))
        saved = codec.MAX_NODES
        try:
            codec.MAX_NODES = 8
            reject(lambda: codec.decode(b))
        finally:
            codec.MAX_NODES = saved
    return rejected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('proof',type=Path); parser.add_argument('spec',type=Path)
    parser.add_argument('statement',type=Path,help='JSON containing trusted roots')
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--shared',action='store_true',help='V2 deterministic prior-vector references')
    args=parser.parse_args()
    global codec
    if args.shared:
        import scheduled_proof_codec_shared
        codec = scheduled_proof_codec_shared
    proof=json.loads(args.proof.read_text()); spec=json.loads(args.spec.read_text())
    roots=json.loads(args.statement.read_text())['roots']
    blob=codec.encode(proof); decoded=codec.decode(blob)
    assert decoded==proof and codec.encode(decoded)==blob
    verify(decoded,spec,roots)
    negatives=malformed_tests(proof,blob)
    # A changed semantic claim remains encodable but the proof verifier rejects it.
    bad=deepcopy(proof); v=bad['finals'][0][0]['c0']; v['c0']=(v['c0']+1)%codec.P
    try: verify(codec.decode(codec.encode(bad)),spec,roots)
    except (ValueError,KeyError,TypeError,IndexError): pass
    else: raise AssertionError('semantic mutation accepted')
    args.output.parent.mkdir(parents=True,exist_ok=True); args.output.write_bytes(blob)
    report={'status':'PASS','lossless_all_fields':True,'decoded_proof_verified':True,
            'malformed_codec_inputs_rejected':negatives,'semantic_mutation_rejected':True,
            'source_json_bytes':args.proof.stat().st_size,'binary_sha256':hashlib.sha256(blob).hexdigest(),
            'proof_json_sha256':hashlib.sha256(args.proof.read_bytes()).hexdigest(),
            'codec_source_sha256':hashlib.sha256(Path(codec.__file__).read_bytes()).hexdigest(),
            'size':decomposition(proof) if not args.shared else {'complete_binary_bytes':len(blob)},
            'profile':'shared-vector-v2' if args.shared else 'verbatim-v1',
            'limitations':['Trusted AIR/public/profile/source roots are external verifier inputs.',
                           'All metadata and redundant transcript fields retained; no derivation or lossy omission.',
                           'Container checks do not replace semantic/protocol verification.',
                           'No security level or complete state-transition proof claim.']}
    args.output.with_suffix('.report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__': main()
