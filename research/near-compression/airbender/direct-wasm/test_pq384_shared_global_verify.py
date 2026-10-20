"""Differential complete-workload checks for mandatory shared authentication."""
import argparse
import copy
import json
import struct
from pathlib import Path
import pq384_global_bus as bus
import pq384_global_codec as codec
import pq384_shared_global_verify as shared
from profile_pq384_verifier import measure


def rejected(fn):
    try:
        fn()
    except ValueError:
        return True
    return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('directory', type=Path)
    ap.add_argument('output', type=Path)
    a = ap.parse_args()
    proof = json.loads((a.directory/'proof.json').read_text())
    statement = json.loads((a.directory/'statement.json').read_text())
    spec = statement['spec']
    roots = [bytes.fromhex(v) for v in statement['roots']]
    assert bus.verify(proof, spec, roots)
    st, t, alpha, gamma = bus.begin(spec, roots)
    aux = [bytes.fromhex(v) for v in proof['aux_roots']]
    bus.initialize_aux(t, spec, aux, proof['finals'])
    jobs = []
    negative = 0
    for ti, part in enumerate(proof['tables']):
        branches = bus.verify_table_reduction(part, spec, st, t, alpha, gamma,
            ti, proof['finals'][ti], [roots[ti], aux[ti]])
        for opening, args in zip(part['openings'], branches):
            kwargs = dict(terminal_degree=spec['terminal_degree'], **args)
            wire = codec.encode(opening, **kwargs)
            assert codec.decode(wire, **kwargs) == opening
            assert shared.verify(wire, **kwargs)
            jobs.append((wire, kwargs))
            rounds, fixed, _ = codec.limits(args, spec['terminal_degree'])
            offsets = [0, 6, 6+48, 6+96*rounds, fixed, len(wire)-1]
            mutations = []
            for offset in offsets:
                v = bytearray(wire)
                v[offset] ^= 1
                mutations.append(bytes(v))
            mutations += [wire[:-1], wire+b'\x00', wire[:6]+struct.pack('<I', shared.P)+wire[10:]]
            for v in mutations:
                assert rejected(lambda: codec.decode(v, **kwargs)), 'reference accepted mutation'
                assert rejected(lambda: shared.verify(v, **kwargs)), 'shared accepted mutation'
                negative += 1
            wrong = copy.deepcopy(kwargs)
            wrong['expected_root'] = bytes([kwargs['expected_root'][0]^1])+kwargs['expected_root'][1:]
            assert rejected(lambda: codec.decode(wire, **wrong))
            assert rejected(lambda: shared.verify(wire, **wrong))
            negative += 1

    def run_shared():
        return all(shared.verify(wire, **kwargs) for wire, kwargs in jobs)

    def run_reference():
        return all(bool(codec.decode(wire, **kwargs)) for wire, kwargs in jobs)

    report = dict(status='PASS', branches=len(jobs), differential_rejections=negative,
        shared_verifier=measure(run_shared), reference_binary_verifier=measure(run_reference),
        scope='All actual PCS branches from independently verified complete bus proof; same bytes and transcript, mandatory shared authentication.',
        limits=['Branch verifier only; complete bus binary decoder still uses reference path.',
                'No formal equivalence theorem or recursive circuit yet.', 'Q8/Ext4 security unchanged.'])
    a.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('status','branches','differential_rejections')}))


if __name__ == '__main__':
    main()
