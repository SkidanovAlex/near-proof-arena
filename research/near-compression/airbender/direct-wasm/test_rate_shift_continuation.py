"""Fresh-process authenticated continuation tests and complete JSON sizes."""
import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
import pq384_ext8_rate_shift_continuation as r
p, e = r.p, r.e


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--verify-only', type=Path)
    args = ap.parse_args()
    if args.verify_only:
        env = json.loads(args.verify_only.read_text())
        assert r.verify(env['proof'], env['config'], bytes.fromhex(env['root']), env['continuation_queries'])
        print('PASS fresh continuation verifier')
        return
    args.output.mkdir(parents=True, exist_ok=True)
    cases, negatives = [], []
    for degree, qs, qc in [(32, 4, 8), (128, 4, 8), (32, 314, 256), (1024, 314, 264)]:
        coeff = [(i*i*541+i*173+11) % e.P for i in range(degree)]
        point = [tuple((i+7)*(j+19) for j in range(8)) for i in range(degree.bit_length()-1)]
        # Independent bit-index equality functional, not p.eqweights.
        claim = e.ZERO
        for i, c in enumerate(coeff):
            weight = e.ONE
            for j, u in enumerate(point):
                weight = e.mul(weight, u if (i >> j) & 1 else e.sub(e.ONE, u))
            claim = e.add(claim, e.scale(weight, c))
        cfg = dict(profile=p.PROFILE, degree=degree, queries=qs, point=[list(u) for u in point],
            claim=list(claim), statement=b'continuation-experiment'.hex(), source_namespace=b'continuation-base'.hex())
        root = p.source_tree(coeff, cfg)['root']
        started = time.monotonic()
        proof = r.prove(coeff, cfg, root, qc)
        proving = time.monotonic()-started
        started = time.monotonic()
        assert r.verify(proof, cfg, root, qc)
        verification = time.monotonic()-started
        env = dict(proof=proof, config=cfg, root=root.hex(), continuation_queries=qc)
        raw = json.dumps(env, separators=(',', ':')).encode()
        path = args.output/f'd{degree}-s{qs}-c{qc}.json'
        path.write_bytes(raw)
        subprocess.run([sys.executable, __file__, '--output', str(args.output), '--verify-only', str(path)], check=True)
        source_threshold = (9*degree)//3+1
        minimum = (source_threshold+3)//4
        next_degree, next_domain = degree//4, 2*degree
        continuation_threshold = (2*next_domain+next_degree)//3+1
        radius = next_domain-continuation_threshold
        assert 2*radius+next_degree <= next_domain
        extraction = sum(next_domain//(2**i) for i in range(1, next_degree.bit_length()))
        ideal = (Fraction(3*degree+qs+1+extraction, e.P**8)
                 + Fraction(minimum-1, degree)**qs
                 + Fraction(continuation_threshold-1, next_domain)**qc)
        if qs == 314:
            assert ideal <= Fraction(1, 2**128)
        cases.append(dict(degree=degree, source_queries=qs, continuation_queries=qc,
            complete_envelope_json_bytes=len(raw), proof_json_bytes=len(json.dumps(proof, separators=(',', ':')).encode()),
            ideal_error_bound_float=float(ideal), ideal_bound_below_2powminus128=ideal <= Fraction(1, 2**128),
            prove_seconds=proving, verify_seconds=verification, sha256=hashlib.sha256(raw).hexdigest()))
        if degree == 32 and qs == 4:
            def reject(name, bad, config=cfg, expected=root, count=qc):
                try:
                    r.verify(bad, config, expected, count)
                except (ValueError, TypeError, KeyError, IndexError):
                    negatives.append(name)
                else:
                    raise AssertionError(name)
            for key, val in [('profile', 'wrong'), ('next_root', '00'*48), ('ood_value', [0]*8),
                             ('terminal', [0]*8), ('source_queries', proof['source_queries'][:-1]),
                             ('queries', proof['queries'][:-1]), ('rounds', proof['rounds'][:-1])]:
                bad = copy.deepcopy(proof)
                bad[key] = val
                reject(key, bad)
            for name, mutate in [
                ('prefix endpoint', lambda b: b['quadratics'][0][0].__setitem__(0, (b['quadratics'][0][0][0]+1) % e.P)),
                ('continuation endpoint', lambda b: b['rounds'][0]['quadratic'][0].__setitem__(0, (b['rounds'][0]['quadratic'][0][0]+1) % e.P)),
                ('source authentication', lambda b: b['source_queries'][0][0]['path'].__setitem__(0, '00'*48)),
                ('continuation authentication', lambda b: b['queries'][0][0][0]['path'].__setitem__(0, '00'*48)),
            ]:
                bad = copy.deepcopy(proof)
                mutate(bad)
                reject(name, bad)
            reject('external root', proof, expected=bytes(48))
            reject('external statement', proof, config={**cfg, 'statement': '00'})
            reject('external continuation budget', proof, count=qc+1)
            reject('external source budget', proof, config={**cfg, 'queries': qs+1})
    report = dict(status='PASS', cases=cases, negative_checks=negatives,
        limitations=['JSON repeats authentication paths; no compact codec claimed.',
            'Sizes cover this PCS envelope, not recursive GKR or full NEAR state transitions.',
            'Executable Python is not kernel-refined; commitment binding and QROM remain open.',
            'Ideal error bounds require original no-candidate, root geometry and causal transcript premises.'],
        source_sha256={name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
            for name in ['pq384_ext8_rate_shift_continuation.py', Path(__file__).name]})
    (args.output/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
