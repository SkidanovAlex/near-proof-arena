"""Alternating injections/folds versus original dense algebra, including endpoints."""
import hashlib
import json
from pathlib import Path
import random
import ext8_structured_functional as structured
import ext8_code_switch_functional as dense
from pq384_ext8_terminal_gkr import eqs
f=structured.f
ROOT=Path(__file__).resolve().parents[2]


def main():
    rng=random.Random(265040);scalar=lambda:tuple(rng.randrange(f.P) for _ in range(8));cases=[];comparisons=0
    for n in range(1,7):
        for mode in ('zero','one','random'):
            point=[scalar() for _ in range(n)];state=structured.Functional.equality(point);weights=eqs(point);claim=f.ZERO
            for step in range(n+1):
                # Duplicate and zero evaluation points, zero/nonzero mixers.
                z=scalar();points=[f.ZERO,f.ONE,z,z];mixers=[f.ZERO,scalar(),scalar(),scalar()];answers=[scalar() for _ in points]
                weights,claim=dense.inject(weights,claim,points,answers,mixers);state=state.inject(points,mixers)
                assert state.materialize()==weights;comparisons+=len(weights)
                if step<n:
                    r=f.ZERO if mode=='zero' else f.ONE if mode=='one' else scalar()
                    weights=f.affine_fold(weights,r);state=state.fold(r)
                    assert state.materialize()==weights;comparisons+=len(weights)
            try:state.fold(f.ONE)
            except ValueError:pass
            else:raise AssertionError('fold beyond terminal')
            cases.append(dict(log_degree=n,mode=mode,injection_terms=len(state.powers)))
    paths=[Path(__file__),Path(structured.__file__),Path(dense.__file__)]
    report=dict(status='STRUCTURED_FUNCTIONAL_DENSE_PARITY',cases=cases,compared_ext8_values=comparisons,
        identities=['Fold of tensor equality weights removes the low bit and multiplies by (1-r)(1-u)+r*u.',
                    'Fold of m*z^i gives m*(1-r+r*z)*(z^2)^i.',
                    'Injected functionals add their (m,z) terms; claim update remains the original sum m*answer.'],
        scope='18 deterministic small sequences of alternating injections and folds, zero/one/random folds, duplicate/zero points. Exact executable parity with existing dense functional. Not a universal Lean theorem, protocol change, transcript-binding certificate, recursive proof or PQ128 result. Existing vector-hashing transcript still requires materialization.',
        sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths})
    (ROOT/'results/ext8-structured-functional.json').write_text(json.dumps(report,indent=2)+'\n');print(report['status'],comparisons)


if __name__=='__main__':main()
