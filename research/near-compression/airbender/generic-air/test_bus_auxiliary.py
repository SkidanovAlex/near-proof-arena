#!/usr/bin/env python3
"""Source differential algebra tests; no transcript or succinct bus proof."""
import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import random
import sys
from bus_auxiliary import (P,ZERO,ONE,base,add,mul,power,layout,expr,fingerprint,generate,evaluate)

HERE = Path(__file__).resolve().parent


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--direct-wasm',type=Path,help='Optional upstream-compatible Ext4 helper directory for arithmetic parity')
    args = ap.parse_args()
    fixture = json.loads((HERE/'bus-aux-fixture.json').read_text())
    table = fixture['table']
    assert layout(table) == {'chain_columns':6,'aux_columns':10,'finals':4,'order':[1,2,0,3]}
    compared = 0
    for case in fixture['cases']:
        b = lambda xs: [base(x) for x in xs]
        selectors = dict(zip(('first','last','trans'),b(case['selectors'])))
        result = evaluate(table,b(case['current']),b(case['next']),case['public'],selectors,
                          base(case['alpha']),base(case['gamma']),b(case['aux_current']),b(case['aux_next']),b(case['finals']))
        assert result == b(case['residuals']),case['label']
        ev = lambda e: expr(e,b(case['current']),b(case['next']),case['public'],selectors)
        assert [fingerprint(i,ev,base(case['alpha'])) for i in table['interactions']] == b(case['fingerprints'])
        compared += len(result)
    rows = [[7,1,0],[8,0,1]]; public = [11]
    rejected, positive = [], 0
    for name,alpha,gamma in [('zero-factor',base(3),base(10)),('extension',(3,4,5,6),(7,8,9,10))]:
        generated = generate(table,rows,public,alpha,gamma)
        def residuals(generated,r):
            selectors = {'first':base(int(r==0)),'last':base(int(r==1)),'trans':base(int(r==0))}
            return evaluate(table,[base(x) for x in rows[r]],[base(x) for x in rows[1-r]],public,
                            selectors,alpha,gamma,generated['aux_rows'][r],generated['aux_rows'][1-r],generated['finals'])
        assert all(x == ZERO for r in range(2) for x in residuals(generated,r))
        # Independent natural-power calculation, rather than auxiliary recurrence.
        products = [ONE]*4
        for r,row in enumerate(rows):
            selectors={'first':base(int(r==0)),'last':base(int(r==1)),'trans':base(int(r==0))}
            ev=lambda e: expr(e,[base(x) for x in row],[base(x) for x in rows[1-r]],public,selectors)
            for j,i in enumerate(table['interactions']):
                multiplicity=sum(2**k for k,e in enumerate(i['mult']) if ev(e)==ONE)
                from bus_auxiliary import sub
                products[j]=mul(products[j],power(sub(gamma,fingerprint(i,ev,alpha)),multiplicity))
        assert generated['finals'] == [products[i] for i in layout(table)['order']]
        assert generated['finals'][0] == ONE  # Empty multiplicity list.
        if name == 'zero-factor': assert generated['finals'][2] == ZERO
        positive += 1
        for r in range(2):
            for c in range(10):
                bad=deepcopy(generated);bad['aux_rows'][r][c]=add(bad['aux_rows'][r][c],ONE)
                assert any(x != ZERO for rr in range(2) for x in residuals(bad,rr)),(name,r,c)
                rejected.append(f'{name} auxiliary {r}/{c}')
        for c in range(4):
            bad=deepcopy(generated);bad['finals'][c]=add(bad['finals'][c],ONE)
            assert any(x != ZERO for r in range(2) for x in residuals(bad,r))
            rejected.append(f'{name} final {c}')
        for key in ('aux_rows','finals'):
            bad=deepcopy(generated)
            if key=='aux_rows':bad[key][0].pop()
            else:bad[key].pop()
            try:residuals(bad,0)
            except ValueError:rejected.append(f'{name} missing {key}')
            else:raise AssertionError('missing item accepted')
    # No interactions: exact empty shape; no padding/default columns permitted.
    empty=deepcopy(table);empty['interactions']=[]
    assert generate(empty,rows,public,base(3),base(10)) == {'aux_rows':[[],[]],'finals':[]}
    upstream_checks = 0
    if args.direct_wasm:
        sys.path.insert(0,str(args.direct_wasm.resolve()))
        from check_whir_handoff import mul as upstream_mul
        rng=random.Random(0xB05)
        for _ in range(32):
            a,b=[tuple(rng.randrange(P) for _ in range(4)) for _ in range(2)]
            assert mul(a,b)==upstream_mul(a,b)
            upstream_checks += 1
    report={'status':'PASS','lean_differential_cases':len(fixture['cases']),
            'lean_residuals_compared':compared,'honest_auxiliary_profiles':positive,
            'rejections':len(rejected),'upstream_extension_arithmetic_checks':upstream_checks,
            'layout':layout(table),'zero_factor_accepted':True,
            'limitations':['Full-witness auxiliary generation and local algebra evaluation only.',
                          'No commitment, transcript, global balance or succinct-proof claim.',
                          'Differential tests are not formal implementation refinement.'],
            'sha256':{name:hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in
                      ('bus_auxiliary.py','BusAuxFixture.lean','bus-aux-fixture.json','test_bus_auxiliary.py')}}
    (HERE/'bus-aux-results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))


if __name__=='__main__':main()
