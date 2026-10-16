#!/usr/bin/env python3
"""Differential checks against Lean-exported evaluations; no succinct proof."""
import hashlib
import json
from copy import deepcopy
from pathlib import Path
from reference import P, check, inspect, evaluate, expr_degree, public_messages

HERE = Path(__file__).resolve().parent


def main():
    fixture = json.loads((HERE / 'fixture.json').read_text())
    air = fixture['air']
    assert fixture['field_modulus'] == P
    compared = 0
    for case in fixture['cases']:
        result = inspect(air, case['rows'], case['public'])
        for key in ('residuals', 'interactions', 'public_messages'):
            assert result[key] == case[key], (case['label'], key)
        assert case['pub_fit']
        assert result['accepted'] == (case['label'] == 'honest'), case['label']
        compared += sum(map(len, case['residuals']))
    honest = fixture['cases'][0]
    rows, public = honest['rows'], honest['public']
    check(air, rows, public)
    rejected = []

    def reject(label, a=air, rs=rows, ps=public):
        try:
            check(a, rs, ps)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError('Accepted ' + label)

    for ti, table in enumerate(rows):
        for ri, row in enumerate(table):
            for ci in range(len(row)):
                bad = deepcopy(rows)
                bad[ti][ri][ci] = (bad[ti][ri][ci] + 1) % P
                reject(f'cell {ti}/{ri}/{ci}', rs=bad)
    for i in range(len(public)):
        bad = public.copy(); bad[i] += 1
        reject(f'public element {i}', ps=bad)
    for value in (-1, P, True):
        bad = deepcopy(rows); bad[0][0][0] = value
        reject(f'noncanonical cell {value}', rs=bad)
        badpub = public.copy(); badpub[8] = value
        reject(f'noncanonical public {value}', ps=badpub)
    for count in (0, 1, 3, 8):
        bad = deepcopy(rows); bad[0] = (bad[0] * 2)[:count]
        reject(f'invalid height {count}', rs=bad)
    bad = deepcopy(rows); bad[0][0].pop(); reject('missing column', rs=bad)
    bad = deepcopy(rows); bad.pop(); reject('missing table', rs=bad)
    for expr in (['v', 2, 0], ['v', 0, True], ['p',100], ['c',-1],
                 ['c',True], ['first',1], ['mystery'], ['+', ['c',0]]):
        bad = deepcopy(air); bad['tables'][0]['constraints'].append(expr)
        reject('malformed expression ' + repr(expr), a=bad)
    for key, value in (('bus',2), ('send',1), ('width',0), ('startAt',-1), ('indexBase',True)):
        bad = deepcopy(air); bad['pubSegs'][0][key] = value
        reject('malformed segment ' + key, a=bad)
    bad = deepcopy(air); bad['maxPub'] = 11; reject('segment exceeds maxPub', a=bad)
    # Exact cyclic wrapping, default public access, reduction and all operators.
    assert evaluate(['v',0,1], rows[0],3,public) == 10
    assert evaluate(['p',99], rows[0],0,public) == 0
    assert evaluate(['c',P+7],rows[0],0,public) == 7
    assert evaluate(['-', ['c',1]],rows[0],0,public) == P-1
    polynomial = ['v',0,0]
    for _ in range(4): polynomial = ['*',polynomial,polynomial]
    assert expr_degree(polynomial,2,100) == 16
    assert evaluate(polynomial,rows[0],0,public) == pow(10,16,P)
    # Preserve exact naturally counted multiplicities, not counts modulo p.
    one = ['first']; zero = ['c',0]
    interaction = {'bus':0,'send':True,'msg':[['c',7]],'mult':[zero]*24+[one]}
    natural_air = {'format':'np-air-v1','numBuses':1,'numPub':0,'tables':[
        {'width':0,'maxLog':1,'constraints':[],
         'interactions':[deepcopy(interaction) for _ in range(120)]+
                        [{'bus':0,'send':True,'msg':[['c',7]],'mult':[one]}]}]}
    natural = inspect(natural_air, [[[],[]]], [])
    assert natural['violations'] == [['bus',0,[7],P]], natural['violations']
    reject('natural multiplicity p is not zero', natural_air, [[[],[]]], [])
    # v1 and v2-with-no-segments agree after removing the public bus interaction.
    v1 = deepcopy(air); v1['format'] = 'np-air-v1'
    del v1['pubSegs']; del v1['maxPub']; v1['tables'][1]['interactions'].pop()
    check(v1, rows, public)
    v2 = deepcopy(v1); v2.update(format='np-air-v2',pubSegs=[],maxPub=0)
    assert inspect(v1,rows,public) == inspect(v2,rows,public)
    # Source count digits are not themselves restricted to bytes; count256 fits.
    digit_air = {'format':'np-air-v2','numBuses':1,'numPub':260,'tables':[],
                 'maxPub':260,'pubSegs':[{'bus':0,'send':True,'width':1,'countAt':0,
                  'start':4,'startAt':None,'indexBase':None,'prefix':[]}]}
    assert len(public_messages(digit_air,[256,0,0,0]+[7]*256)) == 256
    # Tuple lengths are semantically significant, including trailing zeros.
    messages_air = deepcopy(natural_air)
    messages_air['tables'][0]['interactions'] = [
        {'bus':0,'send':True,'msg':[['c',7]],'mult':[one]},
        {'bus':0,'send':False,'msg':[['c',7],zero],'mult':[one]}]
    reject('different message arities',messages_air,[[[],[]]],[])
    report = {'status':'PASS','lean_differential_cases':len(fixture['cases']),
              'lean_rows_compared':compared,'rejected_cases':len(rejected),
              'exact_natural_multiplicity_counterexample':P,
              'coverage':['all canonical Expr constructors','cyclic next row','heterogeneous heights',
                          'public getD-zero','allConstraints bit constraints','natural bus balance',
                          'dynamic/static public segments','prefix/index generation','degree16 expression',
                          'canonical field encoding','np-air-v1/v2 empty segment parity'],
              'limitations':['Full-witness reference interpreter, not succinct proof or PCS verifier.',
                             'Finite Lean/Python differential tests, not formal implementation refinement.',
                             'Does not certify Air.wf security-budget or max-degree bounds.',
                             'Trusted prime modulus; no PQ/security/proof-size claim.'],
              'sha256':{name:hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                        for name in ('reference.py','Fixture.lean','fixture.json','test_reference.py')},
              'rejections':rejected}
    (HERE/'test-results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('sha256','rejections')}))


if __name__ == '__main__': main()
