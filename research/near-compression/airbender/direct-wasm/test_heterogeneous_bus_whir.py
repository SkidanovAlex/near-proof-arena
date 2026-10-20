#!/usr/bin/env python3
"""Replay independent bus proof verification with shape and binding attacks."""
from copy import deepcopy
import json
from pathlib import Path

import heterogeneous_bus_whir as protocol


def main():
    out = Path(__file__).resolve().parents[2] / 'results'
    proof = json.loads((out / 'heterogeneous-bus-proof.json').read_text())
    spec = json.loads((out / 'heterogeneous-bus-spec.json').read_text())
    roots = json.loads((out / 'heterogeneous-bus-statement.json').read_text())['roots']
    assert protocol.verify(proof, spec, roots)
    rejected = []

    def reject(label, change, which='proof'):
        p, s, r = deepcopy(proof), deepcopy(spec), deepcopy(roots)
        change({'proof': p, 'spec': s, 'roots': r}[which])
        try:
            protocol.verify(p, s, r)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError('Accepted ' + label)

    for key in ('aux_roots', 'finals', 'tables'):
        reject('missing ' + key, lambda p, key=key: p.pop(key))
        reject('truncated ' + key, lambda p, key=key: p[key].pop())
        reject('extra ' + key, lambda p, key=key: p[key].append(deepcopy(p[key][-1])))
    for ti in range(2):
        for key in ('constraint_rounds', 'shift_reduction', 'openings'):
            reject(f'table{ti} missing {key}', lambda p, ti=ti, key=key: p['tables'][ti].pop(key))
        for key in ('constraint_rounds', 'openings'):
            reject(f'table{ti} truncated {key}', lambda p, ti=ti, key=key: p['tables'][ti][key].pop())
            reject(f'table{ti} extra {key}', lambda p, ti=ti, key=key: p['tables'][ti][key].append(deepcopy(p['tables'][ti][key][-1])))
        for key in ('current_evals', 'next_evals', 'rounds'):
            reject(f'table{ti} missing shift {key}', lambda p, ti=ti, key=key: p['tables'][ti]['shift_reduction'].pop(key))
            reject(f'table{ti} truncated shift {key}', lambda p, ti=ti, key=key: p['tables'][ti]['shift_reduction'][key].pop())
            reject(f'table{ti} extra shift {key}', lambda p, ti=ti, key=key: p['tables'][ti]['shift_reduction'][key].append(deepcopy(p['tables'][ti]['shift_reduction'][key][-1])))
        for ri in range(spec['log_rows'][ti]):
            for ci in range(3):
                def mutate(p, ti=ti, ri=ri, ci=ci):
                    p['tables'][ti]['shift_reduction']['rounds'][ri][ci]['c0']['c0'] ^= 1
                reject(f'table{ti} shift round{ri} coefficient{ci}', mutate)
        for branch in range(2):
            values = proof['tables'][ti]['openings'][branch]['proof']['witness_commitment']['evals']
            for ci in range(len(values)):
                def mutate(p, ti=ti, branch=branch, ci=ci):
                    p['tables'][ti]['openings'][branch]['proof']['witness_commitment']['evals'][ci]['c0']['c0'] ^= 1
                reject(f'table{ti} branch{branch} final evaluation{ci}', mutate)
            reject(f'table{ti} branch{branch} omitted PCS',
                   lambda p, ti=ti, branch=branch: p['tables'][ti]['openings'][branch].pop('proof'))
        reject(f'table{ti} truncated finals', lambda p, ti=ti: p['finals'][ti].pop())
        reject(f'table{ti} extra finals', lambda p, ti=ti: p['finals'][ti].append(deepcopy(p['finals'][ti][-1])))

    reject('missing original root', lambda r: r.pop(), 'roots')
    reject('extra original root', lambda r: r.append(r[-1]), 'roots')
    reject('public count exceeds segment fit', lambda s: s['public'].__setitem__(0, 9), 'spec')
    reject('public source record removed', lambda s: s['public'].pop(), 'spec')
    reject('public segment duplicated', lambda s: s['air']['pubSegs'].append(deepcopy(s['air']['pubSegs'][0])), 'spec')
    reject('wrong row dimension', lambda s: s.__setitem__('log_rows', 4), 'spec')

    def monomial(degree):
        result = ['c', 1]
        for _ in range(degree):
            result = ['*', result, ['v', 0, 0]]
        return result

    # These bounds exercise the first partial product, whose degree can exceed
    # the source expression and the later chain residuals.
    degree_checks = []
    for d, expected in ((1, 4), (4, 13), (5, 16)):
        table = {'width': 1, 'maxLog': 3, 'constraints': [], 'interactions': [
            {'bus': 0, 'send': True, 'mult': [monomial(d), monomial(d)], 'msg': [monomial(d)]}]}
        assert protocol.table_degree(table, 0) == expected
        degree_checks.append([d, expected])
    table['interactions'][0]['mult'] = [monomial(6), monomial(6)]
    table['interactions'][0]['msg'] = [monomial(6)]
    try:
        protocol.table_degree(table, 0)
    except ValueError:
        pass
    else:
        raise AssertionError('Auxiliary degree19 silently accepted under cap16')

    report = {'status': 'PASS', 'rejections': len(rejected), 'rejection_labels': rejected,
              'first_partial_product_degree_checks': degree_checks,
              'above_cap_auxiliary_degree_rejected': True,
              'limitations': ['Mutation and degree-budget tests, not a formal soundness proof.']}
    (out / 'heterogeneous-bus-negative-tests.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
