#!/usr/bin/env python3
"""Symbolic diagnostic: observed D1 padding emits no bus multiplicity.

Fixes current padding cells and public tape, leaving next columns and the
last-row selector symbolic. Polynomial normalization is over the base field.
Not a Lean certificate or a proof that every rendered suffix has these cells.
"""
import argparse
import hashlib
import json
from pathlib import Path
from reference import P, schema, require


def constant(n):
    return {(): n % P} if n % P else {}


def plus(a, b):
    result = dict(a)
    for m, c in b.items():
        result[m] = (result.get(m, 0)+c) % P
        if not result[m]:
            del result[m]
    return result


def times(a, b):
    result = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            m = tuple(sorted(ma+mb))
            result = plus(result, {m: ca*cb % P})
    return result


def lower(e, pad, public):
    op = e[0]
    if op == 'c':
        return constant(e[1])
    if op == 'p':
        return constant(public[e[1]] if e[1] < len(public) else 0)
    if op == 'v':
        return {(e[1],): 1} if e[2] else constant(pad[e[1]])
    if op == 'first':
        return {}
    if op == 'last':
        return {(len(pad),): 1}
    if op == 'trans':
        return plus(constant(1), {(len(pad),): P-1})
    a = lower(e[1], pad, public)
    if op == '-':
        return {m: -c % P for m, c in a.items()}
    b = lower(e[2], pad, public)
    return plus(a, b) if op == '+' else times(a, b)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('air', type=Path)
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    air = json.loads(args.air.read_text())
    schema(air)
    public = list((args.directory/'prepared.bin').read_bytes())
    samples = json.loads((args.directory/'samples.json').read_text())
    results = []
    for ti in (11, 12, 13, 14, 15, 16):
        pad = samples[ti]['samples'][-1]['current']
        table = air['tables'][ti]
        require(len(pad) == table['width'], 'padding width')
        count = 0
        for interaction in table['interactions']:
            for bit in interaction['mult']:
                require(lower(bit, pad, public) == {}, f'nonzero symbolic padding multiplicity table{ti}')
                count += 1
        results.append({'table': ti, 'multiplicity_expressions_zero': count,
                        'padding_row_sha256': hashlib.sha256(json.dumps(pad).encode()).hexdigest()})
    report = {'status': 'PASS', 'tables': results,
              'symbolic_variables': 'All next-row columns and last selector; transition=1-last,first=0',
              'limitations': ['Python polynomial normalization, not a formal Lean certificate.',
                             'The renderer must establish that its padding rows equal these observed cells.']}
    (args.directory/'padding-traffic-diagnostic.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
