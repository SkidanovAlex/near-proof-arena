#!/usr/bin/env python3
"""Binding regressions on an actual completed D1 diagnostic proof."""
import argparse
from copy import deepcopy
import json
from pathlib import Path

import scheduled_bus_whir as protocol


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('proof', type=Path)
    ap.add_argument('expected_spec', type=Path)
    ap.add_argument('expected_statement', type=Path)
    ap.add_argument('report', type=Path)
    args = ap.parse_args()
    original = json.loads(args.proof.read_text())
    spec = json.loads(args.expected_spec.read_text())
    roots = json.loads(args.expected_statement.read_text())['roots']
    if protocol.verify(original, spec, roots) is not True: raise ValueError('baseline failed')
    rejected = []
    def reject(label, change):
        proof, expected, caps = deepcopy(original), deepcopy(spec), deepcopy(roots)
        change(proof, expected, caps)
        try: protocol.verify(proof, expected, caps)
        except (ValueError, KeyError, TypeError, IndexError): rejected.append(label)
        else: raise AssertionError('accepted mutation: '+label)
    reject('missing table', lambda p,s,r:p['tables'].pop())
    reject('reordered tables', lambda p,s,r:p['tables'].reverse())
    reject('missing auxiliary root', lambda p,s,r:p['aux_roots'].pop())
    reject('source root binding', lambda p,s,r:r[0].__setitem__(0,r[0][0]^1))
    reject('auxiliary root binding', lambda p,s,r:p['aux_roots'][0].__setitem__(0,p['aux_roots'][0][0]^1))
    reject('public tape binding', lambda p,s,r:s['public'].__setitem__(0,s['public'][0]^1))
    reject('row dimension binding', lambda p,s,r:s['log_rows'].__setitem__(0,s['log_rows'][0]-1))
    reject('source/aux opening swap', lambda p,s,r:p['tables'][0]['openings'].reverse())
    reject('truncated zerocheck', lambda p,s,r:p['tables'][0]['constraint_rounds'].pop())
    reject('excess zerocheck degree', lambda p,s,r:p['tables'][0]['constraint_rounds'][0].append(p['tables'][0]['constraint_rounds'][0][0]))
    reject('truncated shift', lambda p,s,r:p['tables'][0]['shift_reduction']['rounds'].pop())
    small = next(i for i,n in enumerate(spec['log_rows']) if n==1)
    def mutate_small(p,s,r):
        rows=p['tables'][small]['openings'][0]['proof']['rows'];rows[0][0]^=1
    reject('disclosed two-row witness mutation', mutate_small)
    reject('small-table format confusion', lambda p,s,r:p['tables'][small]['openings'][0].__setitem__('format','scheduled-whir-v1'))
    reject('large-table downgrade attempt', lambda p,s,r:p['tables'][0]['openings'][0].__setitem__('format','direct-two-row-v1'))
    result={'status':'PASS','rejected':rejected,'count':len(rejected),
            'scope':'Actual D1 binding and malformed-proof regressions; no cryptographic soundness bound.'}
    args.report.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))


if __name__ == '__main__':
    main()
