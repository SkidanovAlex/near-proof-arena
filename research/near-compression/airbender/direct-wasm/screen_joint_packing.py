#!/usr/bin/env python3
"""Joint packing screen accounting for a single max-degree folding chain.
Uses full-word expected leaf sizes, not witness-specific zero compression.
"""
import argparse
import itertools
import json
from pathlib import Path
import pq384_global_bus as bus
from report_packing_expectation import tree_expectation, validate_expectation


def screen(spec, queries):
    widths, choices = [], []
    for ti, table in enumerate(spec['air']['tables']):
        for kind, width in (('source', table['width']), ('auxiliary', 4*bus.aux.layout(table)['aux_columns'])):
            if not width:
                continue
            widths.append({'table': ti, 'kind': kind, 'width': width})
            options = []
            for k in range(11):
                packing = 1 << k
                degree = (1 << spec['log_rows'][ti])*packing
                lanes = (width+packing-1)//packing
                if not 128 <= degree <= 262144 or lanes > 64:
                    continue
                leaves, siblings = tree_expectation(2*degree, queries)
                options.append({'packing': packing, 'degree': degree,
                                'source_bytes': 8*lanes*leaves+48*siblings})
            choices.append(options)
    tails = {}
    for degree in {o['degree'] for options in choices for o in options}:
        n = degree.bit_length()-1
        tail = 0.0
        for j in range(n-1):  # Constant terminal tree is reconstructed.
            leaves, siblings = tree_expectation(degree >> j, queries)
            tail += 32*leaves+48*siblings
        tails[degree] = tail+6+62*n+48*(n-1)+16
    best = None
    count = 0
    for options in itertools.product(*choices):
        count += 1
        degree = max(o['degree'] for o in options)
        cost = sum(o['source_bytes'] for o in options)+tails[degree]
        if best is None or cost < best['expected_pcs_bytes']:
            best = {'packings': [o['packing'] for o in options], 'degree': degree,
                    'expected_pcs_bytes': cost, 'expected_sources_bytes': sum(o['source_bytes'] for o in options),
                    'expected_shared_tail_and_header_bytes': tails[degree]}
    return {'queries': queries, 'branches': widths, 'combinations_checked': count, 'best': best}


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--statement', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    validate_expectation()
    spec = json.loads(args.statement.read_text())['spec']
    report = {'status': 'EXPECTED_FULL_WORD_COST_SCREEN',
              'cases': [screen(spec, q) for q in (8, 128, 239, 309)],
              'qualification': 'Ext4 diagnostic shape; costs exclude outer GKR/local/public input data. Optimizing source trees independently is insufficient because increasing maximum degree also enlarges the shared chain. Actual zero-tag costs require fresh proofs.'}
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    for c in report['cases']:
        print(c['queries'], c['best'])
