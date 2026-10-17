#!/usr/bin/env python3
"""Expected wire size under ideal uniform global query seeds; not security.
Models existing separate source/aux trees and terminal1, including multiproofs.
Ext8 is a width projection, not an implemented verifier profile.
"""
import argparse
import json
import math
from itertools import product
from pathlib import Path
import pq384_global_bus as bus
import pq384_multiproof as mp


def tree_expectation(leaves, queries):
    distinct = leaves * (-math.expm1(queries * math.log1p(-1/leaves)))
    siblings = 0.0
    nodes = leaves
    while nodes > 1:
        # A node is missing while its sibling is present.
        a = (1-1/nodes)**queries
        b = (1-2/nodes)**queries
        siblings += nodes*(a-b)
        nodes //= 2
    return distinct, siblings


def validate_expectation():
    checks = 0
    for leaves in (2, 4, 8):
        for queries in (1, 2, 3, 4):
            totals = [0, 0]
            for indices in product(range(leaves), repeat=queries):
                totals[0] += len(set(indices))
                totals[1] += len(mp.boundary(leaves, list(indices)))
            expected = tree_expectation(leaves, queries)
            for actual, target in zip(totals, expected):
                assert abs(actual/leaves**queries-target) < 1e-10
            checks += 1
    return checks


def branch_size(log_rows, width, packing, extension, queries):
    degree = (1 << log_rows)*packing
    rounds = degree.bit_length()-1
    # Three extension elements plus one SHA384 root per round; terminal1.
    fixed = 6+(3*4*extension+48)*rounds+4*extension
    leaf_bytes = sibling_bytes = 0.0
    for stage in range(rounds+1):
        count = 2*(degree >> stage)
        leaf_size = 8*((width+packing-1)//packing) if stage == 0 else 8*extension
        leaves, siblings = tree_expectation(count, queries)
        leaf_bytes += leaves*leaf_size
        sibling_bytes += siblings*48
    return {'packing': packing, 'degree': degree, 'lanes': (width+packing-1)//packing,
            'expected_bytes': fixed+leaf_bytes+sibling_bytes, 'fixed_bytes': fixed,
            'expected_leaf_bytes': leaf_bytes, 'expected_sibling_bytes': sibling_bytes}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--fixture', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    validated = validate_expectation()
    spec = json.loads((a.fixture/'statement.json').read_text())['spec']
    assert spec['terminal_degree'] == 1
    table_degrees = bus.validate(spec)
    cases = []
    for extension in (4, 8):
        for queries in (8, 128, 239, 309):
            # Outer framing, transported source roots, auxiliary roots/finals,
            # local sumchecks, shift claim vectors/rounds, and branch framing.
            non_pcs = 6+48*len(spec['air']['tables'])
            branches = []
            for ti, (table, d) in enumerate(zip(spec['air']['tables'], table_degrees)):
                layout = bus.aux.layout(table)
                n = spec['log_rows'][ti]
                sw, aw = table['width'], extension*layout['aux_columns']
                non_pcs += 48+4*extension*(layout['finals']+n*(d+2)+3*(sw+aw)+3*n)
                for branch, width in enumerate((sw, aw)):
                    if not width:
                        continue
                    non_pcs += 8
                    options = []
                    for exponent in range(11):
                        packing = 1 << exponent
                        degree = (1 << n)*packing
                        if not 128 <= degree <= 262144 or (width+packing-1)//packing > 64:
                            continue
                        options.append(branch_size(n, width, packing, extension, queries))
                    best = min(options, key=lambda x: x['expected_bytes'])
                    retained_packing = spec['source_packings' if branch == 0 else 'aux_packings'][ti]
                    retained = branch_size(n, width, retained_packing, extension, queries)
                    branches.append({'table': ti, 'branch': branch, 'width': width,
                                     'best': best, 'retained': retained,
                                     'retained_within_lane_limit': retained['lanes'] <= 64, 'options': options})
            if extension == 4:
                baseline = json.loads((a.fixture/'binary-report.json').read_text())
                geometry_path = a.fixture.parent/'slice-query-geometry.json'
                if geometry_path.exists():
                    assert non_pcs == json.loads(geometry_path.read_text())['non_pcs_bytes']
                assert baseline['proof_bytes'] == (a.fixture/'proof.bin').stat().st_size
            cases.append({'extension_degree': extension, 'queries': queries, 'non_pcs_bytes': non_pcs,
                          'optimized_expected_proof_bytes': non_pcs+sum(b['best']['expected_bytes'] for b in branches),
                          'retained_expected_proof_bytes': non_pcs+sum(b['retained']['expected_bytes'] for b in branches),
                          'branches': branches})
    report = {'status': 'IDEAL_QUERY_EXPECTATION_SCREEN_NOT_PROOF_MEASUREMENT',
              'validation_exhaustive_tree_cases': validated, 'cases': cases,
              'scope': 'Actual193-instruction table dimensions; each PCS branch optimized independently over power-of-two packing1..1024 within degree/lane limits.',
              'qualifications': ['Expected sizes, not worst-case bounds or authenticated generated proofs.',
                                 'Uniform seed marginals suffice for expected stage sums; stage independence is not assumed.',
                                 'Retained Ext8 CODE-aux packing has100 lanes and exceeds the current64-lane limit; retained expectations are hypothetical references, not eligible profiles.',
                                 'Ext8 increases auxiliary coordinate widths and field-element bytes; implementation and security are unproved.',
                                 'Statement/request bytes excluded; changing packing changes the statement and transcript.',
                                 'No joint-opening, recursion, or terminal64 model. No claim of a global packing optimum beyond enumerated choices.']}
    a.output.write_text(json.dumps(report, indent=2)+'\n')
    for c in cases:
        print(c['extension_degree'], c['queries'], round(c['retained_expected_proof_bytes']),
              round(c['optimized_expected_proof_bytes']), [b['best']['packing'] for b in c['branches']])


if __name__ == '__main__':
    main()
