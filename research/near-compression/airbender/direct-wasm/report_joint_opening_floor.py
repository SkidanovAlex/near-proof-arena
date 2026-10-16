#!/usr/bin/env python3
"""Optimistic expected source-opening floors under narrowly defined layouts.
All PCS round/terminal/folded-oracle costs are deliberately omitted.
These are not lower bounds on arbitrary protocols or on each sampled proof.
"""
import argparse
import json
import hashlib
import pq384_global_bus as bus
from pathlib import Path
from report_packing_expectation import tree_expectation, validate_expectation


def optimize_source(log_rows, width, queries):
    choices = []
    for exponent in range(11):
        packing = 1 << exponent
        degree = (1 << log_rows)*packing
        lanes = (width+packing-1)//packing
        if not 128 <= degree <= 262144 or lanes > 64:
            continue
        leaves, siblings = tree_expectation(2*degree, queries)
        choices.append({'packing': packing, 'degree': degree, 'lanes': lanes,
                        'expected_leaf_bytes': 8*lanes*leaves,
                        'expected_sibling_bytes': 48*siblings,
                        'expected_bytes': 8*lanes*leaves+48*siblings})
    return min(choices, key=lambda c: c['expected_bytes'])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--fixture', type=Path, required=True)
    ap.add_argument('--packing-report', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    validate_expectation()
    spec = json.loads((a.fixture/'statement.json').read_text())['spec']
    assert len(set(spec['log_rows'])) == 1, 'merged-tree screen requires equal table heights'
    log_rows = spec['log_rows'][0]
    report = json.loads(a.packing_report.read_text())
    cases = []
    for case in report['cases']:
        if case['queries'] == 8:
            continue
        for b in case['branches']:
            table = spec['air']['tables'][b['table']]
            expected_width = table['width'] if b['branch'] == 0 else case['extension_degree']*bus.aux.layout(table)['aux_columns']
            assert b['width'] == expected_width, 'packing report does not match fixture'
        separate = [optimize_source(log_rows, b['width'], case['queries']) for b in case['branches']]
        phases = []
        for branch in (0, 1):
            members = [b for b in case['branches'] if b['branch'] == branch]
            width = sum(b['width'] for b in members)
            phases.append({'phase': 'before_bus' if branch == 0 else 'after_bus', 'width': width,
                           'best': optimize_source(log_rows, width, case['queries'])})
        separate_bytes = sum(b['expected_bytes'] for b in separate)
        phase_bytes = sum(b['best']['expected_bytes'] for b in phases)
        cases.append({'extension_degree': case['extension_degree'], 'queries': case['queries'],
                      'retained_local_and_framing_bytes': case['non_pcs_bytes'],
                      'four_tree_expected_source_only_bytes': separate_bytes,
                      'four_tree_plus_retained_local_bytes': separate_bytes+case['non_pcs_bytes'],
                      'two_phase_tree_expected_source_only_bytes': phase_bytes,
                      'two_phase_tree_plus_retained_local_bytes': phase_bytes+case['non_pcs_bytes'],
                      'two_phase_remaining_budget_before_all_other_costs': 300000-phase_bytes,
                      'four_tree_optima': separate, 'phase_tree_optima': phases})
    result = {'statement_sha256': hashlib.sha256((a.fixture/'statement.json').read_bytes()).hexdigest(),
              'packing_report_sha256': hashlib.sha256(a.packing_report.read_bytes()).hexdigest(),
              'status': 'OPTIMISTIC_EXPECTED_LAYOUT_SCREEN_NOT_A_PROTOCOL', 'cases': cases,
              'preserved': ['Base-field source/auxiliary coordinate leaves, SHA384 Merkle paths, rate1/4, same query count per tree.',
                            'Two-phase alternative keeps source commitments before bus challenges and auxiliary commitments after; no cross-phase merging.'],
              'omitted': ['All folded-oracle openings, PCS round messages, terminal coefficients.',
                          'Statement/request bytes, any new cross-table reduction or domain framing costs.'],
              'qualifications': ['Expected values under uniform queries, not per-proof lower bounds.',
                                 'Four-tree minima are only over eligible packing choices in this model.',
                                 'Two-phase merging is speculative; no combined prover/verifier or binding theorem is implemented.',
                                 'Retained non-PCS subtotal deliberately remains unchanged, including old root/framing bytes; the subtotal is not an exact new-format prediction.',
                                 'Ext8 and all query counts remain uncertified projections.'],
              'decision': 'Sharing only folded-oracle work cannot meet300000 bytes in the four-tree309-query Ext8 model. Two-phase merging additionally requires compression of local claim data and a budget for the omitted PCS work; evaluate against recursion.'}
    a.output.write_text(json.dumps(result, indent=2)+'\n')
    for c in cases:
        print(c['extension_degree'], c['queries'], round(c['four_tree_expected_source_only_bytes']),
              round(c['two_phase_tree_expected_source_only_bytes']), round(c['two_phase_tree_plus_retained_local_bytes']))


if __name__ == '__main__':
    main()
