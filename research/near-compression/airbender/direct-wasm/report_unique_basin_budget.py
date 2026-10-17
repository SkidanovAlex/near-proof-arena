#!/usr/bin/env python3
"""Exact integer screen of the proved unique-basin interactive count bound.
Not a PQ claim, a proof-size estimate, or a demonstration of source proximity.
"""
import json
from pathlib import Path

P = 2013265921
Q = P**8

def screen(degree, bits):
    domain = 4 * degree
    rounds = degree.bit_length() - 1
    threshold = (2 * domain + degree) // 3 + 1
    round_numerator = sum(max(domain >> (i + 1), 2) for i in range(rounds))
    # epsilon <= round_numerator/Q + ((threshold-1)/domain)**queries.
    target = 1 << bits
    if round_numerator * target >= Q:
        return {'degree': degree, 'target_ideal_bits': bits, 'feasible': False,
                'reason': 'fold challenge term exhausts target'}
    queries = 0
    while target * (round_numerator * domain**queries + Q * (threshold-1)**queries) > Q * domain**queries:
        queries += 1
    return {'degree': degree, 'domain': domain, 'target_ideal_bits': bits,
            'feasible': True, 'threshold': threshold, 'minimum_queries_for_bound': queries,
            'fold_round_numerator': round_numerator,
            'maximum_representative_mismatches': threshold-degree,
            'diagnostic_queries': 8}

if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = {'status': 'CONDITIONAL_IDEAL_INTERACTIVE_SCREEN',
              'field_size': Q, 'field': 'BabyBear^8 arithmetic projection',
              'bound': 'A/Q + ((T-1)/N)^q',
              'threshold_choice': 'smallest integer satisfying 2*N+D < 3*T',
              'qualifications': ['Fixed representative proximity not established for adversarial commitments.',
                                 '128 ideal bits does not establish 128 post-quantum bits.',
                                 'No Merkle, Fiat-Shamir/QROM, or byte cost included.'],
              'cases': [screen(d, b) for d in (1024, 131072, 1048576) for b in (128, 192, 256)]}
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))
