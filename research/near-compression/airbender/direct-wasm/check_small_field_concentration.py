#!/usr/bin/env python3
"""Exhaustive affine candidate enumeration for fixed small prime fields.
Not a general concentration proof or a production security estimate.
"""
import argparse
import json
from itertools import product
from pathlib import Path


def screen(p, weights, threshold):
    domain = tuple(range(4))
    coefficients = list(product(range(p), repeat=2))
    # Subtract each word's interpolating affine polynomial at x=0,1.
    # This bijects its candidates and preserves every agreement support.
    words = [(0, 0, a, b) for a, b in coefficients]
    evaluations = [tuple((a+b*x) % p for x in domain) for a, b in coefficients]
    mass = lambda mask: sum(w for x, w in enumerate(weights) if mask >> x & 1)
    candidates = {}
    for word in words:
        matches = []
        for coeff, values in zip(coefficients, evaluations):
            mask = sum(1 << x for x in domain if word[x] == values[x])
            if mass(mask) >= threshold:
                matches.append((coeff, mask))
        candidates[word] = matches
    maximum = -1
    witness = None
    absent = 0
    for even in words:
        for odd in words:
            joint = [(a, b) for a, ma in candidates[even] for b, mb in candidates[odd]
                     if mass(ma & mb) >= threshold]
            if joint:
                continue
            absent += 1
            successes = []
            for r in range(p):
                folded = tuple(((1-r)*a+r*b) % p for a, b in zip(even, odd))
                if candidates[folded]:
                    successes.append({'challenge': r, 'candidates': [list(a) for a, _ in candidates[folded]]})
            if len(successes) > maximum:
                maximum = len(successes)
                witness = {'source_even': even, 'source_odd': odd, 'successes': successes}
    return {'prime': p, 'domain': domain, 'strict_degree': 2, 'weights': weights,
            'threshold': threshold, 'johnson_gap': threshold**2-sum(weights)*max(weights),
            'unique_separation_holds': 2*sum(weights)+max(weights)<3*threshold,
            'normalized_source_pairs_checked': len(words)**2,
            'pairs_without_joint_candidate': absent, 'maximum_successful_challenges_without_joint_candidate': maximum,
            'witness': witness}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = {'status': 'EXACT_FINITE_ENUMERATION_NOT_GENERAL_THEOREM',
              'constraint': 'ew=ow=0 and sent=0, so the quadratic constraint is identically satisfied.',
              'coverage': 'All normalized source pairs for each field/profile; every degree<2 polynomial and every challenge enumerated. Reduction of arbitrary words by affine subtraction is mathematical reasoning, not yet a Lean theorem.',
              'lesson': 'Positive weighted Johnson gap alone does not imply that every successful folded candidate has a jointly agreeing parent. An exceptional-challenge term is necessary.',
              'cases': [screen(p, w, t) for p in (5, 7, 11, 17) for w, t in (([1]*4, 3), ([1, 1, 1, 2], 4))]}
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    for case in report['cases']:
        print(case['prime'], case['weights'], 'gap', case['johnson_gap'], 'max false challenges', case['maximum_successful_challenges_without_joint_candidate'])
