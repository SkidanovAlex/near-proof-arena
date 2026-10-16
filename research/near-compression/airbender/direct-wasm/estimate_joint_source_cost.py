"""Expected transport cost of retaining original roots in a joint PCS.

Uniform independent full-domain queries project uniformly to each original
tree. Projections across different trees may be correlated; linearity of
expectation does not require independence between trees. This is an expected
cost, not a lower bound or a secure query recommendation.
"""
import argparse
import itertools
import json
from fractions import Fraction
from pathlib import Path
from pq384_multiproof import boundary


def expected_counts(n, q):
    assert n >= 2 and n & (n - 1) == 0 and q > 0
    leaves = n * (1 - Fraction(n - 1, n) ** q)
    siblings = Fraction(0)
    nodes = n
    while nodes > 1:
        # A boundary node is absent while its sibling subtree is visited.
        siblings += nodes * (Fraction(nodes - 1, nodes) ** q
                             - Fraction(nodes - 2, nodes) ** q)
        nodes //= 2
    return leaves, siblings


def validate():
    cases = 0
    for n in (2, 4, 8):
        for q in range(1, 5):
            leaf_sum = sibling_sum = 0
            for indices in itertools.product(range(n), repeat=q):
                leaf_sum += len(set(indices))
                sibling_sum += len(boundary(n, list(indices)))
            assert expected_counts(n, q) == (Fraction(leaf_sum, n**q),
                                             Fraction(sibling_sum, n**q))
            cases += 1
    return cases


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('breakdown', type=Path)
    ap.add_argument('output', type=Path)
    args = ap.parse_args()
    checks = validate()
    report = json.loads(args.breakdown.read_text())
    branches = [b for t in report['tables'] for b in t['branches']]
    first = [b['stages'][0] for b in branches]
    actual = sum(s['leaf_bytes'] + s['sibling_bytes'] for s in first)
    components = report['components']
    retained = sum(components[k] for k in (
        'source_roots', 'aux_roots', 'bus_finals', 'air_sumcheck',
        'shift_sumcheck', 'column_claim_vectors'))
    scenarios = []
    for q in (8, 335, 445):
        leaves = siblings = Fraction(0)
        for stage in first:
            l, s = expected_counts(stage['leaf_count'], q)
            leaves += l * 4 * stage['leaf_words']
            siblings += s * 48
        scenarios.append(dict(queries=q, expected_initial_leaf_bytes=float(leaves),
            expected_initial_sibling_bytes=float(siblings),
            expected_initial_authentication_bytes=float(leaves + siblings),
            expected_retained_plus_initial_bytes=float(retained + leaves + siblings)))
    result = dict(status='PASS', exhaustive_small_shape_cases=checks,
        authenticated_branches=len(first),
        current_actual_initial_authentication_bytes=actual,
        current_non_pcs_retained_bytes=retained,
        current_column_claim_bytes=components['column_claim_vectors'],
        scenarios=scenarios,
        assumptions=[
            'Retain all original commitments, leaf layouts and independent root authentication.',
            'Each original tree receives q uniform independent projected queries.',
            'No independence between trees is needed for expected total size.',
            'Retained bytes assume unchanged AIR/shift/claim prefix; exclude new joint sumcheck, joint PCS, transport framing.',
            'Q8 is diagnostic; 335/445 are illustrative sensitivity cases, not validated security parameters.',
            'Expected sizes are not lower bounds; deterministic byte sizes require an actual transcript.'],
        conclusion='Joint later-stage openings alone leave original-root authentication and large column vectors; reducing these costs is a separate requirement.')
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
