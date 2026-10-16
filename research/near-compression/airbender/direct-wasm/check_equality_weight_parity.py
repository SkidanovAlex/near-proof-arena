"""Compare executable Lean equality weights with actual Python PCS weights.

Base-field embedded challenges include 0, 1, -1 and mixed coordinates. This
checks ordering/representation, not extension-field or cryptographic security.
"""
import argparse
import hashlib
import json
from pathlib import Path

from pq384_joint_opening import eq_weights
from pq384_primitives import P
from pq384_one_fold import ZERO
from check_whir_handoff import add, mul


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean-export', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    raw = args.lean_export.read_bytes()
    cases = json.loads(raw)
    entries = 0
    reversal_detected = 0
    for point, expected, residual, mle in cases:
        actual = eq_weights([(x, 0, 0, 0) for x in point])
        assert actual == [(x, 0, 0, 0) for x in expected]
        assert len(actual) == 2 ** len(point)
        dot = ZERO
        for i, weight in enumerate(actual):
            dot = add(dot, mul(weight, ((i*i + 19*i + 7) % P, 0, 0, 0)))
        assert dot == (residual, 0, 0, 0) == (mle, 0, 0, 0)
        entries += len(actual)
        if eq_weights([(x, 0, 0, 0) for x in reversed(point)]) != actual:
            reversal_detected += 1
    assert len(cases) == 55 and reversal_detected > 0
    report = {
        'status': 'PASS', 'cases': len(cases), 'weight_entries': entries,
        'reversed_coordinate_order_detected_cases': reversal_detected,
        'lean_export_sha256': hashlib.sha256(raw).hexdigest(),
        'scope': 'Actual Lean equalityWeights/scalarRSResidual/genericRowMLE vs actual Python eq_weights on base-field embedded challenges; not full extension arithmetic refinement or security certification',
    }
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
